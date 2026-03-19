#lang racket

(require racket/generic
         [for-syntax racket/list
                     racket/struct
                     racket/syntax
                     syntax/parse
                     syntax/id-table
                     racket/syntax-srcloc]
         [for-meta 2 racket/base
                   syntax/parse])

(provide
 (r:struct-out dp-set)
 dp-set/c

 dp-set/kc
 dp-setof/kc
 dp-setof-d/kc
 dp-subset-of-d/kc

 dp-set-with-size=/kc
 dp-set-size=-d/kc
 
 a-set
 set-∈
 set-∉
 set-∈-safe
 set-∉-safe
 set-∈-d/kc
 dp-list->hash
 dp-list->set
 dp-list-list->set
 set-ground-set
 dp-ground-set->list
 dp-set-members->list
 set-subset-of?
 set-equal?

 dp-set-shrink
 
 set
 subset-of
 the-set-of
 the-product-of
 element-of
 
 as-set
 set-∪
 set-∩
 dp-set-remove
 dp-set-filter
 set-minus
 set-size

 dp-null-set
 dp-symbolic-subset
 dp-set-from-sol

 dp-element-from-sol

 ;temp

 dp-symbolic-element-of

 dp-extract-singleton
)


;
; set operations
;

; check if set-a and set-b has the same elements
; set-a : dp-set/c
; set-b : dp-set/c
; -> boolean?
; NOTE: define here as gen:equal+hash needs to refer to
(define (set-equal? set-a set-b [recursive-equal? #f])
  ; intentional fallback to Racket
  (if (or (not (dp-set-S set-a)) (not (dp-set-S set-b)))
      (and (not (dp-set-S set-a)) (not (dp-set-S set-b)))
      (r:and
       (set-subset-of? set-a set-b)
       (set-subset-of? set-b set-a))))

;
; get the solved set from the rosette solution
; a-sol : r:solution? 
; the-sym-set : (), assumed to be consistent with the solution
; old version, only works on sets every hash value of which is a single (symbolic or concrete) constant
(define (dp-set-from-sol the-sym-set a-sol)
  (if (r:unsat? a-sol) dp-null-set
      (let* ([sym-set-hash (dp-set-S the-sym-set)]
            [complete-sol
             (r:complete-solution
              a-sol
              ; could have potential optimization
              (remove-duplicates
               (apply append (map r:symbolics (hash-values sym-set-hash)))))])
      (dp-set (for/hash ([v (hash-keys sym-set-hash)])
                (values v (r:evaluate
                           (hash-ref sym-set-hash v) complete-sol)))))))


; set type for static checking

; type object representing Set
(begin-for-syntax
  (provide
   tSetOf)

  ; underlying type object of SetOf
  (struct ty-Set (el-type) #:transparent ; set-∈ of nested set does not match
    #:property prop:type-interface (list (r:cons 'set r:identity))
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'SetOf)
        (λ (self) (list (ty-Set-el-type self)))))]
    )

  ; return #f if a-t is not a subtype of the type "a set of something"
  (define (as-ty-Set a-t)
    (and
     (interfaced-type? a-t)
     ; get a function always return #f when a-t does not have a interpretation
     ; as a set type
     ((cdr (or (assoc 'set (get-type-interface a-t))
               (cons '() (const #f))))
      a-t)))

  (define-match-expander tSetOf
    (syntax-parser
      ; if the type being matched has a interpretation as tSet
      [(_ ty-el) #'(app as-ty-Set (ty-Set ty-el))])
    ; used as the constructor for the type object outside ```match'''
    (syntax-parser
      [(_ el-type) #'(ty-Set el-type)]))
)


; set-like structure
; Note: dp-set? implies dp-set/c
;       contract for S is assumed as invariant except for using (dp-set #f) as null set
; (SOLVED) XXX: currently, two dp-set are equal? iff both the ground set and members are equal
;
; the set of keys is the ground set, keys mapped to #t are the actual members
;
; S : (hash/c any/c boolean?)

; fallback to use Racket struct avoid Rosette symbolic evaluation opening up the structure
; resulting fields of the structure becoming unions
; Note: defining ``gen:equal+hash'' seemed to prevent this
(struct dp-set (S)
          ; why ```prop:interface ('a)''' passes compilation
          #:property prop:interface
                    (r:list
                       (r:cons 'set r:identity); casting to set is identity
                       (r:cons 'symbolic?
                               (λ (the-set)
                                 (r-symbolic-atom?
                                  (hash-iterate-value
                                   (dp-set-S the-set)
                                   (hash-iterate-first (dp-set-S the-set))
                                   #f))))
                     ) 
          #:methods gen:custom-write
          [(define write-proc
            (r:λ (the-set port mode)
                 (if (dp-set-S the-set)
                     (if (list? (dp-set-members->list the-set))
                         (fprintf port "{~a}" (string-join (map
                                                            (λ (e) (format "~s" e))
                                                            (dp-set-members->list the-set)) ", "))
                         (begin
                           (print "dp-set:" port)
                           (print (dp-set-S the-set) port)))
                     (fprintf port "null (no solution)"))))]
          #:methods gen:equal+hash
          [(define equal-proc set-equal?)
           (define (hash-proc a-set recursive-equal-hash)
             (equal-hash-code (dp-set-S (dp-set-shrink a-set))))
           (define (hash2-proc a-set recursive-equal-hash)
             (equal-secondary-hash-code (dp-set-S (dp-set-shrink a-set))))]
          #:methods gen:dp-mergeable
                    ; S-ref is the representative set, which should have completed all keys
                    ; i.e. the union of all hash keys of the underlying hashes of the components
                    ; of the symbolic union
                    [(define (gen-merge-union U-sets S-ref)
                       (let ([H (dp-set-S S-ref)])
                         (dp-set (for/hash ([k (hash-keys H)])
                                   (values k (r:for/all ([Sx U-sets])
                                                        (hash-ref (dp-set-S Sx) k #f)))))))                     
                     (define (gen-representative-el-from-lst S-lst dummy-set)
                       (dp-set (for/hash
                                   ([k (apply append
                                              (map (λ (a-set) (hash-keys (dp-set-S a-set)))
                                                   S-lst))])
                                 (values k #t))))                     
                     (define gen-decode-merged-from-sol dp-set-from-sol)]
          #:transparent)

; null set
; used to represent no solution
(define dp-null-set (dp-set #f))

; contract for object that can be interpret as a set (set-like)
; an-object : any/c
; -> boolean?
(define (dp-set/c an-object)
  (not (not ; convert to boolean?
    (and
     (interfaced-struct? an-object)
     (assoc 'set (get-interface an-object))))))

(define-simple-contract/kc dp-set/kc (v)
  (and
   (interfaced-struct? v)
   (assoc 'set (get-interface v)))
  "expects a value interpretable as a set")

; contract combinator for set-like with members satisfying given contract, internal
; Note: flat version, membering element contracts are also flat
;       used to check only structure without value dependency
;       e.g. ``Are the members a set of integer?''
;       but not ``Are the members subset of another value?''
; el-ctc : (-> any/c boolean?), contract of the membering element
; -> (any/c -> boolean?)
(define (dp-setof/c el-ctc) ; curried shorthand
  (make-flat-contract
   #:name 'set-like
   #:late-neg-projection
   (λ (blame)
     (define el-proj ((contract-late-neg-projection el-ctc)
                      (blame-add-context blame (format "an element of" ))))
     (λ (an-object neg-party)
       (if (interfaced-struct? an-object)
           (let ([to-set (assoc 'set (get-interface an-object))])
             (if to-set
                 (let ([the-hash (dp-set-S ((cdr to-set) an-object))])
                   (map
                    (λ (e)
                      ; enforce [ e ∈ S => (el-ctc e) is #t ]
                      (if (hash-ref the-hash e)
                          (el-proj e neg-party) ; error triggered here if violation
                          e))
                    (hash-keys the-hash)) ; result discarded
                   an-object)
                 (raise-blame-error blame #:missing-party neg-party
                                    an-object '(expected "an object interpretable as a set" given: "~e") 
                                    an-object)))
           (raise-blame-error blame #:missing-party neg-party
                              an-object '(expected "an object interpretable as a set" given: "~e") 
                              an-object))
       ))))

(define (dp-setof/kc el-ctc)
  (and/kc
   dp-set/kc
   (kc-contract (v the-srcloc name context [predicate? #f])
    (let* ([the-set (as-set v)]
           [the-hash (dp-set-S the-set)]
           [success? (andmap
                       (λ (e)
                         ; enforce [ e ∈ S => (el-ctc e) is #t ]
                         (if (hash-ref the-hash e)
                             ; error triggered here if violation
                             (el-ctc e the-srcloc name         
                                     (cons "an element" context)
                                     predicate?) 
                             #t))
                       (hash-keys the-hash))])
      (if predicate? success? v)))))

; construct a contract factory for contract of set-like with members satisfying
; specific contracts, internal
; Note: value-dependent version, produce a factory accepting dependent values
;       The factory generates contracts that check members satisfying certain property
;       dependent on values feed to the factory. But the generated contract does not
;       check the value-dependent properties that set satisfies as a whole.
;       e.g., it can check ``Are the members subset of another value?''
;             (by passing another contract factory that accepts a super set S (another value)
;             and generate a contract taking a set T returns if T ⊂ S)
;             but not ``Is this set a family of subset of another value?''
; el-ctc-d : (-> any/c ... (-> any/c boolean?)), contract of the membering element
; -> (-> any/c ... (any/c -> boolean?))
(define ((dp-setof-d/c el-ctc-d) v . rest) ; curried shorthand
    ; produce contract of elements given dependent values
    (let ([el-ctc (apply el-ctc-d (cons v rest))])
      (make-flat-contract
       #:name 'set-like
       #:late-neg-projection
       (λ (blame)
         (define el-proj ((contract-late-neg-projection el-ctc)
                          (blame-add-context blame (format "an element of" ))))
         (λ (an-object neg-party)
           (if (interfaced-struct? an-object)
               (let ([to-set (assoc 'set (get-interface an-object))])
                 (if to-set
                     (let ([the-hash (dp-set-S ((cdr to-set) an-object))])
                       (map
                        (λ (e)
                          ; enforce [ e ∈ S => (el-ctc e) is #t ]
                          (if (hash-ref the-hash e)
                              (el-proj e neg-party) ; error triggered here if violation
                              e))
                        (hash-keys the-hash)) ; result discarded
                       an-object)
                     (raise-blame-error blame #:missing-party neg-party
                                  an-object '(expected "an object interpretable as a set" given: "~e") 
                                  an-object)))
               (raise-blame-error blame #:missing-party neg-party
                                  an-object '(expected "an object interpretable as a set" given: "~e") 
                                  an-object))
           )))
      ))

; convention: the contract generated does not need to check the non-dependent shape
(define ((dp-setof-d/kc el-ctcs-d) v . rest) ; curried shorthand
  ; produce contract of elements given dependent values
  (let ([el-ctcs (apply el-ctcs-d (cons v rest))])
    (and/kc
     dp-set/kc
     (kc-contract (v the-srcloc name context [predicate? #f])
      (let* ([the-set (as-set v)]
             [the-hash (dp-set-S the-set)]
             [success? (andmap
                        (λ (e)
                          ; enforce [ e ∈ S => (el-ctc e) is #t ]
                          (if (hash-ref the-hash e)
                              ; error triggered here if violation
                              (el-ctcs e the-srcloc name         
                                      (cons "an element" context)
                                      predicate?) 
                              e))
                        (hash-keys the-hash))])
        (if predicate? success? v))))
    ))

; return a contract checking the set size of a set being exactly n
(define (dp-set-size=/c n)
  (make-flat-contract
   #:name 'set-size
   #:late-neg-projection
   (λ (blame)
     (λ (a-set neg-party)
       ; alternatively: use dp-equal? to wrap raw int if present
       (if (equal? (dp-int-unwrap (set-size a-set))
                   (dp-int-unwrap n))
           a-set
           (raise-blame-error blame #:missing-party neg-party
                              a-set '(expected "a set of size ~e" given: "~e")
                              n
                              a-set))))))

; Note: the contract produced assuming the object being checked is a set
(define (dp-set-size=-d/kc n)
  (kc-contract (v the-srcloc name context [predicate? #f])
      (if (equal? (dp-int-unwrap (set-size v))
                  (dp-int-unwrap n))
          v
          (contract-fail/kc the-srcloc name
                            (format "expects a set of size ~e" (dp-int-unwrap n))
                            context v predicate?))))

; returns a contract checking if an object is a set with size exactly n
(define (dp-set-with-size=/kc n)
  (and/kc dp-set/kc (dp-set-size=-d/kc n)))

; convert set-like to set, raise error otherwise
; an-object : any/c
; -> dp-set?
(define (as-set an-object)
  ((r:cdr (r:assoc 'set (get-interface an-object))) an-object))

; covert the ground set of a set-like to Racket list, internal
; a-set : dp-set/c
; -> list?
(define (dp-ground-set->list a-set)
  (let ([S (dp-set-S (as-set a-set))])
    (if S
        (hash-keys S)
        '())))

; create a new set with elements
; Note: does not wrap int
; elements : list?
; -> dp-set?
(define (a-set . elements)
  (dp-set (make-immutable-hash
           (r:map
            (r:λ (e)
                 (r:cons
                  (if (dp-symbolic? e)
                      (raise "can not add an element whose value is to be solved to the set")
                      e) #t))
            elements))))


; check if a-element is a member of a-set
; a-element : any/c
; a-set : dp-set/c

(provide set-∈-typed-rewriter
         set-∉-typed-rewriter)
(define-syntax set-∈-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ ('CON τb) (_ (tSetOf τb)))
       (λ (stx) (cons stx (tBool)))]
      [(args-τ ('SYM τb) (_ (tSetOf τb)))
       (syntax-parser
         [(set-∈ arg-el arg-S)
          (cons #'(set-∈-safe arg-el arg-S) (tBool))])]
      [(args-τ (_ τb0) (_ (tSetOf τb1)))
       (syntax-parser
         [(set-∈ arg-el arg-S) (raise-syntax-error #f "element type does not match the set"
                                                   #'(set-∈ arg-el arg-S)
                                                   #'arg-el)])]
      [(args-τ (_ _) (_ _))
       (syntax-parser
         [(set-∈ arg0 arg1) (raise-syntax-error #f "expects a set"
                                                   #'(set-∈ arg0 arg1)
                                                   #'arg1)])]
      [_ (λ (stx) (raise-syntax-error #f "expect 2 arguments" stx))])))

(define-syntax set-∉-typed-rewriter
  (λ (type-lst)
    (match type-lst
      [(args-τ ('CON τb) (_ (tSetOf τb)))
       (λ (stx) (cons stx (tBool)))]
      [(args-τ ('SYM τb) (_ (tSetOf τb)))
       (syntax-parser
         [(set-∉ arg-el arg-S)
          (cons #'(set-∉-safe arg-el arg-S) (tBool))])]
      [(args-τ (_ τb0) (_ (tSetOf τb1)))
       (syntax-parser
         [(set-∉ arg-el arg-S) (raise-syntax-error #f "element type does not match the set"
                                                   #'(set-∉ arg-el arg-S)
                                                   #'arg-el)])]
      [(args-τ (_ _) (_ _))
       (syntax-parser
         [(set-∉ arg0 arg1) (raise-syntax-error #f "expects a set"
                                                   #'(set-∉ arg0 arg1)
                                                   #'arg1)])]
      [_ (λ (stx) (raise-syntax-error #f "expect 2 arguments" stx))])))

(define/contract/kc (set-∈ a-element a-set)
  (->k ([x any/kc] [y dp-set/kc]) any/kc)
  (hash-ref (dp-set-S (as-set a-set)) (dp-wrap-if-raw-int a-element) #f))
(define/contract/kc (set-∉ a-element a-set)
  (->k ([x any/kc] [y dp-set/kc]) any/kc)
  (r:not (set-∈ a-element a-set)))

(define (set-∈-d/kc the-set)
  (make-simple-contract/kc (v)
    (set-∈ v the-set)
    (format "expects an element of ~v" the-set)))

; safe versions
(define (set-∈-safe a-element a-set)
  (∃ [v ∈ (as-set a-set)]
     (dp-equal? a-element v)))
(define (set-∉-safe a-element a-set)
  (∀ [v ∈ (as-set a-set)]
     (r:not
      (dp-equal? a-element v))))

; convert Racket list to a hash with each key maps to #t, internal
; -> (hash/c any/c boolean? ....)
(define (dp-list->hash a-lst)
  (make-immutable-hash
   (r:map
    (r:λ (e) (r:cons e #t))
    a-lst)))

; convert Racket list to a set, internal
; a-lst : list?
; -> dp-set?
(define (dp-list->set a-lst)
  (dp-set (dp-list->hash
           a-lst)))

; build a set with members mbr-lst and potential members pmbr-lst,
; internal, non-solvable
; Note: resulting ground set will be mbr-lst union pmbr-lst
; mbr-lst : list?
; pmbr-lst : list?
; -> dp-set?
(define (dp-list-list->set mbr-lst pmbr-lst)
  (dp-set (make-immutable-hash
           (map
            (λ (e) (cons e (if (member e mbr-lst) #t #f)))
            (append mbr-lst pmbr-lst)))))

; get the ground set of a set-like
; a-set : dp-set/c
; -> dp-set?
(define (set-ground-set a-set)
  (dp-set (make-immutable-hash
           (r:map
            (r:λ (e) (r:cons e #t))
            (hash-keys
             (dp-set-S (as-set a-set)))))))

; get rid of nonmember ground set elements of a set-like, internal,
; non-solvable(!) (r:filter may generate symbolic hash,
;                    not work with hash-ref (?) )
; a-set : dp-set/c
; -> dp-set?
(define (dp-set-shrink a-set)
  (let ([the-set-hash (dp-set-S (as-set a-set))])
    (dp-set (for/hash ([e (hash-keys the-set-hash)]
                       #:when (hash-ref the-set-hash e))
              (values e #t)))))

; get the set members of a set-like as Racket list, internal
; non-solvable(!) (r:filter may generate symbolic hash,
;                    not work with hash-ref (?) )
; a-set : dp-set/c
; -> list?
(define (dp-set-members->list a-set)
  (r:let ([the-set-hash (dp-set-S (as-set a-set))])
    (r:filter (r:λ (e) (hash-ref the-set-hash e #f))
              (hash-keys the-set-hash))))

; check if set-a is a subset of set-b
; set-a : dp-set/c
; set-b : dp-set/c
; -> boolean?
(define/contract/kc (set-subset-of? set-a set-b)
  (->k ([x dp-set/kc] [y dp-set/kc]) any/kc)
  (r:let ([the-set-hash-a (dp-set-S (as-set set-a))]
          [the-set-hash-b (dp-set-S (as-set set-b))])
         (r:andmap (r:λ (e)
                        (r:implies
                         (hash-ref the-set-hash-a e #f)
                         (hash-ref the-set-hash-b e #f)))
                   (hash-keys the-set-hash-a))))
(kv-func-type-annotate set-subset-of? ((tSetOf τb) (tSetOf τb) (tBool))
                       "two sets of the same element type")

; Note: 1) assuming the value dependent on is always correct, i.e. the-superset is a set
;       2) assuming the value being checked has the correct shape, i.e. v is a set
(define (dp-subset-of-d/kc the-superset)
  (make-simple-contract/kc (v)
    (set-subset-of? v the-superset)
    (format "expects a subset of ~v" the-superset)))

; XXX: maybe nonsolvable(?) because of the presence of remove-duplicates
; union set of the set-likes
; the ground set of the union is the union of ground sets
; a-p-set ... : dp-set/c ...
; -> dp-set?
(define-syntax (set-∪ stx)
  (syntax-parse stx
    [(_ a-set-like ...)
     #:with (the-set ...)
     (let ([l (stx->list #'(a-set-like ...))])
       (for/list ([i (range 1 (+ (length l) 1))]
                  [v l])
         #`(contracted-v/kc
            dp-set/kc #,v #,(syntax-srcloc v) 'set-∪
            (list (format "the ~v~s argument of set-∪" #,i
                          '#,(ordinal-numeral i)
                          #;(cond [(equal? i 1) 'st]
                                  [(equal? i 2) 'nd]
                                  [(equal? i 3) 'rd]
                                  [else 'th]))))))
     #;(generate-temporaries #'(a-set-like ...))
     #:with (a-set ...) (generate-temporaries #'(a-set-like ...))
     #:with (a-gnd-set ...) ; ground sets represented as lists of hash-keys
     (r:map
      (r:λ (s)
           #`(hash-keys (dp-set-S #,s)))           
      (syntax->list #'(a-set ...)))
     #'(r:let ([a-set (as-set the-set)] ...) ; caching casting to set
        (dp-set
         (make-immutable-hash
          (r:map
           (r:λ (e)
               (r:cons
                e
                (r:ormap
                 (r:λ (s) ; set-like
                      (hash-ref (dp-set-S s) e #f))
                 (r:list a-set ...))))
           (r:remove-duplicates (r:append a-gnd-set ...))))))])) ; maybe don't remove duplicate here?
(kv-func-type-annotate set-∪ ((tSetOf τb) (tSetOf τb) (tSetOf τb))
                       "two sets of the same element-type")


; intersection set of the set-likes
; the ground set of the intersection is the of ground set of the first set
; Note: since we don't have the universe set (identity element for intersection),
;       set-∩ must be supplied with at least 1 element
; a-p-set ...+ : dp-set/c ...
; -> dp-set?
(define-syntax (set-∩ stx)
  (syntax-parse stx
    [(_ a-set-like0 a-set-like1 ...)
     #:with (s1 ...) (generate-temporaries #'(a-set-like1 ...))
     #:with (the-set0 the-set1 ...)
     (let ([l (stx->list #'(a-set-like0 a-set-like1 ...))])
       (for/list ([i (range 1 (+ (length l) 1))]
                  [v l])
         #`(contracted-v/kc
            dp-set/kc #,v #,(syntax-srcloc v) 'set-∪
            (list (format "the ~v~s argument of set-∪" #,i
                          '#,(ordinal-numeral i)
                          #;(cond [(equal? i 1) 'st]
                                   [(equal? i 2) 'nd]
                                   [(equal? i 3) 'rd]
                                   [else 'th]))))))
     #`(let ([s0 (as-set the-set0)]
             [s1 (as-set the-set1)] ...)
         (dp-set
          (make-immutable-hash 
           (r:map
            (r:λ (k)
                 (cons
                  k
                  (r:and (hash-ref (dp-set-S s0) k #f)
                         (hash-ref (dp-set-S s1) k #f) ...)))
            (hash-keys (dp-set-S s0))))))]))
(kv-func-type-annotate set-∩ ((tSetOf τb) (tSetOf τb) (tSetOf τb))
                       "two sets of the same element-type")

; remove an element from a set
; non-sets are converted to sets,
; nothing observable happens if the element is not in the set
; Note: may strips the chaperone if a-set is chaperoned
;       non-solvable(?) if the element is symbolic,
;       i.e., if the value depends on other symbolic value
;       so make it internal at least now
; a-set : dp-set/c
; -> dp-set?
(define (dp-set-remove a-set e)
  (dp-set (hash-set (dp-set-S (as-set a-set)) e #f)))

; select the subset of a set satisifying pred
; internal, see below
; Note: All e in the ground set will be fed to pred.
;       There will be a problem if anything in the
;       ground set that is not compatible with pred.
; pred : (-> any/c boolean?)
; a-set : dp-set/c
; -> dp-set?
(define (dp-set-filter pred a-set)
  (let ([the-set-hash (dp-set-S (as-set a-set))])
   (dp-set
    (make-immutable-hash
     (r:map
      (r:λ (e)
           (r:cons e
                   (r:if (hash-ref the-set-hash e #f)
                         (pred e)
                         #f)))
      (hash-keys the-set-hash))))))

; the set diffence of two set-like
; set-a : dp-set/c
; set-b : dp-set/c
; -> dp-set?
(define/contract/kc (set-minus set-a set-b)
  (->k ([x dp-set/kc] [y dp-set/kc]) dp-set/kc)
  (dp-set
   (make-immutable-hash
    (r:let ([the-set-hash-a (dp-set-S (as-set set-a))]
            [the-set-hash-b (dp-set-S (as-set set-b))])
           (r:map
            (r:λ (x)
                 (r:cons
                  x
                  (r:and
                   (hash-ref the-set-hash-a x #f)
                   (r:not (hash-ref the-set-hash-b x #f)))))
            (hash-keys the-set-hash-a))))))
(kv-func-type-annotate set-minus ((tSetOf τb) (tSetOf τb) (tSetOf τb))
                       "two sets of the same element type")

; calculate the number of members in the set
; a-set : dp-set/c
(define/contract/kc (set-size a-set)
  (->k ([x dp-set/kc]) any/kc)
  (r:let ([the-set-hash (dp-set-S (as-set a-set))])
    (dp-integer
     (r:count
      (r:λ (v) (hash-ref the-set-hash v #f))
      (hash-keys the-set-hash))
     ; XXX: unforunately for now we can not tell if the set is constant or not
     ;      assign the size to ;poly for safety
     'poly)))

(kv-func-type-annotate set-size ((tSetOf τb) (tInt))
                       "a set")

(kv-func-type-annotate different? (τb τb (tBool))
                       "two objects of the same type")
(kv-func-type-annotate equal? (τb τb (tBool))
                       "two objects of the same type")


; create a solvable symbolic subset of ground-set, internal, non-solvable(?)
; ground-set : dp-set/c
; -> (dp-setof/c symbolic?)
(define (dp-symbolic-subset ground-set [size #f])
  (values
   (let ([members (dp-set-members->list ground-set)])
    (dp-set (for/hash ([e members])
              (values e (fresh-symbolic-bool)))))
   (if size
       (without-protection/kc
        (r:list (r:λ (a-set)
                     (dp-equal? (set-size a-set) size))))
       '())))


