# deleted-code

<details>
<summary>Root .rkt files</summary>

<summary>reduction-base.rkt</summary>

```racket
; TODO: fix the following issue:
; for [j ∈ (ints-from-to 0 i)] for [(v #:index i) ∈ Vars])
#;(define-syntax define/sets
  (syntax-parser
    [(_ (set-id0:id ...) ({el-expr0 (~seq , el-expr1) ...} ...) (~seq (~datum for) xn-in-Xn:element-of-a-set) ...+
        (~optional (~seq (~datum if) pred-expr)))
     #:with (elem-with-index0 ...) (generate-temporaries #'(xn-in-Xn ...))
     #:fail-unless (equal? (length (syntax->list #'(set-id0 ...)))
                           (length (syntax->list #'(el-expr0 ...))))
     "number of representative elements does not match the number of sets"
     #`(define-values (set-id0 ...)
         (let ([elem-with-index0 (dp-set-element-index xn-in-Xn.X)] ...)
           (for*/lists (set-id0 ... #:result (values (dp-list->set (apply append set-id0)) ...))
                       ((~@
                         [xn-in-Xn.x (hash-keys elem-with-index0)]
                         ; NOTE: ``xn-in-Xn.indx'' returns an uninterned ``i'' when ``ind'' undefined
                         [xn-in-Xn.indx (list (hash-ref elem-with-index0 xn-in-Xn.x))])
                         ...
                        #:when #,(if (attribute pred-expr) #'pred-expr #'#t))
             (values (list el-expr0 el-expr1 ...) ...))))]))
```

```racket
#;(define-syntax for/set
  (syntax-parser
    [(_ (~optional (~seq #:element-type el-type)) [x-expr (~datum for) x-in-X:element-of-a-set
                (~optional (~seq (~datum if) pred-x))])
     #`(dp-list->set
        (map
         (λ (x-in-X.x)
           (let* ([x-res #,(if (attribute el-type) #'(el-type x-expr) #'x-expr)]
                  [x-res-type (match-let-values ([(x-res-type _) (struct-info x-res)]) x-res-type)])
             (displayln x-res)
             (if x-res-type
                 (chaperone-struct x-res
                                   x-res-type
                                   prop:corr x-in-X.x)
                 x-res)))
         #,(if (attribute pred-x)
             #'(filter (λ (x-in-X.x) pred-x) (dp-set-members->list x-in-X.X))
             #'(dp-set-members->list x-in-X.X))))]
    [(_ (~optional (~seq #:element-type el-type)) [x-y-expr (~datum for) x-in-X:element-of-a-set (~datum for) y-in-Y:element-of-a-set
                  (~optional (~seq (~datum if) pred-x-y))])
     #`(dp-list->set
        (apply
         append ; flatten once
         (map
          (λ (y-in-Y.x)
            (map
             (λ (x-in-X.x)
               (let* ([x-y-res #,(if (attribute el-type) #'(el-type x-y-expr) #'x-y-expr)]
                      [x-y-res-type (match-let-values ([(x-y-res-type _) (struct-info x-y-res)]) x-y-res-type)])
                 (if x-y-res-type
                     (chaperone-struct x-y-res
                                   x-y-res-type
                                   prop:corr x-in-X.x)
                     x-y-res)))
             #,(if (attribute pred-x-y)
                   #'(filter (λ (x-in-X.x) pred-x-y) (dp-set-members->list x-in-X.X))
                   #'(dp-set-members->list x-in-X.X))))
          (dp-set-members->list y-in-Y.X))))]
    #;[(_ [xs-expr (~datum for) [(x:id ...) (~or in ∈) X:expr]
                 (~optional (~seq (~datum if) pred-x))])
     #''()]))
```

```racket
(provide find-all)

; Begin -- old version
#;(define-syntax foreach/set  
  (syntax-parser
    #:datum-literals (in)
    [(_ ([x in X] ...) body)
     #'(make-immutable-hash
        (map
         (λ (e) (cons e #t))
         (filter
          identity
          (apply append ; flatten once
              (for/list ([x X] ...)
                body)))))
     ]))

#;(define-syntax find-one
  (syntax-parser
    #:datum-literals (in as s.t.)
    [(_ [x:id in X] (~optional (~seq as as-body)) s.t. pred?)
     (if (attribute as-body)
         ; return singleton list
         #'(list (r:let ([the-one (r:findf (r:λ (x) pred?) X)])
                  (r:if the-one
                        (r:λ (x) as-body)
                        the-one)) )
         #'(list (r:findf (r:λ (x) pred?) X)))]))

; not in use, use for/set instead
(define-syntax find-all
  (syntax-parser
    #:datum-literals (in as s.t.)
    [(_ [x:id in X] (~optional (~seq as as-body)) s.t. pred?)
     #:with filtered #'(r:filter (r:λ (x) pred?) X)
     ; FIXME: not unified with find-one
     (if (attribute as-body)
         #'(make-immutable-hash
            (map
             (λ (e) (cons e #t))

             (r:let ([alls filtered])
                  (r:map
                   (r:λ (x) as-body)
                   alls))
         
         ))
         #'(make-immutable-hash
            (map
             (λ (e) (cons e #t))

             filtered

             ))
         )]
    [(_ [(x:id ...) in X] (~optional (~seq as as-body)) s.t. pred?)
     #:with filtered #'(r:filter
                        (r:λ
                         (a-lst)
                         (match-let ([(list x ...) a-lst])
                           pred?))
                        X)
     (if (attribute as-body)
         #'(make-immutable-hash
        (map
         (λ (e) (cons e #t))

         (r:let ([alls
                    filtered])
                  (r:map
                   (r:λ (a-lst)
                        (match-let ([(list x ...) a-lst])
                          as-body))
                   alls))
         
         ))
         #'(make-immutable-hash
            (map
             (λ (e) (cons e #t))

             filtered

             ))
         )]))

#;(define (all-pairs-in X)
  (cond [(hash? X) (combinations
                    (filter (λ (x)
                              (hash-ref X x))
                            (hash-keys X)) 2)]
        [(list? X) (combinations X 2)]))

```

</details>
</details>

<details>
<summary>lib/</summary>

<details>
<summary>cnf.rkt</summary>

- cnf.rkt
```racket
;(r:struct neg (x) #:transparent)

#;(define clause/c
    (listof literal/c))

#;(define cnf/c (listof clause/c))

#;(define (underlying-var a-literal)
  (cond [(var/c a-literal) a-literal]
        [else (neg-x a-literal)]))

#;(define (n-true-literals a-clause assignment)
  (r:count
   r:identity
   (r:map
    (r:λ (l) (true-literal? l assignment))
    (clause-lst a-clause))))

#;(define (n-true-literals assignment a-clause)
  (r:count
   r:identity
   (r:map
    (r:λ (l)
         (r:if (var/c l)
              (r:hash-ref assignment l)
              (r:not (r:hash-ref assignment (neg-x l)))))
    a-clause)))

#;(define (literals-of a-sth)
  (cond [(clause/c a-sth) (clause-lst a-sth)]
        [(cnf/c a-sth) (r:flatten a-sth)]))

#;(define (vars-of a-sth)
  (r:cond [(clause/c a-sth)
         (r:remove-duplicates
          (r:map underlying-var (clause-lst a-sth)))]
        [(cnf/c a-sth)
         (r:remove-duplicates (r:flatten (r:map vars-of a-sth)))])
  )

(begin-for-syntax
    ...
  ; Question: why this does not work
  #;(define-syntax-class lit
    #:datum-literals (¬)
    (pattern (~or* ((~seq (~and ¬ neg)) x) (x))))
  #;(define (parse-clause stx i)
    (syntax-parse stx
      #:datum-literals (∨)
      [(literal0:lit (~seq ∨ literal1:lit) ...)
       #`(clause (list (literal literal0.x #,(if (attribute literal0.neg) #t #f) #,i)
                       (literal literal1.x #,(if (attribute literal1.neg) #t #f) #,i)
                       ...))]))
  ...
  )


#;(define (generate-sat-instance
                  n-clauses n-vars
                  #:exact-n? [e-n? #f])
  ; not very meaningful to have no contract here
  ;(-> integer? integer? sat-instance/c)
  
  (define (generate-clause n-vars i-clause)

    (define (draw-3-var n-vars)
        (map (λ (x) (string->symbol
                   (string-append "x" (number->string x))))
             (random-sample
              (stream->list (in-range 1 (+ n-vars 1)))
              3
              #:replacement? #f)))

    (define (generate-literal-from-var var i-clause)
      (literal var (random-ref '(#t #f)) i-clause))

    (clause (map generate-literal-from-var (draw-3-var n-vars) (make-list 3 i-clause))))
 
  (define (generate-sat-instance-aux i n-vars res-sat-instance)
       (cond [(eq? i n-clauses) res-sat-instance]
             [else (let* ([a-clause (generate-clause n-vars i)]
                          [repeated?
                           (member a-clause res-sat-instance
                                   (λ (x y) (andmap literal-equal? x y)))]
                          [draw-another? (and e-n? repeated?)])
                    (generate-sat-instance-aux
                    (if draw-another? i (+ i 1))
                    n-vars
                    (if repeated?
                        res-sat-instance
                        (cons
                          a-clause
                          res-sat-instance))))]))
  
  (generate-sat-instance-aux 0 n-vars '()))


#;(define (generate-sat-instance
                  n-clauses n-vars
                  #:exact-n? [e-n? #f])
  ; not very meaningful to have no contract here
  ;(-> integer? integer? sat-instance/c)
  
  (define (generate-clause n-vars)

    (define (draw-3-var n-vars)
        (map (λ (x) (string->symbol
                   (string-append "x" (number->string x))))
             (random-sample
              (stream->list (in-range 1 (+ n-vars 1)))
              3
              #:replacement? #f)))

    (define (generate-literal-from-var var)
        (if (random-ref '(#t #f))
            var
            (neg var)))

    (map generate-literal-from-var (draw-3-var n-vars)))
 
  (define (generate-sat-instance-aux i n-vars res-sat-instance)
       (cond [(eq? i n-clauses) res-sat-instance]
             [else (let* ([a-clause (generate-clause n-vars)]
                          [repeated? (member a-clause res-sat-instance)]
                          [draw-another? (and e-n? repeated?)])
                    (generate-sat-instance-aux
                    (if draw-another? i (+ i 1))
                    n-vars
                    (if repeated?
                        res-sat-instance
                        (cons
                          a-clause
                          res-sat-instance))))]))
  
  (generate-sat-instance-aux 0 n-vars '()))


```

</details>
<details>
<summary>graph.rkt</summary>

```racket
#;(define dp-graph/c
  (and/c
   (struct/c dp-graph
             (hash/c
              any/c
              (hash/c any/c any/c #:immutable #t #:flat? #t)
              #:immutable #t #:flat? #t)
             dp-set/c
             boolean?)
   dp-graph-V-M?))

```

```racket
#;(define dp-graph-u/c
  (and/c
   dp-graph/c
   dp-graph-u-invariant?
   (λ (g) (not (dp-graph-directed? g)))))

#;(define dp-graph-d/c
  (and/c
   dp-graph/c
   (λ (g) (dp-graph-directed? g))))

#;(define-syntax (make-edge stx)
  (syntax-parse stx
    [(_ p ) #'(edge-u p)]
    [(_ u v) #'(edge-u (r:cons u v))]))

;(define edge-u/c (struct/c edge-u (cons/c vertex/c vertex/c)))
#;(define edge-u/c (and/c
                  (dp-setof/c vertex/c)
                  (λ (e) (<= (set-size e) 2))))

;(define edge/c (cons/c vertex/c vertex/c))

; old version
; does not match boolean?
#;(define (has-edge? x y g)
    (r:if
     (r:and
      (r:member y (hash-ref g x '()))
      ; was undirected
      #;(r:member x (hash-ref g y '())))
     #t
     #f))

; not going to work because of symbolic hash
; (r:if
;     (set-∈ e S)
;     (hash-1)
;     (hash-2))
; will resulting symbolic hash
#;(define (remove-edges g es)
  (r:let*
   ([directed (dp-graph-directed? g)]
    [edge-e (r:if directed edge-d-e edge-u-e)])
   (dp-graph
    (r:foldl
     (r:λ (e adj-M)
          (r:if
           (set-∈ e es)
           (hash-set adj-M
                     (e-u e)
                     (hash-set
                      (hash-ref adj-M (e-u e))
                      (e-v e)
                      #f))
           adj-M))
     #;(r:λ (e adj-M)
          (r:if (set-∈ e es)
                (r:let
                 ([u (r:car (edge-e e))]
                  [v (r:cdr (edge-e e))])
                 (r:if directed
                       (hash-set adj-M u (hash-set (hash-ref adj-M u) v #f))
                       (hash-set
                        (hash-set adj-M u (hash-set (hash-ref adj-M u) v #f))
                        v
                        (hash-set (hash-ref adj-M v) u #f))))
                adj-M))
     (dp-graph-M g)
     (dp-ground-set->list es))
    (dp-graph-V g)
    directed)))

```

```racket
; only works for undirected
; not in use any more as undirected edge is now set
#;(r:define (edge-equal-u? edge1 edge2 recursive-equal?)
          (r:let ([u1 (r:car (edge-u-e edge1))]
                  [v1 (r:cdr (edge-u-e edge1))]
                  [u2 (r:car (edge-u-e edge2))]
                  [v2 (r:cdr (edge-u-e edge2))])
                 (r:or (r:and
                        (recursive-equal? u1 u2)
                        (recursive-equal? v1 v2))
                       (r:and
                        (recursive-equal? u1 v2)
                        (recursive-equal? u2 v1)))))
; not in use any more as undirected edge is now set
#;(r:define (edge-hash edge recursive-equal-hash)
          (r:let ([h1 (recursive-equal-hash (edge-u-e edge))]
                  [h2 (recursive-equal-hash (r:cons (r:cdr (edge-u-e edge))
                                                    (r:car (edge-u-e edge))))])
                 (r:if (r:< h1 h2) h1 h2)))

;
; Edges of undirected graphs are now sets of size 2
; Edges of directed graphs are now tuples of length 2
;

#;(r:struct edge-u (e) #:transparent
          #:methods gen:equal+hash [(r:define equal-proc edge-equal-u?)
                                    (r:define hash-proc edge-hash)
                                    (r:define hash2-proc edge-hash)]
          #:methods gen:custom-write
          [(define write-proc
             (λ (the-e port mode)
               (fprintf port "(~a -- ~a)"
                        (car (edge-u-e the-e))
                        (cdr (edge-u-e the-e)))))])

#;(r:struct edge-d (e) #:transparent)

#;(define (-e- u v)
  (edge-u (r:cons u v)))

#;(define (-e-> u v)
  (edge-d (r:cons u v)))

#;(define (incident? e v)
    (r:or (r:equal? (r:car e) v)
          (r:equal? (r:cdr e) v)))

#;(define (endpoints e)
    (a-set (r:car e) (r:cdr e)))

; how to unify the contract of directed graph and the contract of undirected
; define a function with a parameter specifying directness that returns respectively
#;(define (graph/c #:undirected? [undirected? #f])
    (let ([graph-aux/c
           (hash/c vertex/c (listof vertex/c) #:immutable #t #:flat? #t)])
      (if undirected?
          (and/c
           graph-aux/c
           (λ (g)
             (for/and ([(key values) (in-hash g)])
               (for/and ([v values])
                 (has-edge? key v g)))))
          graph-aux/c)))

; original definition
#;(define graph/c
    (and/c
     (hash/c vertex/c (listof vertex/c) #:immutable #t #:flat? #t)
     ; was undirected
     #;(λ (g)
         (for/and ([(key values) (in-hash g)])
           (for/and ([v values])
             (edge? key v g))))))
```

```racket
;; get edge as pair from graph/c
;; assume directed
#;(define (get-edges g)
    (r:map
     (r:hash-keys g)))

; old version, may not be solvable(?)
#;(define (get-edges g)
    (for*/fold ([edges (hash)]
                #:result (dp-set edges))
               ([l (in-list (hash->list g))]
                [t (in-list (if (list? (cdr l))
                                (cdr l)
                                (list (cdr l))))])
      (cond
        [(hash-ref edges (cons t (car l)) #f)
         (values edges)]
        [else (values (hash-set edges (cons (car l) t) #t))])))
```

```racket
; XXX: how to keep the invariant that undirected edge can not
;      be inserted to directed graph or vice-versa
;      does not ensure the invariant that the endpoints in E are subset of V
;      no error info when some e with endpoints not in V are inserted
;      need a contract to check this
; unsolvable
; V : (dp-set/c any/c) set of vertices
; E : (dp-set/c edge/c)
#;(define (create-graph V E #:directed? [directed? #f])
  ; XXX: turn this defensive programming into contract
  (when (not
         (andmap
          (λ (e)
            (set-subset-of? (endpoints e) V))
          (dp-set-members->list E)))
    (error "create-graph: some edge contain an endpoint that does not belong to the set of vertices"))
  
  (dp-graph
   (let loop
     ([M (for/hash ([u (dp-set-members->list V)])
           (values u (make-immutable-hash)))]
      [Es (dp-set-members->list E)])
     (if (empty? Es)
         M
         (let* ([u (e-u (car Es))]
                [v (e-v (car Es))])
           (loop (hash-set
                  (if directed?
                      M
                      (hash-set M v (hash-set (hash-ref M v) u #t)))
                  u (hash-set (hash-ref M u) v #t)) (cdr Es)))))
   V
   directed?))
```

```racket
#;(define (create-graph-from-edges E #:directed? [directed? #f])
  (create-graph (dp-list->set
                 (apply append
                        (map
                         (λ (e)
                           (dp-set-members->list (endpoints e)))
                         (dp-set-members->list E)))) E #:directed? directed?))
```

```racket
#;(define (dp-r-test sym-g possible-start-vs v-order)
  (r:let*
   ([g-V-hash (dp-set-S (dp-graph-V sym-g))]
    [g-M-hash (dp-graph-M sym-g)])
   (r:and
    ; exact 1 of the vertices selected is starting vertex with order index 0
    (r:=
     (r:count
      (r:λ (v)
           (r:and
            (hash-ref g-V-hash v) ; should not need the default #f
            (r:= (hash-ref v-order v) 0))) 
      possible-start-vs)
     1)
    #;(r:=
     (r:count
      (r:λ (v)
           (r:and
            (hash-ref g-V-hash v) ; should not need the default #f
            (r:= (hash-ref v-order v) 0))) 
      (hash-keys g-V-hash))
     1)
    (r:andmap
     (r:λ (v)
          (r:implies
           (r:and
            (hash-ref g-V-hash v)
            (r:not (r:member v possible-start-vs)))
           (r:> (hash-ref v-order v) 0)))
     (hash-keys g-V-hash))
    (dp-r-path-constraint g-V-hash g-M-hash v-order)
    )))
```

```racket
; FIXME: remove this later
(define (dp-r-st-test sym-g s t v-order)
  (r:let*
   ([g-V-hash (dp-set-S (dp-graph-V sym-g))]
    [g-M-hash (dp-graph-M sym-g)])
   (r:and
    ; s must be selected in the subgraph
    (hash-ref g-V-hash s)
    ; t must be selected in the subgraph
    (hash-ref g-V-hash t)
    ; 
    (r:= (hash-ref v-order s) 0)
    ; no other selected vertices can be used as the starting point
    (r:andmap
     (r:λ (v)
          (r:implies
           (r:and
            (hash-ref g-V-hash v)
            (r:not (equal? v s))) ; intentionally fallback to racket
           (r:> (hash-ref v-order v) 0)))
     (hash-keys g-V-hash))
    (dp-r-path-constraint g-V-hash g-M-hash v-order)
    )
   ))

```

```racket
#;(define (st-path? g s t)
  (let ([g-V-hash (dp-set-S (dp-graph-V g))])
    (r:and
     ; XXX: this does not work in both verifier and solver environment
     ;(reachable? g s t)
     (dp-r-st-reachable g s t)
     (r:andmap
      (r:λ (v)
           (r:implies
            (hash-ref g-V-hash v)
            (r:and (r:<= (in-degree g v)
                         (if (dp-graph-directed? g) 1 2))
                   (r:<= (out-degree g v)
                         (if (dp-graph-directed? g) 1 2))))
           ;(r:<= (set-size (set-∪ (out-neighbors g v) (in-neighbors g v))) 2)
           )
      (hash-keys g-V-hash))
     (r:= (in-degree g s) (if (dp-graph-directed? g) 0 1))
     (r:= (out-degree g s) 1)  
     ;(r:= (set-size (set-∪ (out-neighbors g s) (in-neighbors g s))) 1)
     (r:= (in-degree g t) 1)
     (r:= (out-degree g t) (if (dp-graph-directed? g) 0 1))
     ;(r:= (set-size (set-∪ (out-neighbors g t) (in-neighbors g t))) 1)
     )))
```

```racket
#;(module+ test
  (require rackunit
           racket/pretty)
  (test-case
   "DFS test"
   (let* ([a-g (make-hash '((v1 v2 v3 v4 v5)
                            (v2 v1 v4 v6)
                            (v3 v1 v5)
                            (v4 v1 v2 v5 v6)
                            (v5 v1 v3 v4 v6)
                            (v6 v2 v4 v5)
                            (v7 v8 v9)
                            (v8 v7)
                            (v9 v7)))])
     (let-values
         ([(v-order order vs) (dp-dfs-pre a-g)])
       (pretty-print v-order)
       (pretty-print order)
       (pretty-print vs)))
   ))
```

</details>
<details>
<summary>mapping-reduction.rkt</summary>

```racket
; mapping constructor
#;(define-syntax mapping
  (syntax-parser
    #;[(_ #:from dom [(~or x:id (x:id #:index ind:id)) (~datum ~>) x-expr])
     #`(let ([elem-with-index (dp-set-element-index dom)])
         (dp-mapping
          (for*/hash ([x (hash-keys elem-with-index)]
                      [#,(if (attribute ind) #'ind #'i)
                       (hash-ref elem-with-index x)])
            (values x x-expr))))]
    [(_ [x (~or (~datum in) (~datum ∈)) X] (~optional (~seq (~datum where) pred-x)) (~datum ~>) x-expr)
     #`(let ([elem-with-index (dp-set-element-index X)])
         (let-values ([(H defined)
                       (for*/fold ([curr-H (hash)] ; 
                                   [defined (for/hash ([k (hash-keys elem-with-index)]) (values k #f))])
                                  ([x (hash-keys elem-with-index)]
                                   ; Question: we actually want a ``let'', simpler way?
                                   [curr-M (list (dp-mapping curr-H defined))]
                                   #:when (~?
                                           (syntax-parameterize
                                              ([curr (make-rename-transformer #'curr-M)])
                                             pred-x)
                                           #t))
                         (values (syntax-parameterize ([curr (make-rename-transformer #'curr-M)])
                                   (hash-set curr-H x x-expr))
                                 (hash-set defined x #t)))])
           (dp-mapping
            H
            #,(if (attribute pred-x)
                  #'defined
                  #'#f)))
         )]
    [(_ sth ...) #'(m-mapping sth ...)]))
```

```racket
; simple testing
#;(mapping [x ∈ (set 0 1 2 3 4 5)] where (and (dp-int-gt x 0)
                                            (not (defined? curr (dp-int-minus x 1))))
           ~> (dp-int-mult 2 x))

#;(mapping [x ∈ (set 0 1 2 3)] ~> (dp-int-mult 2 x)
         [x ∈ (set 3 4 5)] ~> (dp-int-mult 3 x))
```

</details>
<details>
<summary>stepper.rkt</summary>

```racket
#;(define (init-step)
  (define f (new frame%
                 [label "Stepper"]
                 [width 400]
                 [height 300]))
  (define btn (new button%
                   [parent f]
                   [label "Step"]))
  (define t (new pasteboard%) )
  (define the-content (make-object string-snip% ""))
  (define ec (new editor-canvas% [parent f] [editor t]))
  (send t insert the-content)
  (send f show #t)
  f)

#;(define (stepping f text cont)
  )

```

</details>
</details>

<details>
<summary>private/</summary>

<details>
<summary>core-structures.rkt</summary>

```racket
; ---- discarded currently, maybe switch to this design in the future ----
; element
; struct wrapping something, mainly symbol, as id.
; e.g. a number in 2-partition, a vertex of graph, a item in knapsack, etc.
; wrapping a raw symbol enables attaching chaperone properties,
; values, i.e., the value of the number,
;               the weight of the vertex,
;               the value and weight of the item,
; are attached in the chaperone properties
; id : any/c
;

#;(define-values (el-attr has-attr? get-attr)
    (make-impersonator-property 'attr))

#;(r:struct dp-element (id)
          #:methods gen:custom-write
          [(define write-proc
             (r:λ (the-el port mode)
                  (fprintf port "[id:~a, ~a]"
                           (el-id the-el)
                           (let ([the-attr (get-attr the-el)])
                             (string-join
                              (for/list ([(k v) (in-hash the-attr)])
                                (format "~a:~a" k v))
                              ", ")))))])
; ------- end of discarded ------
; ------------------------------------
```

```racket
#;(define (dp-set-from-sol the-sym-set a-sol)
  (if (r:unsat? a-sol) dp-null-set
      (let ([sym-set-hash (dp-set-S the-sym-set)])
      (dp-set (for/hash ([v (hash-keys sym-set-hash)])
                (values v (hash-ref (r:model a-sol)
                                    (hash-ref sym-set-hash v) #f)))))))
```

```racket
#;(define (dp-set/kc v the-srcloc name context [predicate? #f])
  (if (and
       (interfaced-struct? v)
       (assoc 'set (get-interface v)))
      v
      (contract-fail/kc
       the-srcloc name "can not be interpreted as a set"
       context v predicate?)))
```

```racket
#;(define (as-set an-object)
  (r:if (r:and
         (interfaced-struct? an-object)
         (r:assoc 'set (get-interface an-object)))
        ((r:cdr (r:assoc 'set (get-interface an-object))) an-object)
        (error "can not be used as a set:" an-object)))

; internal, should not protect
#;(define/k-contract (as-set an-object)
  (->k [x dp-set/kc] any/kc)
  ((r:cdr (r:assoc 'set (get-interface an-object))) an-object))
```

```racket
; FIXME
#;(define (make-set a-set el-type)
  (let ([the-set (as-set a-set)])
    (make-immutable-hash
     (r:map
      (r:λ (e) (r:cons (struct el-type e) #t))
      (hash-keys (dp-set-S the-set))))))
```

```racket
; begin
; for debugging
#;(begin-for-syntax
  (define-match-expander testB
    (syntax-parser
      [_ #'1])
    (syntax-parser
      [_ #'1])))
#;(define-syntax test1
  (tBool))
; end of debugging
```

```racket
; concrete versions, unsafe when a-element contains symbolic value
#;(define (set-∈ a-element a-set)
  (hash-ref (dp-set-S (as-set a-set)) (dp-wrap-if-raw-int a-element) #f))
#;(define (set-∉ a-element a-set)
  (r:not (set-∈ a-element a-set)))
```

```racket
; fallback to safe version only when a-element is symbolic
; not in use
#;(define (set-∈ a-element a-set)
  (if (dp-symbolic? a-element)
      (set-∈-safe a-element a-set)
      (set-∈-con a-element a-set)))
#;(define (set-∉ a-element a-set)
  (if (dp-symbolic? a-element)
      (set-∉-safe a-element a-set)
      (set-∉-con a-element a-set)))
```

```racket
; null set
; used to represent no solution
#;(define dp-null-set (dp-set #f))

; get the solved set from the rosette solution
; a-sol : r:solution? 
; the-sym-set : (), assumed to be consistent with the solution
#;(define (dp-set-from-sol the-sym-set a-sol)
  (if (r:unsat? a-sol) dp-null-set
      (let ([sym-set-hash (dp-set-S the-sym-set)])
      (dp-set (for/hash ([v (hash-keys sym-set-hash)])
                (values v (hash-ref (r:model a-sol)
                                    (hash-ref sym-set-hash v) #f)))))))

#;(define (dp-element-from-sol the-sym-element a-sol)
  (if (r:unsat? a-sol)
      dp-null-set
      (dp-extract-singleton (dp-set-from-sol the-sym-element a-sol))))
```

```racket
#;(define (dp-symbolic-element-of a-set)
  (let-values ([(sym-set cstrs) (dp-symbolic-subset a-set 1)])
    (values (dp-extract-singleton sym-set)
            ; Note: no need to maintain the cardinality constraint
            ;       for the set, as we are always getting the first
            ;       element in the set and the rest is ignored
            ;       in the solution the first element in the set
            ;       will be the first one satisfying the constraints
            ;       of the problem
            (append
             #;(andmap
             (λ (a-cstr-on-set)
               (λ (a-el)
                 (a-cstr-on-set sym-set)))
             cstrs)
            ; ensure some element is selected, not getting false
            (list (r:λ (a-el) a-el))))))
```

```racket
#;(define-syntax (sum stx)
  (syntax-parse stx
    [(_ val-x (~datum for) x-in-X:element-of-a-set (~optional (~seq (~datum if) pred-x?)))
     #`(r:let ([vals
                 (r:map
                  (r:λ (x-in-X.x)
                       (r:let ([is-in-set
                                 (r:and
                                  (set-∈ x-in-X.x x-in-X.X)
                                  #,(if (attribute pred-x?)
                                        #'pred-x?
                                        #t))])
                              ; keep symbolic union inside struct dp-integer
                              (let ([wrapped-val-x (dp-wrap-if-raw-int val-x)])
                                  (dp-integer (r:if is-in-set (dp-integer-val wrapped-val-x) 0)
                                          (r:if is-in-set (dp-integer-size wrapped-val-x) 'const)))))
                  (dp-ground-set->list x-in-X.X))])        
               (dp-integer
                (r:apply r:+ (r:map dp-int-unwrap vals))
                (dp-int-lst-max-size vals)))
]))
```
</details>
<details>
<summary>dp-stx-info.rkt</summary>

```racket
  ; why this does not work
  #;(define-syntax dp-type-info
    (syntax-parser
      [(_ (~seq key:id value) ...+)
       #:with ks #'(key ...)
       #:with vs #'(value ...)
       #`(make-immutable-hash
          '#,(for*/list
                 ([k (syntax->list #'ks)]
                  [v (syntax->list #'vs)])
               (cons (syntax->datum k) v)))]))
```

```racket
  #;(define-syntax dp-stx-type-info
    (syntax-parser
      [(_ base-stx (~seq key:id value) ...+)
       #:with kvs #'((key value) ...)
       #`(syntax-property
          base-stx
          'type-info
          (hash
           #,@(flatten
               (map
                (λ (x) (cons #`'#,(syntax->datum
                                 (car (syntax->list x)))
                             (cdr (syntax->list x))))
                (syntax->list #'kvs)))))]))
```

```racket
    #;(define-syntax dp-stx-type-info-accessor-ref
      (syntax-parser
        [(_ x key)
         #'(assoc
            key
            (dp-stx-type-info-field
             x
             accessors))]))
```

```racket
    #;(define-syntax dp-stx-type-desc-accessor-ref
      (syntax-parser
        [(_ x key)
         #'(assoc
            key
            (dp-stx-type-desc-field
             x
             accessors))]))
```

```racket
    #;(define-syntax dp-stx-type-info-data-ref
      (syntax-parser
        [(_ x key)
         #'(assoc
            key
            (dp-stx-type-info-field
             x
             type-data))]))
```

```racket
    #;(define-syntax dp-stx-type-desc-data-ref
      (syntax-parser
        [(_ x key)
         #'(assoc
            key
            (dp-stx-type-desc-field
             x
             type-data))]))
```

```racket
#;(define-syntax test-type
  (syntax-parser
    [(_ k:id v) (dp-stx-type-info #'2 k (+ 1 2) gt (string-append "abc" "def"))]))

#;(define-syntax test-inspector
  (syntax-parser
    [(_ t k:id)
     #`#,(dp-stx-type-info-field
          (local-expand #'t 'expression #f) gt)]))

#;(test-inspector (test-type a 1) a)

#;(pretty-print
 (dp-type-info-field
  (dp-type-info a 1 b 2) c))
```

</details>

<details>
<summary>primitive-data-type.rkt</summary>

```racket
; old version
#;(define-syntax (natural stx)
  (syntax-parse stx
    [(_)
     (if (dp-parse-table)
         ; same for inst and cert env
         (dp-stx-type-desc
          (generate-temporary #'natural)
          type 'natural
          kv-type-object #'(tInt)
          atomic? #t
          ctc #'natural/c
          v-dep-ctc #'v-dep-any/c
          type-data '()
          accessors '()
          ; Note: natural can not be used as solvable
          ;symbolic-constructor #'(λ (a-inst) dp-symbolic-natural)
          ;solution-decoder #'dp-natural-from-sol
          ;null-object #'dp-null-natural
          generator #'(λ (a-inst)
                        (λ ()
                          (gen-random-natural)))
          )
         (raise-syntax-error 'natural unsupport-outside-problem-definition-msg stx))]
    [_:id #'(natural)]))

```

```racket
#;(kv-func-type-annotate r:nand ((tBool) (tBool) (tBool)) "two booleans")
(provide nand-typed-rewriter)
(define-syntax nand-typed-rewriter
  (λ (arg-lst)
    (match arg-lst
      [(list (cons _ (tBool)) ...)
       (λ (stx) (cons stx (tBool)))]
      [_ (syntax-parser
           [(nand arg ...)
            (raise-syntax-error #f
                                (format "expects booleans, gets ~a"
                                        (map get-τb arg-lst))
                                #'(nand arg ...)
                                #'nand)])])))
#;(kv-func-type-annotate r:or ((tBool) (tBool) (tBool)) "two booleans")
(provide or-typed-rewriter)
(define-syntax or-typed-rewriter
  (λ (arg-lst)
    (match arg-lst
      [(list (cons _ (tBool)) ...)
       (λ (stx) (cons stx (tBool)))]
      [_ (syntax-parser
           [(or arg ...)
            (raise-syntax-error #f
                                (format "expects booleans, gets ~a"
                                        (map get-τb arg-lst))
                                #'(or arg ...)
                                #'or)])])))
```

</details>

<details>
<summary>problem-definition-utility.rkt</summary>

```racket
  #;(define (assert-parse-table-ref id-stx)
    (let ([entry (free-id-table-ref (dp-parse-table) id-stx #f)])
      (if entry
          entry
          (raise-syntax-error #f "undefined instance part" id-stx))))

```

```racket
  ; old versions
  #;(define-syntax (dp-expand-part stx)
      (syntax-parse stx
        [(_ part-stx)
         #'(local-expand part-stx 'expression #f)]))
  #;(define-syntax (dp-expand-parts stx)
      (syntax-parse stx
        [(_ parts-stx)
         #'(map
            (λ (a-stx)
              (local-expand a-stx 'expression #f))
            (stx->list parts-stx))]))

#;#'(begin (struct my-element ())
         (....  (struct/c my-element)))
```

</details>
</details>
