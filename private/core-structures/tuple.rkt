#lang racket

(require [for-syntax racket/struct
                     racket/syntax
                     syntax/parse
                     racket/function
                     racket/match]
         [for-meta 2 racket/base
                   syntax/parse])
(require [prefix-in r: rosette/safe])
(require (only-in "./set.rkt" 
                  dp-list->set
                  dp-set-members->list)
         "../../private/verifier-type.rkt"
         "../../private/karp-contract.rkt"
         "../../private/problem-definition-utility.rkt"
         "../../private/primitive-data-type.rkt")

(provide
 (struct-out dp-tuple)
 fst
 snd
 trd
 frh
 ffh
 n-th
 tpl

 tuple

 dp-tuple-any/kc
 dp-duple-with-length=/kc
 dp-tuple/kc
 )

; type object representing Tuple
(begin-for-syntax
  (provide tTuple)

  (struct ty-Tuple (type-lst)
    #:property prop:type-interface (list (r:cons 'tuple r:identity))
    #:methods gen:custom-write
    [(define write-proc
       (make-constructor-style-printer
        (λ (self) 'Tuple)
        (λ (self) (ty-Tuple-type-lst self))))])

  (define (as-ty-Tuple a-t)
    (and
     (interfaced-type? a-t)
     ; get a function always return #f when a-t does not have a interpretation
     ; as ty-Tuple
     ((cdr (or (assoc 'tuple (get-type-interface a-t))
               (cons '() (const #f))))
      a-t)))
  
  (define-match-expander tTuple
    (syntax-parser
      [(_ el-type0 el-type ...)
       #'(app as-ty-Tuple (ty-Tuple (list el-type0 el-type ...)))])
    ; used as the constructor for type object outside ```match'''
    (syntax-parser
      [(_ #:list lst) #'(ty-Tuple lst)]
      [(_ el-type0 el-type ...) #'(ty-Tuple (list el-type0 el-type ...))]))

)

; fallback to Racket
; see also : dp-set
; TODO : make underlying representation of symbolic tuple
;        conform with mappings
(struct dp-tuple (lst) #:transparent
          #:property prop:interface
                    (r:list
                       (r:cons 'set
                               (r:λ (tpl)
                                    (dp-list->set (dp-tuple-lst tpl)))))
          #:methods gen:custom-write
          [(define write-proc
             (r:λ (the-tuple port mode)
                  (fprintf port "~a"
                           (dp-tuple-lst the-tuple))))])

(define-simple-contract/kc dp-tuple-any/kc (v)
  (dp-tuple? v)
  "expects a tuple")

(define (dp-duple-with-length=/kc n)
  (and/kc
   dp-tuple-any/kc
   (kc-contract (v the-srcloc name context [predicate? #f])
      (if (equal? (length (dp-tuple-lst v))
                  (dp-int-unwrap n))
          v
          (contract-fail/kc the-srcloc name
                            (format "expects a tuple with exactly ~e components" (dp-int-unwrap n))
                            context v predicate?)))))

(define (dp-duple-with-length>=/kc n)
  (and/kc
   dp-tuple-any/kc
   (kc-contract (v the-srcloc name context [predicate? #f])
      (if (>= (length (dp-tuple-lst v))
              (dp-int-unwrap n))
          v
          (contract-fail/kc the-srcloc name
                            (format "expects a tuple with at least ~e components" (dp-int-unwrap n))
                            context v predicate?)))))

; XXX: element accessors of the tuple might not support
;      symbolic tuples at this point
(define/contract/kc (fst a-tuple)
  (->k ([x (dp-duple-with-length>=/kc 1)]) any/kc)
  (r:first (dp-tuple-lst a-tuple)))
(kv-func-type-annotate fst ((tTuple τb1 τb2 ...) τb1)
                       "a tuple")

(define/contract/kc (snd a-tuple)
  (->k ([x (dp-duple-with-length>=/kc 2)]) any/kc)
  (r:second (dp-tuple-lst a-tuple)))
(kv-func-type-annotate snd ((tTuple τb1 τb2 τb3 ...) τb2)
                       "a tuple")

(define/contract/kc (trd a-tuple)
  (->k ([x (dp-duple-with-length>=/kc 3)]) any/kc)
  (r:third (dp-tuple-lst a-tuple)))
(kv-func-type-annotate trd ((tTuple τb1 τb2 τb3 τb4 ...) τb3)
                       "a tuple of at least 3 components")

(define/contract/kc (frh a-tuple)
  (->k ([x (dp-duple-with-length>=/kc 4)]) any/kc)
  (r:fourth (dp-tuple-lst a-tuple)))
(kv-func-type-annotate frh ((tTuple τb1 τb2 τb3 τb4 τb5 ...) τb4)
                       "a tuple of at least 4 components")

(define/contract/kc (ffh a-tuple)
  (->k ([x (dp-duple-with-length>=/kc 5)]) any/kc)
  (r:fifth (dp-tuple-lst a-tuple)))

(define/contract/kc (n-th a-tuple n)
  (->k ([x (dp-duple-with-length>=/kc n)]) any/kc)
  (r:list-ref (dp-tuple-lst a-tuple) n))

(define (dp-tuple/c . el-ctcs)
  (struct/c dp-tuple
            (apply list/c el-ctcs)))

(define (dp-tuple/kc . el-ctcs)
  (and/kc
   (dp-duple-with-length=/kc (length el-ctcs))
   (kc-contract (v the-srcloc name context [predicate? #f])
    (let* ([the-tpl v]
           [the-lst (dp-tuple-lst v)]
           [success? (andmap
                       (λ (i)
                         ; error triggered here if violation
                         ((list-ref el-ctcs i) (list-ref the-lst i)
                          the-srcloc name         
                          (cons (format "the ~v~s component of" i
                                        (cond [(equal? i 1) 'st]
                                              [(equal? i 2) 'nd]
                                              [(equal? i 3) 'rd]
                                              [else 'th]))
                                context)
                          predicate?))
                       (range (length the-lst)))])
      (if predicate? success? v)))))


; construct a contract factory for contract of tuple
; internal
; Note: value-dependent version, produce a factory accepting dependent values
; See also: dp-setof-d/c
; el-ctc-d : (-> any/c ... (-> any/c boolean?)), contract of one of the element
; ......
; -> (-> any/c ... (any/c -> boolean?))
(define ((dp-tuple-d/c . el-ctcs-d) v . rest)
  (λ (a-tuple)
   (andmap
    (λ (i)
      ((apply (list-ref el-ctcs-d i) (cons v rest))
       (list-ref (dp-tuple-lst a-tuple) i)))
    (range (length (dp-tuple-lst a-tuple))))))

(define ((dp-tuple-d/kc . el-ctcs-d) v . rest) ; curried shorthand
  ; produce contract of elements given dependent values
  (let ([el-ctcs
         (map
          (λ (a-ctc-d) (apply a-ctc-d (cons v rest)))
          el-ctcs-d)])
    (and/kc
     dp-tuple-any/kc
     (kc-contract (v the-srcloc name context [predicate? #f])
      (let* ([the-tpl v]
             [the-lst (dp-tuple-lst v)]
             [success? (andmap
                        (λ (i)
                          ; error triggered here if violation
                          ((list-ref el-ctcs i) (list-ref the-lst i)
                          the-srcloc name         
                          (cons (format "the ~v~s component of" i
                                        (cond [(equal? i 1) 'st]
                                              [(equal? i 2) 'nd]
                                              [(equal? i 3) 'rd]
                                              [else 'th]))
                                context)
                          predicate?))
                        (range (length the-lst)))])
        (if predicate? success? v))))
    ))


; tuple constructor
(define (tpl v . rest)
  (dp-tuple (cons v rest)))

; create the cartisan product of sets
; ∀(dp-setof/c α) ... -> (dp-setof/c (dp-tuple/c α) ...)
; potentially expensive, internal, nonsolvable
(define (dp-set-product . rest)
  (dp-list->set
   (map
    dp-tuple
    (apply cartesian-product
           (map
            dp-set-members->list
            rest)))))

; tuple
(define-syntax (tuple stx)
  (if (dp-parse-table)
      (if
       ; only valid in inst enviroment
       (not (dp-part-cert-env?))
       (syntax-parse stx
         [(_ (~seq #:field-type type-desc) ...)
          (let* ([el-types
                  (map
                   (λ (a-stx) (dp-stx-type-desc a-stx))
                   (dp-expand-parts
                    #'(type-desc ...)))]
                 [el-kv-type-objects
                  (map (λ (a-type-info)
                         (dp-stx-info-field a-type-info kv-type-object))
                       el-types)]  
                 [el-ctcs (map (λ (a-stx-info) (dp-stx-info-field a-stx-info ctc)) el-types)]
                 [el-v-dep-ctcs (map (λ (a-stx-info) (dp-stx-info-field a-stx-info v-dep-ctc)) el-types)]
                 [tuple-ctc #`(dp-tuple/kc #,@el-ctcs)]
                 [tuple-v-dep-ctc #`(dp-tuple-d/kc #,@el-v-dep-ctcs)]
                 ; ids in referred parts
                 [type-desc-ids (apply append
                                       (map
                                        (λ (a-stx-info)
                                          (let ([a-id (dp-stx-info-field a-stx-info referred-ids)])
                                            (if (equal? a-id 'undefined)
                                                '()
                                                a-id)))
                                        el-types))])
            (dp-stx-type-desc (generate-temporary #'tuple)
                              type 'tuple
                              kv-type-object #`(tTuple #,@el-kv-type-objects)
                              atomic? #f
                              ctc tuple-ctc
                              v-dep-ctc tuple-v-dep-ctc
                              ; XXX: currently not supporting creating new element structureb
                              #;el-type-to-make #;(apply append
                                                     (map
                                                      (λ (a-stx-info)
                                                        (dp-stx-info-field a-stx-info el-type-to-make))
                                                      el-types))
                              type-data (list (cons 'el-types el-types))
                              accessors '()
                              generator #`(λ (a-inst)
                                            (apply
                                             dp-tuple
                                             #,(map
                                                (λ (el-type)
                                                  #`((#,(dp-stx-info-field el-type generator) a-inst)))
                                                el-types)))
                              referred-ids type-desc-ids))])
       (raise-syntax-error #f unsupport-in-certificate-msg stx))
      (syntax-parse stx
        [(_ elements ...)
         #'(tpl (dp-wrap-if-raw-int elements) ...)])))
