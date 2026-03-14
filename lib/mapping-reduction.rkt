#lang racket

(require [except-in "../reduction-base.rkt" define]
         [rename-in "mapping.rkt" [mapping m-mapping] ]
         [for-syntax syntax/parse
                     syntax/stx
                     racket/list]
         "../private/karp-contract.rkt"
         racket/stxparam
         racket/syntax-srcloc)


(provide mapping
         defined?
         (all-from-out "mapping.rkt"))


(define (defined? a-mapping k)
  (hash-ref (dp-mapping-defined a-mapping) k #f))

(define-syntax build-mapping-core
  (syntax-parser
    [(_ curr-H curr-defined (x0:id X0 (~optional pred-x0) x-expr0) (x:id X (~optional pred-x) x-expr) ...)
     #:with rest-xs #'(x ...)
     #`(let-values
           ([(res-H res-defined)
             (let ([elem-with-index (dp-set-element-index X0)])
               (for*/fold ([H curr-H] ; 
                           [defined curr-defined])
                          ([x0 (hash-keys elem-with-index)]
                           ; Question: we actually want a ``let'', simpler way?
                           [curr-M (list (dp-mapping H #f defined))] ; intemmediate result, el-rep not set
                           #:when (~?
                                   (syntax-parameterize
                                       ([curr (make-rename-transformer #'curr-M)])
                                     pred-x0)
                                   #t))
                 (values (syntax-parameterize ([curr (make-rename-transformer #'curr-M)])
                           (hash-set H x0 x-expr0))
                         (hash-set defined x0 #t))))])
         #,(if (equal? (length (stx->list #'rest-xs)) 0)
               #'(dp-mapping
                  res-H
                  (if (dp-mergeable? (car (hash-values res-H)))
                      (gen-representative-el-from-lst (hash-values res-H) (car (hash-values res-H)))
                      #f)
                  ; clear the temporary state for whether a key is defined
                  #f)
               #'(build-mapping-core res-H res-defined (x X (~? pred-x) x-expr) ...)))]))

; For elements appears in multiple sets, later will override the former
; See mapping-reduction-test.rkt for examples
(define-syntax mapping
  (syntax-parser
    [(_ (~seq [x (~or (~datum in) (~datum ∈)) X] (~optional (~seq (~datum where) pred-x)) (~datum ~>) x-expr) ...+)
     #:with (X/kc ...)
     (let ([Xs (syntax->list #'(X ...))])
       (for/list ([i (range 1 (+ (length Xs) 1))]
                  [an-X Xs])
         #`(contracted-v/kc
            dp-set/kc #,an-X (syntax-srcloc #'#,an-X) 'mapping
            (list (format "the ~v~s set" #,i
                          '#,(ordinal-numeral i))))))
     #`(build-mapping-core
        (hash) ; init curr-H to empty hash 
        (for/hash ([k (dp-set-members->list (set-∪ X/kc ...))]) (values k #f)) ; init curr-defined to indicate nothing is defined
        (x X/kc (~? pred-x) x-expr) ...)]
    [(_ sth ...) #'(m-mapping sth ...)]))
