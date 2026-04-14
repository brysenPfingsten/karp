#lang racket
(require
  "private/primitive-data-type.rkt"
  "private/karp-contract.rkt"
  [for-syntax syntax/parse])

; abstract elements with subscripts
(provide el
         el?
         el/kc
         _1s
         _2s
         _3s
         _ks
         n_s)

(struct el-struct (subscripts) #:transparent
   #:methods gen:custom-write
  [(define write-proc
     (λ (the-el port mode)
       (fprintf port "<~a>"
                (string-join
                 (for/list ([s (el-struct-subscripts the-el)])
                   (format "~a" s))
                 ", "))))])

(define-syntax (el stx)
  (syntax-parse stx
    [(_ subscript0 ...+)
     #'(el-struct (list (dp-wrap-if-raw-int subscript0) ...))]))

(define (el? a-sth)
  (el-struct? a-sth))

(define-simple-contract/kc el/kc (v)
  (el? v)
  "expects an element")

; first subscript
(define/contract/kc (_1s a-el)
  (->k ([a-el el/kc]) any/kc)
  (list-ref (el-struct-subscripts a-el) 0))

; second subscript
(define/contract/kc (_2s a-el)
  (->k ([a-el el/kc]) any/kc)
  (list-ref (el-struct-subscripts a-el) 1))

; third subscript
(define/contract/kc (_3s a-el)
  (->k ([a-el el/kc]) any/kc)
  (list-ref (el-struct-subscripts a-el) 2))

; k-th subscript
(define/contract/kc (_ks a-el k)
  (->k ([a-el el/kc] [k (and/kc
                          (dp-natural-w/kc 'const)
                          (make-simple-contract/kc (v)
                            (dp-int-ge v 1)
                            "subscript index needs to be at least 1"))]) any/kc)
  (list-ref (el-struct-subscripts a-el) (- (dp-int-unwrap k) 1)))

; length of subscript
(define/contract/kc (n_s a-el)
  (->k ([a-el el/kc]) (dp-natural-w/kc 'const))
  (dp-int-wrap (length (el-struct-subscripts a-el)) 'const))
