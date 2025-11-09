#lang racket
(require
  "private/primitive-data-type.rkt"
  [for-syntax syntax/parse])

; abstract elements with subscripts
(provide el
         el?
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

; TODO: Add contracts to subscript accessors
; first subscript
(define (_1s a-el)
  (list-ref (el-struct-subscripts a-el) 0))

; second subscript
(define (_2s a-el)
  (list-ref (el-struct-subscripts a-el) 1))

; third subscript
(define (_3s a-el)
  (list-ref (el-struct-subscripts a-el) 2))

; k-th subscript
(define (_ks a-el k)
  ; TODO: require k to be a constant
  (list-ref (el-struct-subscripts a-el) (- k 1)))

; length of subscript
(define (n_s a-el)
  (length (el-struct-subscripts a-el)))
