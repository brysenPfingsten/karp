#lang racket

(require racket/generic)

(provide
 ; mergeable interface
 gen:dp-mergeable
 dp-mergeable?
 gen-merge-union
 gen-decode-merged-from-sol
 gen-representative-el-from-lst)


;
; mergable interface
; structure the symbolic union of which can be merged
; see also : element-of
;
(define-generics dp-mergeable
  ; U : the symbolic union to be merged
  ; dp-mergeable : this argument should be a value of a component of the symbolic union
  (gen-merge-union U dp-mergeable)
  (gen-representative-el-from-lst v-lst dp-mergeable) ; the last argument is a dummy used for dispatch
  (gen-decode-merged-from-sol dp-mergeable sol))
