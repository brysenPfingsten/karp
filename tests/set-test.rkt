#lang racket

(require "../private/core-structures/set.rkt"
         "../private/karp-contract.rkt"
         "../private/primitive-data-type.rkt"
         (prefix-in r: rosette/safe)
         rackunit rackunit/text-ui
         (only-in racket/set list->set))

(define (normalize-member v)
  (if (dp-integer? v)
      (dp-integer-val v)
      v))

(define (members->set a-set)
  (list->set (map normalize-member (dp-set-members->list a-set))))

(define/provide-test-suite
  SET

  (test-case "Constructors and basics"
    (define s1 (a-set 1 2 3))
    (define s2 (set 1 2 3))
    (check-true (dp-set? s1))
    (check-true (dp-set/c s1))
    (check-true (set-∈ 2 s2))
    (check-false (set-∉ 2 s2))
    (check-true (dp-set/kc s1 #f #f '() #t))
    (check-equal? (members->set s1) (members->set s2)))

  (test-case "Conversions and ground set"
    (define s1 (dp-list->set '(1 2 3)))
    (define s2 (dp-list-list->set '(1 2) '(2 3)))
    (define g2 (set-ground-set s2))
    (check-true (hash-ref (dp-set-S s1) 1 #f))
    (check-false (hash-ref (dp-set-S s2) 3 #f))
    (check-true (hash-ref (dp-set-S g2) 3 #f))
    (check-equal? (members->set g2) (list->set (dp-ground-set->list s2)))
    (check-equal? (members->set (dp-set-shrink s2)) (members->set (dp-list->set '(1 2)))))

  (test-case "Membership and subset contracts"
    (define s1 (set 1 2 3))
    (define nested (set (set 1 2) (set 2 3)))
    (define setof-any (dp-setof/kc any/kc))
    (define (el-ctc-d _v) any/kc)
    (define setof-any-d ((dp-setof-d/kc el-ctc-d) 'ignored))
    (define subset-ctc (dp-subset-of-d/kc s1))
    (define in-s1-ctc (set-∈-d/kc s1))
    (check-true (setof-any s1 #f #f '() #t))
    (check-true (setof-any-d s1 #f #f '() #t))
    (check-true (subset-ctc (set 1 2) #f #f '() #t))
    (check-false (subset-ctc (set 4) #f #f '() #t))
    (check-true (in-s1-ctc 2 #f #f '() #t))
    (check-false (in-s1-ctc 9 #f #f '() #t))
    (check-true (set-∈-safe (set 1 2) nested))
    (check-true (set-∉-safe (set 9 10) nested)))

  (test-case "Relations and operations"
    (define s1 (set 1 2 3))
    (define s2 (set 3 4))
    (define s3 (dp-set-remove s1 (dp-wrap-if-raw-int 2)))
    (define s4 (dp-set-filter (λ (v) (odd? (dp-int-unwrap v))) s1))
    (define union (set-∪ s1 s2))
    (define inter (set-∩ s1 s2))
    (define diff (set-minus s1 s2))
    (check-true (set-subset-of? inter s1))
    (check-true (set-equal? (set-∪ s1 s2) union))
    (check-true (set-∈ 1 s3))
    (check-false (set-∈ 2 s3))
    (check-true (set-∈ 1 s4))
    (check-false (set-∈ 2 s4))
    (check-true (set-∈ 4 union))
    (check-true (set-∈ 3 inter))
    (check-true (set-∈ 1 diff))
    (check-false (set-∈ 3 diff))
    (check-equal? (dp-int-unwrap (set-size s1)) 3))

  (test-case "Set size contracts"
    (define s1 (set 1 2))
    (define size-ctc (dp-set-size=-d/kc 2))
    (define set-with-size (dp-set-with-size=/kc 2))
    (check-equal? (size-ctc s1 #f #f '() #f) s1)
    (check-equal? (set-with-size s1 #f #f '() #f) s1)
    (check-exn exn:fail? (λ () (size-ctc (set 1 2 3) #f #f '() #f))))

  (test-case "Random subset"
    (random-seed 1)
    (define s1 (set 1 2 3 4 5))
    (define sub (random-subset s1 3 #:exact-n? #f))
    (check-true (set-subset-of? sub s1))
    (check-equal? (dp-int-unwrap (set-size sub)) 3))

  (test-case "Symbolic sets and solutions"
    (define base (set 1 2))
    (define-values (sym-set _cstrs) (dp-symbolic-subset base))
    (define sym-hash (dp-set-S sym-set))
    (define k (first (hash-keys sym-hash)))
    (define sol (r:solve (r:assert (hash-ref sym-hash k))))
    (define solved (dp-set-from-sol sym-set sol))
    (check-true (set-∈ k solved))
    (define unsat-sol (r:solve (r:assert #f)))
    (check-equal? (dp-set-from-sol sym-set unsat-sol) dp-null-set))

  (test-case "Symbolic elements"
    (define base (set 1 2))
    (define-values (sym-el _cstrs) (dp-symbolic-element-of base))
    (define sol (r:solve (r:assert (dp-equal? sym-el 1))))
    (check-equal? (dp-int-unwrap (dp-element-from-sol sym-el sol)) 1))

  (test-case "Quantifiers and aggregations"
    (define s1 (set 1 2 3))
    (check-true (∀ [x ∈ s1] (dp-int-ge x 1)))
    (check-false (∀ [x ∈ s1] (dp-int-ge x 2)))
    (check-true (∃ [x ∈ s1] (dp-equal? x 2)))
    (check-true (at-most-1-element-of [x ∈ s1] (dp-equal? x 2)))
    (check-true (exactly-1-element-of [x ∈ s1] (dp-equal? x 2)))
    (check-equal? (dp-int-unwrap (sum x for [x ∈ s1])) 6)
    (check-equal? (dp-int-unwrap (max x for [x ∈ s1])) 3)
    (check-equal? (dp-int-unwrap (min x for [x ∈ s1])) 1)
    (check-equal? (dp-int-unwrap (count [x ∈ s1] s.t. (dp-int-ge x 2))) 2))

  (test-case "Equality helpers"
    (check-true (dp-equal? 1 1))
    (check-false (dp-equal? 1 2))
    (check-true (different? 1 2))
    (check-false (different? 2 2)))

  (test-case "Syntax-only forms error outside problem definition"
    (check-exn exn:fail:syntax? (λ () (expand #'(dont-care))))
    (check-exn exn:fail:syntax? (λ () (expand #'(element))))
    (check-exn exn:fail:syntax? (λ () (expand #'(the-set-of any))))
    (check-exn exn:fail:syntax? (λ () (expand #'(the-product-of any))))
    (check-exn exn:fail:syntax? (λ () (expand #'(subset-of s1))))
    (check-exn exn:fail:syntax? (λ () (expand #'(element-of s1))))))

;; (require rackunit/text-ui)
;; (run-tests SET)
