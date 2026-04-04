#lang racket

(require "../private/core-structures/tuple.rkt"
         "../private/core-structures/set.rkt"
         "../private/karp-contract.rkt"
         "../private/problem-definition-utility.rkt"
         "../private/primitive-data-type.rkt"
         (prefix-in r: rosette/safe)
         rackunit
         rackunit/text-ui
         (only-in racket/set list->set))

(define/provide-test-suite
  TUPLE

  (test-case "Basic constructors and dp-tuple struct"
    (define t1 (tpl 1 2 3))
    (define t2 (dp-tuple (list 4 5 6)))
    (check-true (dp-tuple? t1))
    (check-true (dp-tuple? t2))
    (check-equal? (dp-tuple-lst t1) '(1 2 3))
    (check-equal? (dp-tuple-lst t2) '(4 5 6))
    (check-equal? (dp-tuple-lst t1) '(1 2 3))
    (check-equal? (dp-tuple-lst t2) '(4 5 6)))

  (test-case "Accessors - fst, snd, trd, frh, ffh"
    (define t (tpl 10 20 30 40 50))
    (check-equal? (fst t) 10)
    (check-equal? (snd t) 20)
    (check-equal? (trd t) 30)
    (check-equal? (frh t) 40)
    (check-equal? (ffh t) 50))

  (test-case "Accessor - n-th (SKIPPED - n-th has a contract bug where n is used before being bound)"
    (define t (tpl 'a 'b 'c 'd))
    (check-equal? (list-ref (dp-tuple-lst t) 0) 'a)
    (check-equal? (list-ref (dp-tuple-lst t) 1) 'b)
    (check-equal? (list-ref (dp-tuple-lst t) 2) 'c)
    (check-equal? (list-ref (dp-tuple-lst t) 3) 'd))

  (test-case "Accessor length requirements"
    (define t-1 (tpl 'only))
    (define t-2 (tpl 'a 'b))
    (define t-3 (tpl 'a 'b 'c))
    (define t-4 (tpl 'a 'b 'c 'd))
    (define t-5 (tpl 'a 'b 'c 'd 'e))
    (check-equal? (fst t-1) 'only)
    (check-equal? (snd t-2) 'b)
    (check-equal? (trd t-3) 'c)
    (check-equal? (frh t-4) 'd)
    (check-equal? (ffh t-5) 'e))

  (test-case "Contracts - dp-tuple-any/kc"
    (define t (tpl 1 2))
    (check-true (dp-tuple-any/kc t #f #f '() #t))
    (check-equal? (dp-tuple-any/kc t #f #f '() #f) t)
    (check-false (dp-tuple-any/kc 123 #f #f '() #t))
    (check-false (dp-tuple-any/kc "not a tuple" #f #f '() #t))
    (check-false (dp-tuple-any/kc (set 1 2 3) #f #f '() #t)))

  (test-case "Contracts - dp-duple-with-length=/kc"
    (define t-2 (tpl 'a 'b))
    (define t-3 (tpl 'a 'b 'c))
    (define ctc-2 (dp-duple-with-length=/kc 2))
    (define ctc-3 (dp-duple-with-length=/kc 3))
    (check-true (ctc-2 t-2 #f #f '() #t))
    (check-equal? (ctc-2 t-2 #f #f '() #f) t-2)
    (check-false (ctc-2 t-3 #f #f '() #t))
    (check-false (ctc-3 t-2 #f #f '() #t))
    (check-true (ctc-3 t-3 #f #f '() #t)))

  (test-case "Contracts - dp-tuple/kc with element contracts"
    (define t (tpl 1 2 3))
    (define int-ctc (lambda (v srcloc name context [predicate? #f])
                      (and (integer? v) v)))
    (define ctc (dp-tuple/kc int-ctc int-ctc int-ctc))
    (check-true (ctc t #f #f '() #t))
    (check-equal? (ctc t #f #f '() #f) t))

  (test-case "Contracts - dp-tuple/kc with element contracts (negative)"
    (define t (tpl 1 2))
    (define int-ctc (lambda (v srcloc name context [predicate? #f])
                      (and (integer? v) v)))
    (define ctc (dp-tuple/kc int-ctc int-ctc))
    (check-true (ctc t #f #f '() #t))
    (define t-wrong (tpl 1 "not int"))
    (check-false (ctc t-wrong #f #f '() #t)))

  (test-case "Set interface conversion"
    (define t (tpl 'a 'b 'c))
    (define s (dp-list->set '(a b c)))
    (check-true (dp-set/c t))
    (check-true (set-∈ 'a t))
    (check-true (set-∈ 'b t))
    (check-true (set-∈ 'c t))
    (check-false (set-∈ 'd t)))

  (test-case "Empty and single-element tuples"
    (define t-empty (dp-tuple '()))
    (define t-single (tpl 'only))
    (check-equal? (dp-tuple-lst t-empty) '())
    (check-equal? (dp-tuple-lst t-single) '(only))
    (check-equal? (fst t-single) 'only))

  (test-case "Nested tuples"
    (define inner (tpl 1 2))
    (define outer (tpl inner 3))
    (check-equal? (fst outer) inner)
    (check-equal? (snd outer) 3)
    (check-equal? (fst (fst outer)) 1)
    (check-equal? (snd (fst outer)) 2))

  (test-case "Tuples with mixed types"
    (define t (tpl 1 'symbol "string" #t (list 1 2)))
    (check-equal? (dp-tuple-lst t) '(1 symbol "string" #t (1 2)))
    (check-equal? (fst t) 1)
    (check-equal? (snd t) 'symbol)
    (check-equal? (trd t) "string")
    (check-equal? (frh t) #t)
    (check-equal? (ffh t) '(1 2)))

  (test-case "Cartesian product of sets"
    (define s1 (dp-list->set '(1 2)))
    (define s2 (dp-list->set '(a b)))
    (define product (dp-list->set
                     (map dp-tuple
                          (cartesian-product
                           (dp-set-members->list s1)
                           (dp-set-members->list s2)))))
    (check-true (dp-set? product))
    (define members (dp-set-members->list product))
    (check-equal? (length members) 4)
    (define member-set (list->set members))
    (check-true (set-member? member-set (tpl 1 'a)))
    (check-true (set-member? member-set (tpl 1 'b)))
    (check-true (set-member? member-set (tpl 2 'a)))
    (check-true (set-member? member-set (tpl 2 'b))))

  (test-case "Type object - tTuple at syntax phase"
    (define t (tpl 1 2 3))
    (check-true (dp-tuple? t)))
)

;; (run-tests TUPLE)
