#lang racket

(require "../el.rkt"
         "../private/karp-contract.rkt"
         "../private/problem-definition-utility.rkt"
         "../private/primitive-data-type.rkt"
         (prefix-in r: rosette/safe)
         rackunit)

(define/provide-test-suite
  EL

  (test-case "Basic element construction"
    (define e1 (el 1))
    (define e2 (el 1 2))
    (define e3 (el 1 2 3))
    (check-true (el? e1))
    (check-true (el? e2))
    (check-true (el? e3)))

  (test-case "Element construction with symbols"
    (define e1 (el 'a))
    (define e2 (el 'x 'y))
    (define e3 (el 1 'b 3))
    (check-true (el? e1))
    (check-true (el? e2))
    (check-true (el? e3)))

  (test-case "Element construction with mixed types"
    (define e1 (el 1 '- 0))
    (define e2 (el 's))
    (define e3 (el 1 2 '+))
    (check-true (el? e1))
    (check-true (el? e2))
    (check-true (el? e3)))

  (test-case "el? predicate - positive cases"
    (define e1 (el 1))
    (define e2 (el 1 2 3 4 5))
    (check-true (el? e1))
    (check-true (el? e2)))

  (test-case "el? predicate - negative cases"
    (check-false (el? 123))
    (check-false (el? "string"))
    (check-false (el? 'symbol))
    (check-false (el? '(1 2 3)))
    (check-false (el? #f)))

  (test-case "Accessor _1s - first subscript"
    (define e1 (el 10))
    (define e2 (el 10 20))
    (define e3 (el 10 20 30))
    (check-equal? (dp-int-unwrap (_1s e1)) 10)
    (check-equal? (dp-int-unwrap (_1s e2)) 10)
    (check-equal? (dp-int-unwrap (_1s e3)) 10))

  (test-case "Accessor _1s - with symbols"
    (define e1 (el 'a))
    (define e2 (el 'x 'y 'z))
    (check-equal? (_1s e1) 'a)
    (check-equal? (_1s e2) 'x))

  (test-case "Accessor _2s - second subscript"
    (define e1 (el 10 20))
    (define e2 (el 10 20 30))
    (check-equal? (dp-int-unwrap (_2s e1)) 20)
    (check-equal? (dp-int-unwrap (_2s e2)) 20))

  (test-case "Accessor _2s - with symbols"
    (define e (el 'a 'b))
    (check-equal? (_2s e) 'b))

  (test-case "Accessor _3s - third subscript"
    (define e1 (el 10 20 30))
    (define e2 (el 1 2 3 4 5))
    (check-equal? (dp-int-unwrap (_3s e1)) 30)
    (check-equal? (dp-int-unwrap (_3s e2)) 3))

  (test-case "Accessor _3s - with symbols"
    (define e (el 'x 'y 'z))
    (check-equal? (_3s e) 'z))

  (test-case "Accessor _ks - arbitrary subscript"
    (define e (el 10 20 30 40 50))
    (check-equal? (dp-int-unwrap (_ks e 1)) 10)
    (check-equal? (dp-int-unwrap (_ks e 2)) 20)
    (check-equal? (dp-int-unwrap (_ks e 3)) 30)
    (check-equal? (dp-int-unwrap (_ks e 4)) 40)
    (check-equal? (dp-int-unwrap (_ks e 5)) 50))

  (test-case "Accessor _ks - with symbols"
    (define e (el 'a 'b 'c 'd))
    (check-equal? (_ks e 1) 'a)
    (check-equal? (_ks e 2) 'b)
    (check-equal? (_ks e 3) 'c)
    (check-equal? (_ks e 4) 'd))

  (test-case "Accessor _ks - with wrapped integers"
    (define e (el 10 20 30))
    (check-equal? (dp-int-unwrap (_ks e (dp-int-wrap 1 'const))) 10)
    (check-equal? (dp-int-unwrap (_ks e (dp-int-wrap 2 'const))) 20)
    (check-equal? (dp-int-unwrap (_ks e (dp-int-wrap 3 'const))) 30))

  (test-case "Accessor n_s - subscript count"
    (define e1 (el 1))
    (define e2 (el 1 2))
    (define e3 (el 1 2 3))
    (define e4 (el 1 2 3 4))
    (define e5 (el 1 2 3 4 5))
    (check-equal? (dp-int-unwrap (n_s e1)) 1)
    (check-equal? (dp-int-unwrap (n_s e2)) 2)
    (check-equal? (dp-int-unwrap (n_s e3)) 3)
    (check-equal? (dp-int-unwrap (n_s e4)) 4)
    (check-equal? (dp-int-unwrap (n_s e5)) 5))

  (test-case "n_s returns const-sized integer"
    (define e (el 1 2 3))
    (define len (n_s e))
    (check-true (dp-integer? len))
    (check-equal? (dp-int-size-of len) 'const))

  (test-case "Contract el/kc - positive cases"
    (define e1 (el 1))
    (define e2 (el 'a 'b 'c))
    (check-true (el/kc e1 #f #f '() #t))
    (check-true (el/kc e2 #f #f '() #t))
    (check-equal? (el/kc e1 #f #f '() #f) e1))

  (test-case "Contract el/kc - negative cases"
    (check-false (el/kc 123 #f #f '() #t))
    (check-false (el/kc "not an el" #f #f '() #t))
    (check-false (el/kc 'symbol #f #f '() #t))
    (check-false (el/kc '(1 2 3) #f #f '() #t)))

  (test-case "Integer wrapping - raw integers become dp-integers"
    (define e (el 1 2 3))
    (check-true (dp-integer? (_1s e)))
    (check-true (dp-integer? (_2s e)))
    (check-true (dp-integer? (_3s e))))

  (test-case "Integer wrapping - symbols remain symbols"
    (define e (el 'a 'b 'c))
    (check-true (symbol? (_1s e)))
    (check-true (symbol? (_2s e)))
    (check-true (symbol? (_3s e))))

  (test-case "Mixed element types"
    (define e (el 1 'symbol 3))
    (check-true (dp-integer? (_1s e)))
    (check-true (symbol? (_2s e)))
    (check-true (dp-integer? (_3s e)))
    (check-equal? (_2s e) 'symbol))

  (test-case "Element display formatting"
    (define e1 (el 1 2))
    (define e2 (el 'a 'b 'c))
    (define s1 (format "~a" e1))
    (define s2 (format "~a" e2))
    (check-true (string-contains? s1 "1"))
    (check-true (string-contains? s1 "2"))
    (check-true (string-contains? s2 "a"))
    (check-true (string-contains? s2 "b"))
    (check-true (string-contains? s2 "c")))

  (test-case "Equality of elements with same subscripts"
    (define e1 (el 1 2 3))
    (define e2 (el 1 2 3))
    (check-equal? e1 e2))

  (test-case "Inequality of elements with different subscripts"
    (define e1 (el 1 2))
    (define e2 (el 1 3))
    (define e3 (el 1))
    (check-false (equal? e1 e2))
    (check-false (equal? e1 e3)))

  (test-case "Large element with many subscripts"
    (define e (el 1 2 3 4 5 6 7 8 9 10))
    (check-equal? (dp-int-unwrap (n_s e)) 10)
    (check-equal? (dp-int-unwrap (_ks e 1)) 1)
    (check-equal? (dp-int-unwrap (_ks e 10)) 10))

  (test-case "Elements in reduction context - 3SAT to Hamiltonian Cycle pattern"
    (define e-minus (el 1 0 '-))
    (define e-plus (el 1 0 '+))
    (define e-star (el 1 2 '*))
    (check-equal? (dp-int-unwrap (_1s e-minus)) 1)
    (check-equal? (dp-int-unwrap (_2s e-minus)) 0)
    (check-equal? (_3s e-minus) '-)
    (check-equal? (_3s e-plus) '+)
    (check-equal? (_3s e-star) '*))

  (test-case "Elements as vertex labels - single subscript pattern"
    (define v-dollar (el '$))
    (define v-s (el 's))
    (define v-t (el 't))
    (check-equal? (_1s v-dollar) '$)
    (check-equal? (_1s v-s) 's)
    (check-equal? (_1s v-t) 't))
)

;; (require rackunit/text-ui)
;; (run-tests EL)
