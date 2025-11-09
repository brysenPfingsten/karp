#lang racket

(require "../private/core-structures.rkt"
         "../private/karp-contract.rkt"
         "../private/problem-definition-utility.rkt"
         "../lib/graph.rkt"
         (prefix-in rk: graph)
         rackunit
         mischief/symbol
         racket/stxparam)


(define verts '(x1 x2 x3 x4 x5))
(define V1 (apply a-set verts))
(define E1 (a-set ('x1 . -e- . 'x2)
                    ('x1 . -e- . 'x3)
                    ('x2 . -e- . 'x3)
                    ('x3 . -e- . 'x4)
                    ('x4 . -e- . 'x5)
                    ('x5 . -e- . 'x1)))

(define/contract/kc (test x)
  (->k ([x dp-graph-u/kc]) any/kc)
  x)

(define V2 (set 'x1 'x2 'x3 'x4 'x5))
(define E2 (set ('x1 . -e- . 'x2)
                ('x2 . -e- . 'x3)))
#;(test E1)
;(test (create-graph V1 E1))

(test-case "Conversion from a dp-graph to a racket graph"
  (define GRAPH1 (create-graph V1 E1))
  (define R-GRAPH1 (dp-graph->racket-graph GRAPH1))
  (test-true "Conversion returns a racket graph"
             (rk:graph? R-GRAPH1))
  (test-true "All the vertices are there"
             (set=? (list->set verts)
                    (list->set (rk:get-vertices R-GRAPH1))))
  (test-true "All the edges are there"
             (set=? (list->set (map (λ (e) (sort e symbol<=?))
                                    (map dp-set-members->list (dp-set-members->list E1))))
                    (list->set (map (λ (e) (sort e symbol<=?)) (rk:get-edges R-GRAPH1)))))
  )
