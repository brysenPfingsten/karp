#lang racket
(require "../interface.rkt")
(require (rename-in graph [graph? a-graph?]))

(graph->bitmap (add-nodes (create-graph 'test) '(A B C D E-1)))
(define GRAPH1 (add-nodes (create-graph 'test) '(A B C D E-1)))
(define g (unweighted-graph/directed '((a b) (c d))))
(racket-graph->bitmap g)
(graph->str GRAPH1)
