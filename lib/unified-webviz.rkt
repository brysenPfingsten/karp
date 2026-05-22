#lang racket

;; Unified Web Visualization Framework for Karp Reductions
;; Combines graph, mapping, and other visualizers into a single framework
;; with a common UI shell and pluggable renderers.

(require racket/file
         racket/list
         racket/match
         racket/runtime-path
         racket/string
         net/url
         (only-in "../private/core-structures.rkt"
                  dp-set?
                  dp-set-members->list)
         (only-in "../private/problem-definition-utility.rkt"
                  dp-instance?
                  dp-instance-fields)
         (only-in "mapping.rkt"
                  dp-mapping?
                  dp-mapping-H)
         (only-in "../private/primitive-data-type.rkt"
                  dp-integer?
                  dp-integer-val)
         (only-in "../el.rkt"
                  el?
                  _1s _2s _3s n_s)
         (only-in "graph.rkt" e-u e-v dp-graph? vertices-of edges-of)
         (only-in "cnf.rkt"
                  dp-cnf-clause?
                  dp-cnf-clause-lst
                  dp-cnf?
                  dp-cnf-lst
                  dp-literal?
                  dp-literal-x
                  dp-literal-neg?
                  positive-literal?))

(provide write-unified-viz-html
         detect-viz-type
         viz-type?)

(define-runtime-path cytoscape-runtime-path (build-path 'up "vendor" "cytoscape.min.js"))

;; ============================================================================
;; Utility Functions
;; ============================================================================

(define (normalize-int v)
  (cond
    [(dp-integer? v) (dp-integer-val v)]
    [else v]))

(define (set->list s)
  (cond
    [(dp-set? s) (dp-set-members->list s)]
    [(set? s) (set->list s)]
    [(list? s) s]
    [else '()]))

(define (json-escape s)
  (define str (format "~a" s))
  (define replacements
    '(("\\" . "\\\\") ("\"" . "\\\"") ("\n" . "\\n") ("\r" . "\\r") ("\t" . "\\t")))
  (for/fold ([acc str]) ([pair replacements])
    (string-replace acc (car pair) (cdr pair))))

(define (json->string v)
  (cond
    [(hash? v)
     (string-append "{"
       (string-join
         (for/list ([(k val) (in-hash v)])
           (format "~a:~a" (json->string (format "~a" k)) (json->string val)))
         ",")
       "}")]
    [(list? v)
     (string-append "[" (string-join (map json->string v) ",") "]")]
    [(string? v) (format "\"~a\"" (json-escape v))]
    [(boolean? v) (if v "true" "false")]
    [(number? v) (number->string v)]
    [(symbol? v) (json->string (symbol->string v))]
    [(void? v) "null"]
    [else (json->string (format "~a" v))]))

;; ============================================================================
;; Visualization Type Detection
;; ============================================================================

(define (viz-type? v)
  (member v '(graph mapping sat)))

;; Check if vertex is a graph-style el (has layout hints)
(define (graph-vertex? v)
  (and (el? v)
       (let ([arity (normalize-int (n_s v))])
         (and (integer? arity)
              (or (= arity 1) (= arity 2) (= arity 3))
              ;; Graph vertices have numeric indices
              (let ([first-el (_1s v)])
                (or (integer? (normalize-int first-el))
                    (symbol? first-el)))))))

;; Check if vertex is a mapping-style el (el kind name value)
(define (mapping-vertex? v)
  (and (el? v)
       (let ([arity (normalize-int (n_s v))])
         (and (= arity 3)
              ;; Mapping vertices have symbol kind as first element
              (symbol? (_1s v))
              (member (_1s v) '(obj gadget element))))))

;; Check if item is a SAT clause
(define (sat-clause? v)
  (dp-cnf-clause? v))

(define (detect-viz-type steps)
  (cond
    [(null? steps) 'graph]
    [else
     (define first-step (car steps))
     (define vs (if (and (list? first-step) (>= (length first-step) 1))
                    (first first-step)
                    (set)))
     (define vertices (set->list vs))
     (cond
       [(null? vertices) 'graph]
       [(sat-clause? (car vertices)) 'sat]
       [(mapping-vertex? (car vertices)) 'mapping]
       [else 'graph])]))

;; ============================================================================
;; Graph Data Extraction
;; ============================================================================

(define (vertex-id v)
  (format "~a" v))

(define (edge-id u v)
  (format "~a -> ~a" (vertex-id u) (vertex-id v)))

(define (vertex-indices v)
  (define max-i #f)
  (define max-j #f)
  (define arity (and (el? v) (normalize-int (n_s v))))
  (when (and (integer? arity) (>= arity 2))
    (define i (normalize-int (_1s v)))
    (when (integer? i) (set! max-i i)))
  (cond
    [(and (integer? arity) (= arity 3))
     (define j (normalize-int (_2s v)))
     (when (integer? j) (set! max-j j))]
    [(and (integer? arity) (= arity 1))
     (define a (_1s v))
     (when (integer? a) (set! max-j a))])
  (values max-i max-j))

(define (compute-max-indices nodes)
  (define max-i 1)
  (define max-j 1)
  (for ([v (in-hash-values nodes)])
    (define-values (mi mj) (vertex-indices v))
    (when mi (set! max-i (max max-i mi)))
    (when mj (set! max-j (max max-j mj))))
  (values max-i max-j))

(define (node->json v max-i max-j x-step y-step)
  (define label (vertex-id v))
  (define arity (and (el? v) (normalize-int (n_s v))))
  (define (pos x y kind i j tag)
    (hash "id" label "label" label "x" x "y" y "kind" kind "i" i "j" j "tag" tag))
  (cond
    [(and (integer? arity) (= arity 3))
     (define i (normalize-int (_1s v)))
     (define j (normalize-int (_2s v)))
     (define tag (_3s v))
     (define offset
       (cond [(eq? tag '-) 0] [(eq? tag '+) 18] [(eq? tag '*) 36] [else 18]))
     (pos (* x-step j) (+ (* y-step i) offset) "var" i j (format "~a" tag))]
    [(and (integer? arity) (= arity 2))
     (define i (normalize-int (_1s v)))
     (define tag (_2s v))
     (pos (* x-step (+ max-j 1)) (+ (* y-step i) 18) "var-tail" i (add1 max-j) (format "~a" tag))]
    [(and (integer? arity) (= arity 1))
     (define a (_1s v))
     (cond
       [(symbol? a)
        (define is-s (eq? a 's))
        (define x (if is-s (- x-step) (* x-step (+ max-j 2))))
        (define y (+ (* y-step (+ max-i 1)) 18))
        (pos x y "terminal" #f #f (format "~a" a))]
       [else
        (define j (normalize-int a))
        (pos (* x-step j) 18 "clause" #f j #f)])]
    [else (pos 0 0 "other" #f #f #f)]))

(define (bounds nodes)
  (define xs (map (lambda (n) (hash-ref n "x" 0)) nodes))
  (define ys (map (lambda (n) (hash-ref n "y" 0)) nodes))
  (define padding 80)
  (define min-x (if (null? xs) 0 (- (apply min xs) padding)))
  (define max-x (if (null? xs) 100 (+ (apply max xs) padding)))
  (define min-y (if (null? ys) 0 (- (apply min ys) padding)))
  (define max-y (if (null? ys) 100 (+ (apply max ys) padding)))
  (hash "minX" min-x "minY" min-y "width" (- max-x min-x) "height" (- max-y min-y)))

(define (extract-graph-data steps source-inst)
  (define nodes (make-hash))
  (define edges (make-hash))

  (for ([step (in-list steps)])
    (define vs (if (and (list? step) (>= (length step) 1)) (first step) (set)))
    (define es (if (and (list? step) (>= (length step) 2)) (second step) (set)))
    (for ([v (in-list (set->list vs))])
      (hash-set! nodes (vertex-id v) v))
    (for ([e (in-list (set->list es))])
      (define u (e-u e))
      (define v (e-v e))
      (hash-set! edges (edge-id u v) (list u v))))

  (define-values (max-i max-j) (compute-max-indices nodes))
  (define x-step 220)
  (define y-step 90)

  (define node-labels (sort (hash-keys nodes) string<?))
  (define node-id-map
    (for/hash ([lbl (in-list node-labels)] [i (in-naturals 1)])
      (values lbl (format "n~a" i))))
  (define (node-id-of lbl) (hash-ref node-id-map lbl))

  (define nodes-json
    (for/list ([v (in-hash-values nodes)])
      (define lbl (vertex-id v))
      (define base (node->json v max-i max-j x-step y-step))
      (hash-set (hash-set base "id" (node-id-of lbl)) "label" lbl)))

  (define edge-keys (sort (hash-keys edges) string<?))
  (define edge-id-map
    (for/hash ([key (in-list edge-keys)] [i (in-naturals 1)])
      (values key (format "e~a" i))))
  (define (edge-id-of key) (hash-ref edge-id-map key))

  (define edges-json
    (for/list ([(key uv) (in-hash edges)])
      (define u (first uv))
      (define v (second uv))
      (hash "id" (edge-id-of key)
            "source" (node-id-of (vertex-id u))
            "target" (node-id-of (vertex-id v)))))

  (define steps-json
    (for/list ([step (in-list steps)])
      (define vs (if (and (list? step) (>= (length step) 1)) (first step) (set)))
      (define es (if (and (list? step) (>= (length step) 2)) (second step) (set)))
      (hash "addNodes" (for/list ([v (in-list (set->list vs))])
                         (node-id-of (vertex-id v)))
            "addEdges" (for/list ([e (in-list (set->list es))])
                         (edge-id-of (edge-id (e-u e) (e-v e)))))))

  ;; Extract source instance data (CNF for 3SAT)
  (define source-data
    (if (and source-inst (dp-instance? source-inst))
        (let* ([fields (cdr (dp-instance-fields source-inst))]
               [the-cnf #f]
               [extras '()]
               [scalar-count 0])
          (for ([field fields] [i (in-naturals)])
            (cond
              [(and (dp-cnf? field) (not the-cnf))
               (set! the-cnf field)]
              [(dp-integer? field)
               (set! scalar-count (add1 scalar-count))
               (define name (if (= scalar-count 1) "K" (format "K~a" scalar-count)))
               (set! extras (cons (hash "name" name "value" (normalize-int field)) extras))]
              [(number? field)
               (set! scalar-count (add1 scalar-count))
               (define name (if (= scalar-count 1) "K" (format "K~a" scalar-count)))
               (set! extras (cons (hash "name" name "value" field) extras))]))
          (if the-cnf
              (hash "type" "cnf"
                    "clauses" (for/list ([clause (in-list (dp-cnf-lst the-cnf))])
                                (for/list ([lit (in-list (dp-cnf-clause-lst clause))])
                                  (hash "var" (format "~a" (dp-literal-x lit))
                                        "positive" (positive-literal? lit))))
                    "extras" (reverse extras))
              #f))
        #f))

  (hash "nodes" nodes-json
        "edges" edges-json
        "steps" steps-json
        "viewBox" (bounds nodes-json)
        "sourceInstance" source-data))

;; ============================================================================
;; Mapping Data Extraction
;; ============================================================================

(define (el->info v)
  (list (format "~a" (_1s v))    ; kind
        (format "~a" (_2s v))    ; name
        (normalize-int (_3s v)))) ; value

(define (extract-mapping-data steps source-inst)
  (define all-objects (make-hash))
  (define step-data '())

  (for ([step (in-list steps)] [i (in-naturals)])
    (define vs (if (and (list? step) (>= (length step) 1)) (first step) (set)))
    (define label (and (list? step) (= (length step) 3) (third step)))
    (define step-objects '())

    (for ([v (in-list (set->list vs))])
      (when (mapping-vertex? v)
        (match-define (list kind name value) (el->info v))
        (define obj-data (hash "kind" kind "name" name "value" value))
        (hash-set! all-objects name obj-data)
        (set! step-objects (cons name step-objects))))

    (set! step-data
          (append step-data
                  (list (hash "objects" (reverse step-objects)
                              "label" (or label ""))))))

  ;; Extract source instance data
  (define source-data
    (if (and source-inst (dp-instance? source-inst))
        (let* ([fields (cdr (dp-instance-fields source-inst))]
               [the-set #f]
               [the-mapping #f]
               [extras '()]
               [scalar-count 0])
          (for ([field fields] [i (in-naturals)])
            (cond
              [(and (dp-set? field) (not the-set))
               (set! the-set field)]
              [(and (dp-mapping? field) (not the-mapping))
               (set! the-mapping field)]
              [(dp-integer? field)
               (set! scalar-count (add1 scalar-count))
               (define name (if (= scalar-count 1) "K" (format "K~a" scalar-count)))
               (set! extras (cons (hash "name" name "value" (normalize-int field)) extras))]
              [(number? field)
               (set! scalar-count (add1 scalar-count))
               (define name (if (= scalar-count 1) "K" (format "K~a" scalar-count)))
               (set! extras (cons (hash "name" name "value" field) extras))]))
          (if (and the-set the-mapping)
              (hash "objects"
                    (for/list ([obj (in-list (set->list the-set))])
                      (hash "name" (format "~a" obj)
                            "value" (normalize-int
                                     (hash-ref (dp-mapping-H the-mapping) obj #f))))
                    "extras" (reverse extras))
              #f))
        #f))

  (hash "objects" (hash-values all-objects)
        "steps" step-data
        "sourceInstance" source-data))

;; ============================================================================
;; SAT Data Extraction
;; ============================================================================

(define (clause->json clause)
  (define literals (dp-cnf-clause-lst clause))
  (hash "literals"
        (for/list ([lit (in-list literals)])
          (hash "var" (format "~a" (dp-literal-x lit))
                "positive" (positive-literal? lit)))))

(define (extract-sat-data steps source-inst)
  (define all-clauses '())
  (define all-variables (mutable-set))
  (define step-data '())

  (for ([step (in-list steps)] [i (in-naturals)])
    (define vs (if (and (list? step) (>= (length step) 1)) (first step) (set)))
    (define label (and (list? step) (= (length step) 3) (third step)))
    (define step-clauses '())

    (for ([v (in-list (set->list vs))])
      (when (dp-cnf-clause? v)
        (define clause-json (clause->json v))
        (set! all-clauses (cons clause-json all-clauses))
        (set! step-clauses (cons (length all-clauses) step-clauses))
        ;; Collect variables
        (for ([lit (in-list (dp-cnf-clause-lst v))])
          (set-add! all-variables (format "~a" (dp-literal-x lit))))))

    (set! step-data
          (append step-data
                  (list (hash "clauseIndices" (reverse step-clauses)
                              "label" (or label ""))))))

  ;; Extract source instance data (graph for vertex cover)
  (define source-data
    (if (and source-inst (dp-instance? source-inst))
        (let* ([fields (cdr (dp-instance-fields source-inst))]
               [the-graph #f]
               [extras '()]
               [scalar-count 0])
          (for ([field fields] [i (in-naturals)])
            (cond
              [(and (dp-graph? field) (not the-graph))
               (set! the-graph field)]
              [(dp-integer? field)
               (set! scalar-count (add1 scalar-count))
               (define name (if (= scalar-count 1) "K" (format "K~a" scalar-count)))
               (set! extras (cons (hash "name" name "value" (normalize-int field)) extras))]
              [(number? field)
               (set! scalar-count (add1 scalar-count))
               (define name (if (= scalar-count 1) "K" (format "K~a" scalar-count)))
               (set! extras (cons (hash "name" name "value" field) extras))]))
          (if the-graph
              (hash "type" "graph"
                    "vertices" (for/list ([v (in-list (set->list (vertices-of the-graph)))])
                                 (format "~a" v))
                    "edges" (for/list ([e (in-list (set->list (edges-of the-graph)))])
                              (hash "u" (format "~a" (e-u e))
                                    "v" (format "~a" (e-v e))))
                    "extras" (reverse extras))
              #f))
        #f))

  (hash "clauses" (reverse all-clauses)
        "variables" (set->list all-variables)
        "steps" step-data
        "sourceInstance" source-data))

;; ============================================================================
;; Step Labels Extraction
;; ============================================================================

(define (extract-step-labels steps)
  (for/list ([step (in-list steps)])
    (and (list? step)
         (= (length step) 3)
         (let ([label (list-ref step 2)])
           (and label (format "~a" label))))))

;; ============================================================================
;; Cytoscape JS Loading
;; ============================================================================

(define (cytoscape-js-content)
  (if (file-exists? cytoscape-runtime-path)
      (file->string cytoscape-runtime-path)
      ""))

;; ============================================================================
;; Layout DSL Processing
;; ============================================================================

;; Convert layout DSL S-expression to JSON-compatible hash
(define (layout->json layout-sexp)
  (if (not layout-sexp)
      #f
      (parse-layout-node layout-sexp)))

;; Parse a node in the layout tree
(define (parse-layout-node node)
  (match node
    ;; Top-level layout container
    [`(layout ,children ...)
     (hash "type" "layout"
           "children" (map parse-layout-node children))]

    ;; Variables iterator
    [`(variables ,opts ...)
     (parse-iterator "variables" opts)]

    ;; Clauses iterator
    [`(clauses ,opts ...)
     (parse-iterator "clauses" opts)]

    ;; Boundary section
    [`(boundary ,opts ...)
     (parse-iterator "boundary" opts)]

    ;; Row container
    [`(row ,opts ...)
     (parse-container "row" opts)]

    ;; Place node (vertex placement)
    [`(place ,name ,opts ...)
     (parse-place name opts)]

    ;; Fallback
    [else (hash "type" "unknown" "raw" (format "~a" node))]))

;; Parse iterator (variables, clauses, boundary)
(define (parse-iterator type opts)
  (define index-var #f)
  (define direction #f)
  (define position #f)
  (define children '())

  (let loop ([remaining opts])
    (match remaining
      ['() (void)]
      [`(#:index ,v . ,rest)
       (set! index-var (format "~a" v))
       (loop rest)]
      [`(#:direction ,d . ,rest)
       (set! direction (normalize-quoted-symbol d))
       (loop rest)]
      [`(#:position ,p . ,rest)
       (set! position (normalize-quoted-symbol p))
       (loop rest)]
      [`(,child . ,rest)
       (set! children (append children (list (parse-layout-node child))))
       (loop rest)]))

  (hash "type" type
        "index" index-var
        "direction" direction
        "position" position
        "children" children))

;; Handle quoted symbols like 'down -> "down"
(define (normalize-quoted-symbol v)
  (match v
    [`(quote ,sym) (format "~a" sym)]
    [else (format "~a" v)]))

;; Parse container (row)
(define (parse-container type opts)
  (define direction #f)
  (define children '())

  (let loop ([remaining opts])
    (match remaining
      ['() (void)]
      [`(#:direction ,d . ,rest)
       (set! direction (normalize-quoted-symbol d))
       (loop rest)]
      [`(,child . ,rest)
       (set! children (append children (list (parse-layout-node child))))
       (loop rest)]))

  (hash "type" type
        "direction" direction
        "children" children))

;; Parse place node
(define (parse-place name opts)
  (define match-pattern #f)
  (define role #f)
  (define shape #f)
  (define color #f)

  (let loop ([remaining opts])
    (match remaining
      ['() (void)]
      [`(#:match ,pat . ,rest)
       (set! match-pattern (parse-match-pattern pat))
       (loop rest)]
      [`(#:role ,r . ,rest)
       (set! role (normalize-quoted-symbol r))
       (loop rest)]
      [`(#:shape ,s . ,rest)
       (set! shape (normalize-quoted-symbol s))
       (loop rest)]
      [`(#:color ,c . ,rest)
       (set! color (normalize-quoted-symbol c))
       (loop rest)]
      [`(,_ . ,rest)
       (loop rest)]))

  (hash "type" "place"
        "name" (format "~a" name)
        "match" match-pattern
        "role" role
        "shape" shape
        "color" color))

;; Parse match pattern like (el i j '+)
(define (parse-match-pattern pat)
  (match pat
    [`(el ,args ...)
     (hash "type" "el"
           "args" (map normalize-pattern-arg args))]
    [else (hash "type" "literal" "value" (format "~a" pat))]))

;; Normalize a pattern argument (handle quoted symbols, etc.)
(define (normalize-pattern-arg arg)
  (match arg
    [`(quote ,sym) (format "~a" sym)]  ; 'sym becomes sym
    [(? symbol? s) (format "~a" s)]
    [(? number? n) (format "~a" n)]
    [else (format "~a" arg)]))

;; ============================================================================
;; HTML Generation
;; ============================================================================

(define (write-unified-viz-html steps output-path
                                 #:title [title "Karp Reduction Visualization"]
                                 #:source-instance [source-inst #f]
                                 #:viz-type [explicit-viz-type #f]
                                 #:layout [layout #f])

  (define viz-type (or explicit-viz-type (detect-viz-type steps)))
  (define step-labels (extract-step-labels steps))
  (define layout-json (layout->json layout))

  ;; Build unified data structure
  (define data
    (hash "vizType" (symbol->string viz-type)
          "title" title
          "stepLabels" step-labels
          "stepCount" (length steps)
          "layout" layout-json
          ;; Type-specific data
          "graph" (if (eq? viz-type 'graph) (extract-graph-data steps source-inst) #f)
          "mapping" (if (eq? viz-type 'mapping) (extract-mapping-data steps source-inst) #f)
          "sat" (if (eq? viz-type 'sat) (extract-sat-data steps source-inst) #f)))

  (define json-data (json->string data))
  (define cytoscape-src (cytoscape-js-content))

  (define html (generate-unified-html json-data cytoscape-src title))

  (call-with-output-file output-path
    (lambda (out) (display html out))
    #:exists 'truncate)
  output-path)

(define (generate-unified-html json-data cytoscape-src title)
  (string-append
#<<HTML
<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>
HTML
title
#<<HTML
</title>
<style>
:root {
  --bg: #ffffff;
  --panel-bg: #fff;
  --border: #cccccc;
  --ink: #1b1b1b;
  --accent: #666666;
  --highlight: #f0f0f0;
}
* { box-sizing: border-box; }
body {
  margin: 0;
  font-family: 'Segoe UI', system-ui, sans-serif;
  background: var(--bg);
  color: var(--ink);
  height: 100vh;
  display: flex;
  flex-direction: column;
}
header {
  padding: 12px 20px;
  background: #f5f5f5;
  border-bottom: 2px solid #222;
}
header h1 { margin: 0; font-size: 18px; font-weight: 600; }
.toolbar {
  display: flex;
  align-items: center;
  gap: 16px;
  padding: 10px 20px;
  background: #f0f0f0;
  border-bottom: 1px solid var(--border);
}
.controls { display: flex; gap: 8px; align-items: center; }
.controls button {
  padding: 6px 12px;
  border: 1px solid #333;
  background: #fff;
  cursor: pointer;
  font-size: 13px;
}
.controls button:hover { background: #f0f0f0; }
.controls input[type=range] { width: 200px; }
.step-label {
  flex: 1;
  text-align: center;
  font-weight: 600;
  color: #444;
}
.stats { font-size: 13px; color: #666; }
.content {
  flex: 1;
  display: flex;
  overflow: hidden;
  min-height: 0;  /* Required for flex children to shrink properly */
}

/* Graph-specific styles */
#graph-container {
  flex: 1;
  display: none;
  flex-direction: row;
  min-height: 0;
}
#graphSourcePanel {
  width: 280px;
  margin: 10px;
  overflow: auto;
  flex-shrink: 0;
}
#cy-wrapper {
  flex: 1;
  position: relative;
  min-height: 0;
}
#cy {
  position: absolute;
  top: 0;
  right: 0;
  bottom: 0;
  left: 0;
  background: var(--panel-bg);
}

/* Mapping-specific styles */
#mapping-container {
  flex: 1;
  display: none;
  padding: 20px;
  overflow: auto;
}
.mapping-content {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 20px;
  align-items: start;
}
.panel {
  background: var(--panel-bg);
  border: 1px solid var(--border);
  border-radius: 6px;
  padding: 16px;
}
.panel h2 {
  margin: 0 0 12px 0;
  font-size: 14px;
  font-weight: 600;
  color: #666;
  text-transform: uppercase;
  letter-spacing: 0.5px;
}
table {
  width: 100%;
  border-collapse: collapse;
  font-size: 14px;
}
th, td {
  padding: 8px 12px;
  text-align: left;
  border-bottom: 1px solid #eee;
}
th {
  background: #f8f8f8;
  font-weight: 600;
  color: #555;
}
tr.new td { background: #e0e0e0; }
tr.gadget td { background: #d0d0d0; }
tr.hidden { opacity: 0.25; }
tr.highlight td { background: #b3d9ff !important; }
tr[data-name] { cursor: pointer; }
.edge { cursor: pointer; }
.edge.highlight { background: #b3d9ff !important; }
.clause.highlight { background: #b3d9ff !important; border-color: #3498db; }
.cnf-display .clause-row { cursor: pointer; padding: 6px 8px; margin: 2px 0; border-radius: 4px; }
.cnf-display .clause-row.highlight { background: #b3d9ff; }
.extras {
  margin-top: 16px;
  padding-top: 12px;
  border-top: 1px dashed #ccc;
}
.extra-row {
  display: flex;
  justify-content: space-between;
  padding: 4px 0;
  font-size: 13px;
}
.extra-name { font-weight: 600; color: #666; }
.extra-value { font-family: monospace; }
.legend {
  display: flex;
  gap: 20px;
  margin-top: 16px;
  padding-top: 12px;
  border-top: 1px dashed #ccc;
  font-size: 12px;
}
.legend-item { display: flex; align-items: center; gap: 6px; }
.legend-color { width: 14px; height: 14px; border-radius: 2px; }
.legend-color.new { background: #e0e0e0; border: 1px solid #999999; }
.legend-color.gadget { background: #d0d0d0; border: 1px solid #888888; }

/* SAT-specific styles */
#sat-container {
  flex: 1;
  display: none;
  padding: 20px;
  overflow: auto;
}
.sat-content {
  display: grid;
  grid-template-columns: 1fr 1fr;
  gap: 20px;
  align-items: start;
}
.clause {
  background: #f8f8f8;
  border: 1px solid #ddd;
  border-radius: 4px;
  padding: 8px 12px;
  margin: 4px 0;
  font-family: monospace;
  display: flex;
  align-items: center;
  gap: 8px;
}
.clause.hidden { opacity: 0.25; }
.literal { padding: 2px 6px; border-radius: 3px; }
.literal.positive { background: #e0e0e0; color: #333333; }
.literal.negative { background: #d0d0d0; color: #000000; }
.or-symbol { color: #999; font-size: 12px; }
.source-graph {
  margin-bottom: 16px;
}
.source-graph .edge {
  font-family: monospace;
  padding: 2px 8px;
  background: #f0f0f0;
  border-radius: 3px;
  margin: 2px;
  display: inline-block;
}
.cnf-display .clause-row {
  font-family: monospace;
  padding: 4px 0;
}
.cnf-display .literal {
  padding: 2px 6px;
  border-radius: 3px;
  margin: 0 2px;
}
</style>
<script>
HTML
cytoscape-src
#<<HTML
</script>
</head>
<body>
<header><h1 id="title"></h1></header>
<div class="toolbar">
  <div class="controls">
    <button id="prev">Prev</button>
    <button id="next">Next</button>
    <input type="range" id="slider" min="0" value="0">
  </div>
  <div class="step-label" id="stepLabel"></div>
  <div class="stats" id="stats"></div>
</div>
<div class="content">
  <div id="graph-container">
    <div class="panel" id="graphSourcePanel" style="display: none;">
      <h2>Source Instance</h2>
      <div id="graphSourceContent"></div>
    </div>
    <div id="cy-wrapper">
      <div id="cy"></div>
    </div>
  </div>
  <div id="mapping-container">
    <div class="mapping-content">
      <div class="panel" id="sourcePanel">
        <h2>Source Instance</h2>
        <div id="sourceContent"></div>
      </div>
      <div class="panel" id="targetPanel">
        <h2>Target Instance</h2>
        <div id="targetContent"></div>
      </div>
    </div>
  </div>
  <div id="sat-container">
    <div class="sat-content">
      <div class="panel" id="satSourcePanel">
        <h2>Source Instance</h2>
        <div id="satSourceContent"></div>
      </div>
      <div class="panel" id="satTargetPanel">
        <h2>Target Instance (CNF)</h2>
        <div id="satTargetContent"></div>
      </div>
    </div>
  </div>
</div>
<script>
const data =
HTML
json-data
#<<HTML
;

document.getElementById('title').textContent = data.title;

const slider = document.getElementById('slider');
slider.max = data.stepCount;
let stepIndex = 0;

// ============================================================================
// Layout-aware Label Generation
// ============================================================================

// Parse an el-style label like "(el 1ₚ 2ₚ '+)" into components
function parseElLabel(label) {
  // Match patterns like (el X) or (el X Y) or (el X Y Z)
  // Handle subscript numbers like 1ₚ, 2ₚ
  const cleaned = label.replace(/[()]/g, '').trim();
  const parts = cleaned.split(/\s+/);

  if (parts[0] !== 'el') return null;

  const args = parts.slice(1).map(p => {
    // Remove subscript markers and quotes
    return p.replace(/ₚ/g, '').replace(/'/g, '');
  });

  return { type: 'el', args };
}

// Generate a compact label from parsed el components
function formatCompactLabel(parsed) {
  if (!parsed || parsed.type !== 'el') return null;

  const args = parsed.args;
  if (args.length === 1) {
    // Single arg: terminal (s, t) or clause index
    const val = args[0];
    if (val === 's' || val === 't') return val;
    return `C${val}`;
  } else if (args.length === 2) {
    // Two args: (i, tag) like (1, ^)
    const [i, tag] = args;
    if (tag === '^') return `${i}^`;
    return `${i},${tag}`;
  } else if (args.length === 3) {
    // Three args: (i, j, tag) like (1, 2, +)
    const [i, j, tag] = args;
    return `${i},${j}${tag}`;
  }
  return null;
}

// Get a layout-aware label for a node
function getLayoutLabel(originalLabel, layout) {
  // Try to parse as el expression
  const parsed = parseElLabel(originalLabel);
  if (parsed) {
    const compact = formatCompactLabel(parsed);
    if (compact) return compact;
  }

  // Fallback: return original but cleaned up
  return originalLabel
    .replace(/^\(el\s+/, '')
    .replace(/\)$/, '')
    .replace(/ₚ/g, '')
    .replace(/'/g, '');
}

// Find layout config for a node (shape, color, role)
// nodeData has: i, j, tag, kind, label
function getNodeLayoutConfig(nodeData, layout) {
  if (!layout) return null;

  // Build args array from node data based on kind
  const i = nodeData.i;
  const j = nodeData.j;
  const tag = nodeData.tag;
  const kind = nodeData.kind;

  let args = [];

  // Build args based on node kind to match layout patterns:
  // - var nodes: (el i j tag) -> [i, j, tag]
  // - var-tail nodes: (el i '^) -> [i, tag]
  // - terminal nodes: (el 's) or (el 't) -> [tag]
  // - clause nodes: (el j) -> [j]

  if (kind === 'terminal' && tag) {
    args = [tag];
  } else if (kind === 'clause' && j !== null && j !== undefined && j !== false) {
    args = [String(j)];
  } else if (kind === 'var-tail' && i !== null && i !== undefined && tag && tag !== 'false') {
    // V^ nodes have pattern (el i '^) - don't include j
    args = [String(i), tag];
  } else if (kind === 'var') {
    // Regular variable nodes: (el i j tag)
    if (i !== null && i !== undefined && i !== false) {
      args.push(String(i));
    }
    if (j !== null && j !== undefined && j !== false) {
      args.push(String(j));
    }
    if (tag && tag !== 'false') {
      args.push(tag);
    }
  } else {
    // Fallback: include all available fields
    if (i !== null && i !== undefined && i !== false) {
      args.push(String(i));
    }
    if (j !== null && j !== undefined && j !== false) {
      args.push(String(j));
    }
    if (tag && tag !== 'false') {
      args.push(tag);
    }
  }

  if (args.length === 0) return null;

  const parsed = { type: 'el', args };

  // Search layout tree for matching place
  function findPlace(node) {
    if (!node) return null;
    if (node.type === 'place' && node.match) {
      // Check if this place matches our node
      if (matchesPattern(parsed, node.match)) {
        return {
          role: node.role,
          shape: node.shape,
          color: node.color
        };
      }
    }
    if (node.children) {
      for (const child of node.children) {
        const found = findPlace(child);
        if (found) return found;
      }
    }
    return null;
  }

  return findPlace(layout);
}

// Check if a parsed el matches a layout pattern
function matchesPattern(parsed, pattern) {
  if (pattern.type !== 'el') return false;
  if (parsed.args.length !== pattern.args.length) return false;

  // Check each argument - variables (i, j) match any numeric value, literals must match exactly
  for (let k = 0; k < parsed.args.length; k++) {
    const pArg = pattern.args[k];
    const nArg = parsed.args[k];

    // Variable names like 'i', 'j' match any numeric value (not strings like 's', 't', '^')
    if (pArg === 'i' || pArg === 'j') {
      // Only match if nArg is a numeric string
      if (!/^\d+$/.test(nArg)) return false;
      continue;
    }

    // Otherwise must match exactly
    if (pArg !== nArg) return false;
  }

  return true;
}

// ============================================================================
// Graph Renderer
// ============================================================================
let cy = null;
const nodeVisibility = {};
const edgeVisibility = {};

function initGraphRenderer() {
  if (!data.graph || typeof cytoscape === 'undefined') return;

  document.getElementById('graph-container').style.display = 'flex';

  // Render source instance (CNF) if available
  if (data.graph.sourceInstance) {
    const panel = document.getElementById('graphSourcePanel');
    const container = document.getElementById('graphSourceContent');
    panel.style.display = 'block';

    let html = '';
    if (data.graph.sourceInstance.type === 'cnf') {
      html += '<div class="cnf-display">';
      data.graph.sourceInstance.clauses.forEach((clause, i) => {
        const vars = clause.map(lit => lit.var).join(',');
        html += `<div class="clause-row" data-clause-idx="${i + 1}" data-vars="${vars}">(`;
        html += clause.map(lit => {
          const cls = lit.positive ? 'positive' : 'negative';
          const prefix = lit.positive ? '' : '¬';
          return `<span class="literal ${cls}" data-var="${lit.var}">${prefix}${lit.var}</span>`;
        }).join(' <span class="or-symbol">∨</span> ');
        html += ')</div>';
      });
      html += '</div>';
    }

    if (data.graph.sourceInstance.extras && data.graph.sourceInstance.extras.length > 0) {
      html += '<div class="extras">';
      for (const extra of data.graph.sourceInstance.extras) {
        html += `<div class="extra-row"><span class="extra-name">${extra.name}:</span><span class="extra-value">${extra.value}</span></div>`;
      }
      html += '</div>';
    }

    container.innerHTML = html;

    // Add hover handlers for CNF-to-graph correspondence
    container.querySelectorAll('.clause-row[data-clause-idx]').forEach(clauseRow => {
      clauseRow.addEventListener('mouseenter', () => highlightGraphFromCnf(clauseRow, true));
      clauseRow.addEventListener('mouseleave', () => highlightGraphFromCnf(clauseRow, false));
    });
  }

  const elements = [];
  data.graph.nodes.forEach(n => {
    // Use layout-aware labeling
    const displayLabel = data.layout ? getLayoutLabel(n.label, data.layout) : n.label;
    const layoutConfig = data.layout ? getNodeLayoutConfig(n, data.layout) : null;

    elements.push({
      data: {
        id: n.id,
        label: displayLabel,
        originalLabel: n.label,
        kind: n.kind,
        tag: n.tag,
        // Layout-specified styling
        nodeShape: layoutConfig?.shape || null,
        nodeColor: layoutConfig?.color || null
      },
      position: { x: n.x, y: n.y }
    });
    nodeVisibility[n.id] = false;
  });
  data.graph.edges.forEach(e => {
    elements.push({
      data: { id: e.id, source: e.source, target: e.target }
    });
    edgeVisibility[e.id] = false;
  });

  // Build styles - shape and color come from layout config
  const styles = [
    {
      selector: 'node',
      style: {
        'label': 'data(label)',
        'text-valign': 'center',
        'text-halign': 'center',
        'background-color': '#ffffff',
        'color': '#000',
        'font-size': '10px',
        'width': 28,
        'height': 28,
        'border-color': '#000000',
        'border-width': 2
      }
    },
    // Fallback styles for nodes without layout config
    {
      selector: 'node[kind="clause"]',
      style: { 'background-color': '#888888', 'shape': 'rectangle', 'width': 36, 'height': 24, 'border-width': 2 }
    },
    {
      selector: 'node[kind="terminal"]',
      style: { 'background-color': '#333333', 'color': '#ffffff', 'shape': 'diamond', 'width': 32, 'height': 32, 'border-width': 2 }
    },
    {
      selector: 'edge',
      style: {
        'width': 2,
        'line-color': '#333333',
        'target-arrow-color': '#333333',
        'target-arrow-shape': 'triangle',
        'curve-style': 'bezier'
      }
    },
    {
      selector: '.hidden',
      style: { 'opacity': 0 }
    }
  ];

  // Add layout-specified styles dynamically
  // Cytoscape supports: ellipse, triangle, rectangle, diamond, pentagon, hexagon, etc.
  const shapeMap = {
    'ellipse': 'ellipse',
    'circle': 'ellipse',
    'triangle': 'triangle',
    'rectangle': 'rectangle',
    'rect': 'rectangle',
    'diamond': 'diamond',
    'pentagon': 'pentagon',
    'hexagon': 'hexagon',
    'star': 'star',
    'vee': 'vee'
  };

  // Named color palette
  const colorPalette = {
    // Primary colors
    'red': '#e74c3c',
    'blue': '#3498db',
    'green': '#2ecc71',
    'yellow': '#f1c40f',
    'orange': '#e67e22',
    'purple': '#9b59b6',
    'pink': '#e91e63',
    'cyan': '#00bcd4',
    'teal': '#1abc9c',

    // Darker variants
    'dark-red': '#c0392b',
    'dark-blue': '#2980b9',
    'dark-green': '#27ae60',
    'dark-orange': '#d35400',
    'dark-purple': '#8e44ad',
    'dark-teal': '#16a085',

    // Lighter variants
    'light-red': '#ff6b6b',
    'light-blue': '#74b9ff',
    'light-green': '#55efc4',
    'light-orange': '#ffeaa7',
    'light-purple': '#a29bfe',
    'light-pink': '#fd79a8',

    // Neutrals
    'gray': '#95a5a6',
    'dark-gray': '#7f8c8d',
    'light-gray': '#bdc3c7',
    'black': '#2c3e50',
    'white': '#ecf0f1',

    // Semantic colors
    'positive': '#3498db',
    'negative': '#e67e22',
    'entry': '#2ecc71',
    'exit': '#9b59b6',
    'terminal': '#e74c3c',
    'clause': '#f39c12'
  };

  // Resolve color - check palette first, otherwise use as-is (hex, rgb, etc.)
  function resolveColor(color) {
    if (!color) return null;
    return colorPalette[color] || color;
  }

  // Collect unique shape/color combinations and create selectors
  const seenConfigs = new Set();
  elements.filter(e => e.data && (e.data.nodeShape || e.data.nodeColor)).forEach(e => {
    const shape = e.data.nodeShape;
    const color = e.data.nodeColor;
    if (shape || color) {
      const key = `${shape || 'default'}:${color || 'default'}`;
      if (!seenConfigs.has(key)) {
        seenConfigs.add(key);
        const selector = [];
        if (shape) selector.push(`nodeShape="${shape}"`);
        if (color) selector.push(`nodeColor="${color}"`);
        const style = {};
        if (shape && shapeMap[shape]) style['shape'] = shapeMap[shape];
        if (color) style['background-color'] = resolveColor(color);
        if (Object.keys(style).length > 0) {
          styles.push({
            selector: `node[${selector.join('][')}]`,
            style: style
          });
        }
      }
    }
  });

  cy = cytoscape({
    container: document.getElementById('cy'),
    elements: elements,
    style: styles,
    layout: { name: 'preset' },
    userZoomingEnabled: true,
    userPanningEnabled: true,
    boxSelectionEnabled: false
  });

  // Start with all hidden
  cy.elements().addClass('hidden');

  const vb = data.graph.viewBox;
  cy.fit({ eles: cy.elements(), padding: 40 });
}

function updateGraphStep() {
  if (!cy || !data.graph) return;

  // Reset visibility
  Object.keys(nodeVisibility).forEach(k => nodeVisibility[k] = false);
  Object.keys(edgeVisibility).forEach(k => edgeVisibility[k] = false);

  // Apply steps up to current
  for (let i = 0; i < stepIndex; i++) {
    const step = data.graph.steps[i];
    if (step.addNodes) step.addNodes.forEach(id => nodeVisibility[id] = true);
    if (step.addEdges) step.addEdges.forEach(id => edgeVisibility[id] = true);
  }

  // Update visibility classes
  cy.nodes().forEach(node => {
    if (nodeVisibility[node.id()]) {
      node.removeClass('hidden');
    } else {
      node.addClass('hidden');
    }
  });
  cy.edges().forEach(edge => {
    if (edgeVisibility[edge.id()]) {
      edge.removeClass('hidden');
    } else {
      edge.addClass('hidden');
    }
  });
}

function highlightGraphFromCnf(clauseRow, highlight) {
  if (!cy) return;

  const clauseIdx = clauseRow.dataset.clauseIdx;
  const vars = clauseRow.dataset.vars ? clauseRow.dataset.vars.split(',') : [];

  // Highlight/unhighlight the clause row
  if (highlight) {
    clauseRow.classList.add('highlight');
  } else {
    clauseRow.classList.remove('highlight');
  }

  // Highlight clause selector nodes (nodes where the label contains the clause index)
  cy.nodes().forEach(node => {
    const label = node.data('originalLabel') || node.data('label') || '';
    const kind = node.data('kind');

    // Check if this is a clause node with matching index
    // Clause nodes typically have labels like "(el 1)" for clause 1
    if (kind === 'clause') {
      const match = label.match(/el\s+(\d+)/);
      if (match && match[1] === clauseIdx) {
        if (highlight) {
          node.style('border-width', 4);
          node.style('border-color', '#3498db');
        } else {
          node.style('border-width', 2);
          node.style('border-color', '#000000');
        }
      }
    }
  });
}

// ============================================================================
// Mapping Renderer
// ============================================================================
const sourceNames = new Set();

function initMappingRenderer() {
  if (!data.mapping) return;

  document.getElementById('mapping-container').style.display = 'block';

  // Build source names set
  if (data.mapping.sourceInstance && data.mapping.sourceInstance.objects) {
    data.mapping.sourceInstance.objects.forEach(o => sourceNames.add(o.name));
  }

  renderMappingSource();
}

function renderMappingSource() {
  const container = document.getElementById('sourceContent');
  if (!data.mapping.sourceInstance) {
    document.getElementById('sourcePanel').style.display = 'none';
    return;
  }

  let html = '<table><thead><tr><th>Object</th><th>Value</th></tr></thead><tbody>';
  for (const obj of data.mapping.sourceInstance.objects) {
    html += `<tr data-name="${obj.name}" data-panel="source"><td>${obj.name}</td><td>${obj.value}</td></tr>`;
  }
  html += '</tbody></table>';

  if (data.mapping.sourceInstance.extras && data.mapping.sourceInstance.extras.length > 0) {
    html += '<div class="extras">';
    for (const extra of data.mapping.sourceInstance.extras) {
      html += `<div class="extra-row"><span class="extra-name">${extra.name}:</span><span class="extra-value">${extra.value}</span></div>`;
    }
    html += '</div>';
  }

  container.innerHTML = html;

  // Add hover handlers for correspondence
  container.querySelectorAll('tr[data-name]').forEach(row => {
    row.addEventListener('mouseenter', () => highlightCorrespondingMapping(row.dataset.name, true));
    row.addEventListener('mouseleave', () => highlightCorrespondingMapping(row.dataset.name, false));
  });
}

function highlightCorrespondingMapping(name, highlight) {
  // Highlight all rows with this name in both source and target
  document.querySelectorAll(`tr[data-name="${name}"]`).forEach(row => {
    if (highlight) {
      row.classList.add('highlight');
    } else {
      row.classList.remove('highlight');
    }
  });
}

function updateMappingStep() {
  if (!data.mapping) return;

  const container = document.getElementById('targetContent');

  // Collect visible objects up to current step
  const visible = new Set();
  for (let i = 0; i < stepIndex; i++) {
    data.mapping.steps[i].objects.forEach(name => visible.add(name));
  }

  let html = '<table><thead><tr><th>Object</th><th>Value</th></tr></thead><tbody>';

  // Sort objects: source objects first, then gadgets
  const sortedObjects = [...data.mapping.objects].sort((a, b) => {
    const aIsSource = sourceNames.has(a.name);
    const bIsSource = sourceNames.has(b.name);
    if (aIsSource && !bIsSource) return -1;
    if (!aIsSource && bIsSource) return 1;
    return a.name.localeCompare(b.name);
  });

  for (const obj of sortedObjects) {
    const isVisible = visible.has(obj.name);
    const isGadget = obj.kind === 'gadget';
    const isNew = !sourceNames.has(obj.name);
    let rowClass = isVisible ? '' : 'hidden';
    if (isVisible && isGadget) rowClass = 'gadget';
    else if (isVisible && isNew) rowClass = 'new';

    const valueDisplay = isVisible ? obj.value : '&mdash;';
    html += `<tr class="${rowClass}" data-name="${obj.name}" data-panel="target"><td>${obj.name}</td><td>${valueDisplay}</td></tr>`;
  }
  html += '</tbody></table>';

  html += `
    <div class="legend">
      <div class="legend-item"><div class="legend-color"></div> From source</div>
      <div class="legend-item"><div class="legend-color new"></div> New element</div>
      <div class="legend-item"><div class="legend-color gadget"></div> Gadget</div>
    </div>
  `;

  container.innerHTML = html;

  // Add hover handlers for correspondence
  container.querySelectorAll('tr[data-name]').forEach(row => {
    row.addEventListener('mouseenter', () => highlightCorrespondingMapping(row.dataset.name, true));
    row.addEventListener('mouseleave', () => highlightCorrespondingMapping(row.dataset.name, false));
  });
}

// ============================================================================
// SAT Renderer
// ============================================================================
function initSatRenderer() {
  if (!data.sat) return;

  document.getElementById('sat-container').style.display = 'block';
  renderSatSource();
}

function renderSatSource() {
  const container = document.getElementById('satSourceContent');
  if (!data.sat.sourceInstance) {
    document.getElementById('satSourcePanel').style.display = 'none';
    return;
  }

  let html = '';
  if (data.sat.sourceInstance.type === 'graph') {
    html += '<div class="source-graph">';
    html += '<strong>Vertices:</strong> ' + data.sat.sourceInstance.vertices.join(', ');
    html += '<br><br><strong>Edges:</strong><br>';
    for (let i = 0; i < data.sat.sourceInstance.edges.length; i++) {
      const edge = data.sat.sourceInstance.edges[i];
      html += `<span class="edge" data-edge-idx="${i}" data-u="${edge.u}" data-v="${edge.v}">{${edge.u}, ${edge.v}}</span> `;
    }
    html += '</div>';
  }

  if (data.sat.sourceInstance.extras && data.sat.sourceInstance.extras.length > 0) {
    html += '<div class="extras">';
    for (const extra of data.sat.sourceInstance.extras) {
      html += `<div class="extra-row"><span class="extra-name">${extra.name}:</span><span class="extra-value">${extra.value}</span></div>`;
    }
    html += '</div>';
  }

  container.innerHTML = html;

  // Add hover handlers for edge-to-clause correspondence
  container.querySelectorAll('.edge[data-edge-idx]').forEach(edgeEl => {
    edgeEl.addEventListener('mouseenter', () => highlightSatCorrespondence(edgeEl, true));
    edgeEl.addEventListener('mouseleave', () => highlightSatCorrespondence(edgeEl, false));
  });
}

function highlightSatCorrespondence(edgeEl, highlight) {
  const u = edgeEl.dataset.u;
  const v = edgeEl.dataset.v;

  // Find clause that contains both u and v
  document.querySelectorAll('.clause[data-clause-idx]').forEach(clauseEl => {
    const vars = clauseEl.dataset.vars.split(',');
    if (vars.includes(u) && vars.includes(v)) {
      if (highlight) {
        clauseEl.classList.add('highlight');
        edgeEl.classList.add('highlight');
      } else {
        clauseEl.classList.remove('highlight');
        edgeEl.classList.remove('highlight');
      }
    }
  });
}

function highlightEdgeFromClause(clauseEl, highlight) {
  const vars = clauseEl.dataset.vars.split(',');

  // Find edge whose vertices match the clause variables
  document.querySelectorAll('.edge[data-edge-idx]').forEach(edgeEl => {
    const u = edgeEl.dataset.u;
    const v = edgeEl.dataset.v;
    if (vars.includes(u) && vars.includes(v)) {
      if (highlight) {
        edgeEl.classList.add('highlight');
        clauseEl.classList.add('highlight');
      } else {
        edgeEl.classList.remove('highlight');
        clauseEl.classList.remove('highlight');
      }
    }
  });
}

function updateSatStep() {
  if (!data.sat) return;

  const container = document.getElementById('satTargetContent');

  // Collect visible clause indices up to current step
  const visibleIndices = new Set();
  for (let i = 0; i < stepIndex; i++) {
    data.sat.steps[i].clauseIndices.forEach(idx => visibleIndices.add(idx));
  }

  let html = '<div class="clauses-list">';
  data.sat.clauses.forEach((clause, i) => {
    const isVisible = visibleIndices.has(i + 1);
    const cls = isVisible ? 'clause' : 'clause hidden';
    const vars = clause.literals.map(lit => lit.var).join(',');
    html += `<div class="${cls}" data-clause-idx="${i}" data-vars="${vars}">`;
    html += clause.literals.map(lit => {
      const litCls = lit.positive ? 'literal positive' : 'literal negative';
      const prefix = lit.positive ? '' : '¬';
      return `<span class="${litCls}">${prefix}${lit.var}</span>`;
    }).join(' <span class="or-symbol">∨</span> ');
    html += '</div>';
  });
  html += '</div>';

  html += `
    <div class="legend">
      <div class="legend-item"><span class="literal positive">x</span> Positive literal</div>
      <div class="legend-item"><span class="literal negative">¬x</span> Negative literal</div>
    </div>
  `;

  container.innerHTML = html;

  // Add hover handlers for clause-to-edge correspondence
  container.querySelectorAll('.clause[data-clause-idx]').forEach(clauseEl => {
    clauseEl.addEventListener('mouseenter', () => highlightEdgeFromClause(clauseEl, true));
    clauseEl.addEventListener('mouseleave', () => highlightEdgeFromClause(clauseEl, false));
  });
}

// ============================================================================
// Unified Step Controller
// ============================================================================
function setStep(n) {
  stepIndex = Math.max(0, Math.min(n, data.stepCount));
  slider.value = stepIndex;

  const label = stepIndex > 0 && data.stepLabels && data.stepLabels[stepIndex - 1]
    ? data.stepLabels[stepIndex - 1]
    : (stepIndex === 0 ? 'Click Next to begin' : `Step ${stepIndex}`);
  document.getElementById('stepLabel').textContent = label;
  document.getElementById('stats').textContent = `Step ${stepIndex} / ${data.stepCount}`;

  // Update the appropriate renderer
  if (data.vizType === 'graph') {
    updateGraphStep();
  } else if (data.vizType === 'mapping') {
    updateMappingStep();
  } else if (data.vizType === 'sat') {
    updateSatStep();
  }
}

// ============================================================================
// Initialization
// ============================================================================
document.getElementById('prev').onclick = () => setStep(stepIndex - 1);
document.getElementById('next').onclick = () => setStep(stepIndex + 1);
slider.oninput = (e) => setStep(parseInt(e.target.value));

// Initialize the appropriate renderer
if (data.vizType === 'graph') {
  initGraphRenderer();
} else if (data.vizType === 'mapping') {
  initMappingRenderer();
} else if (data.vizType === 'sat') {
  initSatRenderer();
}

setStep(0);
</script>
</body>
</html>
HTML
))
