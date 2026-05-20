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
         (only-in "graph.rkt" e-u e-v))

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
  (member v '(graph mapping)))

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

(define (extract-graph-data steps)
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

  (hash "nodes" nodes-json
        "edges" edges-json
        "steps" steps-json
        "viewBox" (bounds nodes-json)))

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
;; HTML Generation
;; ============================================================================

(define (write-unified-viz-html steps output-path
                                 #:title [title "Karp Reduction Visualization"]
                                 #:source-instance [source-inst #f]
                                 #:viz-type [explicit-viz-type #f])

  (define viz-type (or explicit-viz-type (detect-viz-type steps)))
  (define step-labels (extract-step-labels steps))

  ;; Build unified data structure
  (define data
    (hash "vizType" (symbol->string viz-type)
          "title" title
          "stepLabels" step-labels
          "stepCount" (length steps)
          ;; Type-specific data
          "graph" (if (eq? viz-type 'graph) (extract-graph-data steps) #f)
          "mapping" (if (eq? viz-type 'mapping) (extract-mapping-data steps source-inst) #f)))

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
  --bg: #f6f3ea;
  --panel-bg: #fff;
  --border: #c7bea8;
  --ink: #1b1b1b;
  --accent: #4a90d9;
  --highlight: #fff3cd;
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
  background: #f0eadc;
  border-bottom: 2px solid #222;
}
header h1 { margin: 0; font-size: 18px; font-weight: 600; }
.toolbar {
  display: flex;
  align-items: center;
  gap: 16px;
  padding: 10px 20px;
  background: #efe7d6;
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
}

/* Graph-specific styles */
#graph-container {
  flex: 1;
  display: none;
}
#cy {
  width: 100%;
  height: 100%;
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
  grid-template-columns: 1fr 40px 1fr;
  gap: 0;
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
.arrow-col {
  display: flex;
  align-items: center;
  justify-content: center;
  font-size: 28px;
  color: #999;
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
tr.new td { background: #e8f5e9; }
tr.gadget td { background: #ffebee; }
tr.hidden { opacity: 0.25; }
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
.legend-color.new { background: #e8f5e9; border: 1px solid #a5d6a7; }
.legend-color.gadget { background: #ffebee; border: 1px solid #ef9a9a; }
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
  <div id="graph-container"><div id="cy"></div></div>
  <div id="mapping-container">
    <div class="mapping-content">
      <div class="panel" id="sourcePanel">
        <h2>Source Instance</h2>
        <div id="sourceContent"></div>
      </div>
      <div class="arrow-col">&rarr;</div>
      <div class="panel" id="targetPanel">
        <h2>Target Instance</h2>
        <div id="targetContent"></div>
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
// Graph Renderer
// ============================================================================
let cy = null;
const nodeVisibility = {};
const edgeVisibility = {};

function initGraphRenderer() {
  if (!data.graph || typeof cytoscape === 'undefined') return;

  document.getElementById('graph-container').style.display = 'block';

  const elements = [];
  data.graph.nodes.forEach(n => {
    elements.push({
      data: { id: n.id, label: n.label, kind: n.kind, tag: n.tag },
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

  cy = cytoscape({
    container: document.getElementById('cy'),
    elements: elements,
    style: [
      {
        selector: 'node',
        style: {
          'label': 'data(label)',
          'text-valign': 'center',
          'text-halign': 'center',
          'background-color': '#4a90d9',
          'color': '#fff',
          'font-size': '10px',
          'width': 28,
          'height': 28
        }
      },
      {
        selector: 'node[kind="clause"]',
        style: { 'background-color': '#666', 'shape': 'rectangle', 'width': 36, 'height': 24 }
      },
      {
        selector: 'node[kind="terminal"]',
        style: { 'background-color': '#e74c3c', 'shape': 'diamond', 'width': 32, 'height': 32 }
      },
      {
        selector: 'edge',
        style: {
          'width': 2,
          'line-color': '#999',
          'target-arrow-color': '#999',
          'target-arrow-shape': 'triangle',
          'curve-style': 'bezier'
        }
      },
      {
        selector: '.hidden',
        style: { 'opacity': 0 }
      }
    ],
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
    html += `<tr><td>${obj.name}</td><td>${obj.value}</td></tr>`;
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
    html += `<tr class="${rowClass}"><td>${obj.name}</td><td>${valueDisplay}</td></tr>`;
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
}

setStep(0);
</script>
</body>
</html>
HTML
))
