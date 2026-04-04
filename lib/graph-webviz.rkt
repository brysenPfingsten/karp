#lang racket

(require racket/file
         racket/list
         racket/match
         racket/string
         (only-in "../private/core-structures.rkt"
                  dp-set?
                  dp-set-members->list)
         (only-in "../private/primitive-data-type.rkt"
                  dp-integer?
                  dp-integer-val)
         (only-in "../el.rkt"
                  el?
                  _1s
                  _2s
                  _3s
                  n_s)
         (only-in "graph.rkt" e-u e-v))

(provide write-hc-steps-html)

(define (normalize-int v)
  (cond
    [(dp-integer? v) (dp-integer-val v)]
    [else v]))

(define (vertex-id v)
  (format "~a" v))

(define (set->list s)
  (cond
    [(dp-set? s) (dp-set-members->list s)]
    [(list? s) s]
    [else '()]))

(define (edge-id u v)
  (format "~a -> ~a" (vertex-id u) (vertex-id v)))

(define (vertex-indices v)
  (define max-i #f)
  (define max-j #f)
  (when (and (el? v) (>= (n_s v) 2))
    (define i (normalize-int (_1s v)))
    (when (integer? i)
      (set! max-i i)))
  (cond
    [(and (el? v) (= (n_s v) 3))
     (define j (normalize-int (_2s v)))
     (when (integer? j)
       (set! max-j j))]
    [(and (el? v) (= (n_s v) 1))
     (define a (_1s v))
     (when (integer? a)
       (set! max-j a))])
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
  (define (pos x y kind i j tag)
    (hash "id" label
          "label" label
          "x" x
          "y" y
          "kind" kind
          "i" i
          "j" j
          "tag" tag))
  (cond
    [(and (el? v) (= (n_s v) 3))
     (define i (normalize-int (_1s v)))
     (define j (normalize-int (_2s v)))
     (define tag (_3s v))
     (define offset
       (cond
         [(eq? tag '-) 0]
         [(eq? tag '+) 18]
         [(eq? tag '*) 36]
         [else 18]))
     (pos (* x-step j) (+ (* y-step i) offset) "var" i j (format "~a" tag))]
    [(and (el? v) (= (n_s v) 2))
     (define i (normalize-int (_1s v)))
     (define tag (_2s v))
     (pos (* x-step (+ max-j 1)) (+ (* y-step i) 18) "var-tail" i (add1 max-j) (format "~a" tag))]
    [(and (el? v) (= (n_s v) 1))
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
    [else
     (pos 0 0 "other" #f #f #f)]))

(define (bounds nodes)
  (define xs (map (lambda (n) (hash-ref n "x" 0)) nodes))
  (define ys (map (lambda (n) (hash-ref n "y" 0)) nodes))
  (define padding 80)
  (define min-x (if (null? xs) 0 (- (apply min xs) padding)))
  (define max-x (if (null? xs) 100 (+ (apply max xs) padding)))
  (define min-y (if (null? ys) 0 (- (apply min ys) padding)))
  (define max-y (if (null? ys) 100 (+ (apply max ys) padding)))
  (hash "minX" min-x
        "minY" min-y
        "width" (- max-x min-x)
        "height" (- max-y min-y)))

(define (steps->json steps node-id-of edge-id-of)
  (for/list ([step (in-list steps)])
    (define vs (if (and (list? step) (>= (length step) 1)) (first step) (set)))
    (define es (if (and (list? step) (>= (length step) 2)) (second step) (set)))
    (hash "addNodes" (for/list ([v (in-list (set->list vs))])
                        (node-id-of (vertex-id v)))
          "addEdges" (for/list ([e (in-list (set->list es))])
                        (edge-id-of (edge-id (e-u e) (e-v e)))))))

(define (steps->labels steps)
  (for/list ([step (in-list steps)])
    (and (list? step)
         (= (length step) 3)
         (let ([label (list-ref step 2)])
           (and label (format "~a" label))))))

(define (json-escape s)
  (define replacements
    (list (cons "\\" "\\\\")
          (cons "\"" "\\\"")
          (cons "\b" "\\b")
          (cons "\f" "\\f")
          (cons "\n" "\\n")
          (cons "\r" "\\r")
          (cons "\t" "\\t")))
  (foldl (lambda (pair acc)
           (string-replace acc (car pair) (cdr pair)))
         s
         replacements))

(define (json->string v)
  (cond
    [(hash? v)
     (string-append
      "{"
      (string-join
       (for/list ([(k val) (in-hash v)])
         (string-append
          (json->string (format "~a" k))
          ":"
          (json->string val)))
       ",")
      "}")]
    [(list? v)
     (string-append
      "["
      (string-join (map json->string v) ",")
      "]")]
    [(string? v) (format "\"~a\"" (json-escape v))]
    [(boolean? v) (if v "true" "false")]
    [(number? v) (format "~a" v)]
    [(symbol? v) (json->string (format "~a" v))]
    [(void? v) "null"]
    [else (json->string (format "~a" v))]))

(define (cytoscape-js-path)
  (define base-dir (or (current-load-relative-directory) (current-directory)))
  (define js-path (build-path base-dir "vendor" "cytoscape.min.js"))
  (and (file-exists? js-path) js-path))

(define (write-hc-steps-html steps output-path #:title [title "3SAT -> Hamiltonian Cycle"] #:labels [labels #f])
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

  (define node-labels
    (sort (hash-keys nodes) string<?))
  (define node-id-map
    (for/hash ([lbl (in-list node-labels)]
               [i (in-naturals 1)])
      (values lbl (format "n~a" i))))
  (define (node-id-of lbl)
    (hash-ref node-id-map lbl))

  (define nodes-json
    (for/list ([v (in-hash-values nodes)])
      (define lbl (vertex-id v))
      (define base (node->json v max-i max-j x-step y-step))
      (hash-set (hash-set base "id" (node-id-of lbl)) "label" lbl)))

  (define edge-keys
    (sort (hash-keys edges) string<?))
  (define edge-id-map
    (for/hash ([key (in-list edge-keys)]
               [i (in-naturals 1)])
      (values key (format "e~a" i))))
  (define (edge-id-of key)
    (hash-ref edge-id-map key))

  (define edges-json
    (for/list ([(key uv) (in-hash edges)])
      (define u (first uv))
      (define v (second uv))
      (hash "id" (edge-id-of key)
            "source" (node-id-of (vertex-id u))
            "target" (node-id-of (vertex-id v)))))

  (define data
    (hash "nodes" nodes-json
          "edges" edges-json
          "steps" (steps->json steps node-id-of edge-id-of)
          "stepLabels" (or labels (steps->labels steps) #f)
          "viewBox" (bounds nodes-json)))

  (define json-data (json->string data))

  (define html
    (string-append
     "<!doctype html>\n"
     "<html lang=\"en\">\n"
     "<head>\n"
     "<meta charset=\"utf-8\">\n"
     "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">\n"
     "<title>" title "</title>\n"
     "<style>\n"
     "  :root { --bg: #f6f3ea; --ink: #1b1b1b; --edge: #4b4b4b; }\n"
     "  * { box-sizing: border-box; }\n"
     "  html, body { height: 100%; }\n"
     "  body { margin: 0; font-family: Georgia, serif; background: var(--bg); color: var(--ink); }\n"
     "  header { padding: 16px 20px; border-bottom: 2px solid #222; background: #f0eadc; }\n"
     "  header h1 { margin: 0; font-size: 20px; letter-spacing: 0.5px; }\n"
     "  #app { display: flex; flex-direction: column; height: 100vh; }\n"
     "  .toolbar { display: grid; grid-template-columns: auto 1fr auto; align-items: center; gap: 12px; padding: 12px 20px; background: #efe7d6; border-bottom: 1px solid #c7bea8; }\n"
     "  .toolbar button { border: 1px solid #1b1b1b; background: #fff6dd; padding: 6px 10px; cursor: pointer; }\n"
     "  .toolbar input[type=range] { width: 220px; }\n"
     "  .controls { display: flex; gap: 8px; align-items: center; }\n"
     "  .stats { font-size: 13px; justify-self: end; }\n"
     "  .annotation { font-size: 14px; font-weight: 700; text-align: center; color: #2f2a1f; }\n"
     "  #graph { flex: 1 1 auto; width: 100%; min-height: 420px; background: radial-gradient(circle at 20% 10%, #fff 0%, #f6f3ea 60%, #efe5d0 100%); }\n"
     "</style>\n"
     "</head>\n"
     "<body>\n"
     "<div id=\"app\">\n"
     "  <header><h1>" title "</h1></header>\n"
     "  <div class=\"toolbar\">\n"
     "    <div class=\"controls\">\n"
     "      <button id=\"back\">Prev</button>\n"
     "      <button id=\"forward\">Next</button>\n"
     "      <button id=\"layout\">Layout</button>\n"
     "      <input id=\"slider\" type=\"range\" min=\"0\" value=\"0\">\n"
     "    </div>\n"
     "    <div class=\"annotation\" id=\"annotation\"></div>\n"
     "    <div class=\"stats\" id=\"stats\"></div>\n"
     "  </div>\n"
     "  <div id=\"graph\" aria-label=\"graph visualization\"></div>\n"
     "</div>\n"
     "<script src=\"" (if (cytoscape-js-path)
                           (path->string (cytoscape-js-path))
                           "vendor/cytoscape.min.js") "\"></script>\n"
     "<script>\n"
     "const data = " json-data ";\n"
     "window.graphData = data;\n"
     "const steps = data.steps;\n"
     "const stepLabels = data.stepLabels || null;\n"
     "const slider = document.getElementById('slider');\n"
     "slider.max = steps.length;\n"
     "let stepIndex = 0;\n"
     "const activeNodes = new Set();\n"
     "const activeEdges = new Set();\n"
     "if (typeof cytoscape === 'undefined') {\n"
     "  document.getElementById('debug').textContent = 'cytoscape failed to load';\n"
     "} else {\n"
     "const cy = cytoscape({\n"
     "  container: document.getElementById('graph'),\n"
     "  elements: data.nodes.map(n => ({ data: { id: n.id, label: n.label, kind: n.kind }, position: { x: n.x, y: n.y } }))\n"
     "    .concat(data.edges.map(e => ({ data: { id: e.id, source: e.source, target: e.target } }))),\n"
     "  layout: { name: 'preset' },\n"
     "  style: [\n"
     "    { selector: 'node', style: {\n"
     "        'label': 'data(label)',\n"
     "        'text-valign': 'center',\n"
     "        'text-halign': 'center',\n"
     "        'width': 18,\n"
     "        'height': 18,\n"
     "        'font-size': 8,\n"
     "        'color': '#1b1b1b',\n"
     "        'background-color': '#c0c0c0',\n"
     "        'border-color': '#111',\n"
     "        'border-width': 1\n"
     "      }\n"
     "    },\n"
     "    { selector: 'edge', style: {\n"
     "        'curve-style': 'bezier',\n"
     "        'target-arrow-shape': 'triangle',\n"
     "        'line-color': '#4b4b4b',\n"
     "        'target-arrow-color': '#4b4b4b',\n"
     "        'width': 1.4,\n"
     "        'opacity': 0.7\n"
     "      }\n"
     "    },\n"
     "    { selector: '.hidden', style: { 'display': 'none' } },\n"
     "    { selector: 'node[kind = \"var\"]', style: { 'background-color': '#f7b32b' } },\n"
     "    { selector: 'node[kind = \"var-tail\"]', style: { 'background-color': '#f6ae2d' } },\n"
     "    { selector: 'node[kind = \"clause\"]', style: { 'background-color': '#f9564f' } },\n"
     "    { selector: 'node[kind = \"terminal\"]', style: { 'background-color': '#0d5c63', 'color': '#f6f3ea' } }\n"
     "  ]\n"
     "});\n"
     "cy.elements().addClass('hidden');\n"
     "const nodeMeta = new Map(data.nodes.map(n => [n.id, n]));\n"
     "cy.fit(cy.elements(), 40);\n"
     "const baseZoom = cy.zoom();\n"
     "const basePan = cy.pan();\n"

     "function autoLabel(step) {\n"
     "  const nodes = step.addNodes || [];\n"
     "  const edges = step.addEdges || [];\n"
     "  if (!nodes.length && edges.length) return 'Add edges';\n"
     "  if (!nodes.length && !edges.length) return '';\n"
     "  const kinds = new Set();\n"
     "  for (const id of nodes) {\n"
     "    const meta = nodeMeta.get(id);\n"
     "    if (meta && meta.kind) kinds.add(meta.kind);\n"
     "  }\n"
     "  if (kinds.size === 1 && kinds.has('terminal')) return 'Add terminal nodes';\n"
     "  if (kinds.size === 1 && kinds.has('clause')) return 'Add clause nodes';\n"
     "  if (kinds.has('var') || kinds.has('var-tail')) return 'Add variable gadget nodes';\n"
     "  return 'Add nodes';\n"
     "}\n"

     "function setStep(next) {\n"
     "  stepIndex = Math.max(0, Math.min(next, steps.length));\n"
     "  activeNodes.clear();\n"
     "  activeEdges.clear();\n"
     "  for (let i = 0; i < stepIndex; i++) {\n"
     "    for (const n of steps[i].addNodes) activeNodes.add(n);\n"
     "    for (const e of steps[i].addEdges) activeEdges.add(e);\n"
     "  }\n"
     "  cy.elements().addClass('hidden');\n"
     "  for (const n of activeNodes) cy.getElementById(n).removeClass('hidden');\n"
     "  for (const e of activeEdges) cy.getElementById(e).removeClass('hidden');\n"
     "  slider.value = stepIndex;\n"
     "  document.getElementById('stats').textContent = `Step ${stepIndex}/${steps.length} | Nodes ${activeNodes.size} | Edges ${activeEdges.size}`;\n"
     "  const stepLabel = stepIndex > 0 ? (stepLabels && stepLabels[stepIndex - 1]) : '';\n"
     "  document.getElementById('annotation').textContent = stepLabel || (stepIndex > 0 ? autoLabel(steps[stepIndex - 1]) : '');\n"
     "  cy.zoom(baseZoom);\n"
     "  cy.pan(basePan);\n"
     "}\n"

     "document.getElementById('back').addEventListener('click', () => setStep(stepIndex - 1));\n"
     "document.getElementById('forward').addEventListener('click', () => setStep(stepIndex + 1));\n"
     "document.getElementById('layout').addEventListener('click', () => {\n"
     "  cy.layout({ name: 'cose', animate: true, fit: true }).run();\n"
     "});\n"
     "slider.addEventListener('input', (evt) => setStep(parseInt(evt.target.value, 10)));\n"
     "setStep(stepIndex);\n"
     "}\n"
     "</script>\n"
     "</body>\n"
     "</html>\n"))

  (call-with-output-file output-path
    (lambda (out)
      (display html out))
    #:exists 'replace)
  output-path)
