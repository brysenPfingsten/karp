#lang racket

(require racket/list
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

(define (steps->json steps)
  (for/list ([step (in-list steps)])
    (match-define (list vs es) step)
    (hash "addNodes" (for/list ([v (in-list (set->list vs))])
                        (vertex-id v))
          "addEdges" (for/list ([e (in-list (set->list es))])
                        (edge-id (e-u e) (e-v e))))))

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

(define (write-hc-steps-html steps output-path #:title [title "3SAT -> Hamiltonian Cycle"])
  (define nodes (make-hash))
  (define edges (make-hash))
  (for ([step (in-list steps)])
    (match-define (list vs es) step)
    (for ([v (in-list (set->list vs))])
      (hash-set! nodes (vertex-id v) v))
    (for ([e (in-list (set->list es))])
      (define u (e-u e))
      (define v (e-v e))
      (hash-set! edges (edge-id u v) (list u v))))

  (define-values (max-i max-j) (compute-max-indices nodes))
  (define x-step 220)
  (define y-step 90)

  (define nodes-json
    (for/list ([v (in-hash-values nodes)])
      (node->json v max-i max-j x-step y-step)))

  (define edges-json
    (for/list ([(id uv) (in-hash edges)])
      (define u (first uv))
      (define v (second uv))
      (hash "id" id
            "source" (vertex-id u)
            "target" (vertex-id v))))

  (define data
    (hash "nodes" nodes-json
          "edges" edges-json
          "steps" (steps->json steps)
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
     "  :root { --bg: #f6f3ea; --ink: #1b1b1b; --accent: #0d5c63; --edge: #4b4b4b; }\n"
     "  * { box-sizing: border-box; }\n"
     "  body { margin: 0; font-family: Georgia, serif; background: var(--bg); color: var(--ink); }\n"
     "  header { padding: 16px 20px; border-bottom: 2px solid #222; background: #f0eadc; }\n"
     "  header h1 { margin: 0; font-size: 20px; letter-spacing: 0.5px; }\n"
     "  #app { display: grid; grid-template-rows: auto 1fr; height: 100vh; }\n"
     "  .toolbar { display: flex; gap: 8px; align-items: center; padding: 12px 20px; background: #efe7d6; border-bottom: 1px solid #c7bea8; }\n"
     "  .toolbar button { border: 1px solid #1b1b1b; background: #fff6dd; padding: 6px 10px; cursor: pointer; }\n"
     "  .toolbar input[type=range] { width: 220px; }\n"
     "  .stats { margin-left: auto; font-size: 13px; }\n"
     "  #graph { width: 100%; height: 100%; background: radial-gradient(circle at 20% 10%, #fff 0%, #f6f3ea 60%, #efe5d0 100%); }\n"
     "  .edge { stroke: var(--edge); stroke-width: 1.4; opacity: 0.7; }\n"
     "  .node { stroke: #111; stroke-width: 1; cursor: grab; }\n"
     "  .node.dragging { cursor: grabbing; }\n"
     "  .node.var { fill: #f7b32b; }\n"
     "  .node.var-tail { fill: #f6ae2d; }\n"
     "  .node.clause { fill: #f9564f; }\n"
     "  .node.terminal { fill: #0d5c63; }\n"
     "  .node.other { fill: #c0c0c0; }\n"
     "  .label { font-size: 11px; pointer-events: none; fill: #1b1b1b; }\n"
     "</style>\n"
     "</head>\n"
     "<body>\n"
     "<div id=\"app\">\n"
     "  <header><h1>" title "</h1></header>\n"
     "  <div class=\"toolbar\">\n"
     "    <button id=\"back\">Prev</button>\n"
     "    <button id=\"forward\">Next</button>\n"
     "    <input id=\"slider\" type=\"range\" min=\"0\" value=\"0\">\n"
     "    <div class=\"stats\" id=\"stats\"></div>\n"
     "  </div>\n"
     "  <svg id=\"graph\" aria-label=\"graph visualization\"></svg>\n"
     "</div>\n"
     "<script>\n"
     "const data = " json-data ";\n"
     "window.graphData = data;\n"
     "const svg = document.getElementById('graph');\n"
     "const viewBox = data.viewBox;\n"
     "svg.setAttribute('viewBox', `${viewBox.minX} ${viewBox.minY} ${viewBox.width} ${viewBox.height}`);\n"
     "const edgeById = new Map(data.edges.map(e => [e.id, e]));\n"
     "const nodeById = new Map(data.nodes.map(n => [n.id, n]));\n"
     "const steps = data.steps;\n"
     "const slider = document.getElementById('slider');\n"
     "slider.max = steps.length;\n"
     "let stepIndex = 0;\n"
     "const activeNodes = new Set();\n"
     "const activeEdges = new Set();\n"
     "const edgeEls = new Map();\n"
     "const nodeEls = new Map();\n"
     "let dragging = null;\n"

     "function buildDefs() {\n"
     "  const defs = document.createElementNS('http://www.w3.org/2000/svg', 'defs');\n"
     "  const marker = document.createElementNS('http://www.w3.org/2000/svg', 'marker');\n"
     "  marker.setAttribute('id', 'arrow');\n"
     "  marker.setAttribute('markerWidth', '10');\n"
     "  marker.setAttribute('markerHeight', '8');\n"
     "  marker.setAttribute('refX', '9');\n"
     "  marker.setAttribute('refY', '4');\n"
     "  marker.setAttribute('orient', 'auto');\n"
     "  const path = document.createElementNS('http://www.w3.org/2000/svg', 'path');\n"
     "  path.setAttribute('d', 'M0,0 L10,4 L0,8 Z');\n"
     "  path.setAttribute('fill', '#4b4b4b');\n"
     "  marker.appendChild(path);\n"
     "  defs.appendChild(marker);\n"
     "  svg.appendChild(defs);\n"
     "}\n"

     "function render() {\n"
     "  while (svg.firstChild) svg.removeChild(svg.firstChild);\n"
     "  buildDefs();\n"
     "  edgeEls.clear();\n"
     "  nodeEls.clear();\n"
     "  for (const edgeId of activeEdges) {\n"
     "    const edge = edgeById.get(edgeId);\n"
     "    if (!edge) continue;\n"
     "    const u = nodeById.get(edge.source);\n"
     "    const v = nodeById.get(edge.target);\n"
     "    if (!u || !v) continue;\n"
     "    const line = document.createElementNS('http://www.w3.org/2000/svg', 'line');\n"
     "    line.setAttribute('x1', u.x);\n"
     "    line.setAttribute('y1', u.y);\n"
     "    line.setAttribute('x2', v.x);\n"
     "    line.setAttribute('y2', v.y);\n"
     "    line.setAttribute('class', 'edge');\n"
     "    line.setAttribute('marker-end', 'url(#arrow)');\n"
     "    svg.appendChild(line);\n"
     "    edgeEls.set(edgeId, line);\n"
     "  }\n"
     "  for (const nodeId of activeNodes) {\n"
     "    const node = nodeById.get(nodeId);\n"
     "    if (!node) continue;\n"
     "    const group = document.createElementNS('http://www.w3.org/2000/svg', 'g');\n"
     "    const circle = document.createElementNS('http://www.w3.org/2000/svg', 'circle');\n"
     "    circle.setAttribute('cx', node.x);\n"
     "    circle.setAttribute('cy', node.y);\n"
     "    circle.setAttribute('r', 10);\n"
     "    circle.setAttribute('class', `node ${node.kind}`);\n"
     "    circle.dataset.nodeId = nodeId;\n"
     "    const label = document.createElementNS('http://www.w3.org/2000/svg', 'text');\n"
     "    label.setAttribute('x', node.x + 14);\n"
     "    label.setAttribute('y', node.y + 4);\n"
     "    label.setAttribute('class', 'label');\n"
     "    label.dataset.nodeId = nodeId;\n"
     "    label.textContent = node.label;\n"
     "    const title = document.createElementNS('http://www.w3.org/2000/svg', 'title');\n"
     "    title.textContent = node.label;\n"
     "    circle.appendChild(title);\n"
     "    group.appendChild(circle);\n"
     "    group.appendChild(label);\n"
     "    svg.appendChild(group);\n"
     "    nodeEls.set(nodeId, { circle, label });\n"
     "  }\n"
     "  document.getElementById('stats').textContent = `Step ${stepIndex}/${steps.length} | Nodes ${activeNodes.size} | Edges ${activeEdges.size}`;\n"
     "}\n"

     "function svgPoint(evt) {\n"
     "  const pt = svg.createSVGPoint();\n"
     "  pt.x = evt.clientX;\n"
     "  pt.y = evt.clientY;\n"
     "  const ctm = svg.getScreenCTM();\n"
     "  if (!ctm) return { x: 0, y: 0 };\n"
     "  const res = pt.matrixTransform(ctm.inverse());\n"
     "  return { x: res.x, y: res.y };\n"
     "}\n"

     "function updateNodePosition(nodeId, x, y) {\n"
     "  const node = nodeById.get(nodeId);\n"
     "  if (!node) return;\n"
     "  node.x = x;\n"
     "  node.y = y;\n"
     "  const el = nodeEls.get(nodeId);\n"
     "  if (el) {\n"
     "    el.circle.setAttribute('cx', x);\n"
     "    el.circle.setAttribute('cy', y);\n"
     "    el.label.setAttribute('x', x + 14);\n"
     "    el.label.setAttribute('y', y + 4);\n"
     "  }\n"
     "  for (const [edgeId, edge] of edgeById.entries()) {\n"
     "    if (!activeEdges.has(edgeId)) continue;\n"
     "    if (edge.source !== nodeId && edge.target !== nodeId) continue;\n"
     "    const u = nodeById.get(edge.source);\n"
     "    const v = nodeById.get(edge.target);\n"
     "    const line = edgeEls.get(edgeId);\n"
     "    if (line && u && v) {\n"
     "      line.setAttribute('x1', u.x);\n"
     "      line.setAttribute('y1', u.y);\n"
     "      line.setAttribute('x2', v.x);\n"
     "      line.setAttribute('y2', v.y);\n"
     "    }\n"
     "  }\n"
     "}\n"

     "function setStep(next) {\n"
     "  stepIndex = Math.max(0, Math.min(next, steps.length));\n"
     "  activeNodes.clear();\n"
     "  activeEdges.clear();\n"
     "  for (let i = 0; i < stepIndex; i++) {\n"
     "    for (const n of steps[i].addNodes) activeNodes.add(n);\n"
     "    for (const e of steps[i].addEdges) activeEdges.add(e);\n"
     "  }\n"
     "  slider.value = stepIndex;\n"
     "  render();\n"
     "}\n"

     "document.getElementById('back').addEventListener('click', () => setStep(stepIndex - 1));\n"
     "document.getElementById('forward').addEventListener('click', () => setStep(stepIndex + 1));\n"
     "slider.addEventListener('input', (evt) => setStep(parseInt(evt.target.value, 10)));\n"
     "svg.addEventListener('pointerdown', (evt) => {\n"
     "  const target = evt.target;\n"
     "  if (!target || !target.dataset) return;\n"
     "  const nodeId = target.dataset.nodeId;\n"
     "  if (!nodeId || !activeNodes.has(nodeId)) return;\n"
     "  dragging = nodeId;\n"
     "  target.classList.add('dragging');\n"
     "  svg.setPointerCapture(evt.pointerId);\n"
     "});\n"
     "svg.addEventListener('pointermove', (evt) => {\n"
     "  if (!dragging) return;\n"
     "  const pos = svgPoint(evt);\n"
     "  updateNodePosition(dragging, pos.x, pos.y);\n"
     "});\n"
     "svg.addEventListener('pointerup', (evt) => {\n"
     "  if (!dragging) return;\n"
     "  const el = nodeEls.get(dragging);\n"
     "  if (el) el.circle.classList.remove('dragging');\n"
     "  dragging = null;\n"
     "  svg.releasePointerCapture(evt.pointerId);\n"
     "});\n"
     "setStep(0);\n"
     "</script>\n"
     "</body>\n"
     "</html>\n"))

  (call-with-output-file output-path
    (lambda (out)
      (display html out))
    #:exists 'replace)
  output-path)
