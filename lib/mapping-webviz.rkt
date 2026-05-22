#lang racket

;; Generic Mapping Visualization for Karp Reductions
;; Renders mapping-based reductions showing source and target instances
;; with step-by-step construction and correspondence

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
                  _1s _2s _3s n_s))

(provide write-mapping-steps-html
         mapping-el-webviz-steps?)

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

;; Check if a vertex is a mapping-style el: (el kind name value)
(define (mapping-el? v)
  (and (el? v)
       (let ([arity (normalize-int (n_s v))])
         (= arity 3))))

;; Check if steps are mapping visualization steps
;; Each step is (list vertices edges label?) where vertices contain mapping els
(define (mapping-el-webviz-steps? steps)
  (and (list? steps)
       (not (null? steps))
       (for/and ([step (in-list steps)])
         (match step
           [(list vs _es)
            (and (not (null? (set->list vs)))
                 (for/and ([v (in-list (set->list vs))])
                   (mapping-el? v)))]
           [(list vs _es _label)
            (and (not (null? (set->list vs)))
                 (for/and ([v (in-list (set->list vs))])
                   (mapping-el? v)))]
           [_ #f]))))

;; Extract info from an el vertex: (el kind name value)
(define (el->info v)
  (list (format "~a" (_1s v))    ; kind (e.g., 'obj, 'gadget)
        (format "~a" (_2s v))    ; name
        (normalize-int (_3s v)))) ; value

;; Generate HTML for mapping reduction visualization
(define (write-mapping-steps-html steps output-path
                                   #:title [title "Mapping Reduction"]
                                   #:source-instance [source-inst #f])

  ;; Collect all objects from all steps
  (define all-objects (make-hash))
  (define step-data '())

  (for ([step (in-list steps)]
        [i (in-naturals)])
    (define vs (if (and (list? step) (>= (length step) 1)) (first step) (set)))
    (define label (and (list? step) (= (length step) 3) (third step)))
    (define step-objects '())

    (for ([v (in-list (set->list vs))])
      (when (mapping-el? v)
        (match-define (list kind name value) (el->info v))
        (define obj-data (hash "kind" kind "name" name "value" value))
        (hash-set! all-objects name obj-data)
        (set! step-objects (cons name step-objects))))

    (set! step-data
          (append step-data
                  (list (hash "objects" (reverse step-objects)
                              "label" (or label ""))))))

  ;; Build source instance data from a dp-instance
  ;; Extract sets, mappings, and scalar values from the instance fields
  (define source-data
    (if (and source-inst (dp-instance? source-inst))
        (let* ([fields (cdr (dp-instance-fields source-inst))] ; skip 'instance marker
               [the-set #f]
               [the-mapping #f]
               [extras '()])
          ;; Find sets, mappings, and other values in fields
          ;; Track scalar field count for naming
          (define scalar-count 0)
          (for ([field fields]
                [i (in-naturals)])
            (cond
              [(and (dp-set? field) (not the-set))
               (set! the-set field)]
              [(and (dp-mapping? field) (not the-mapping))
               (set! the-mapping field)]
              [(dp-integer? field)
               (set! scalar-count (add1 scalar-count))
               ;; Common convention: first scalar is "K" (target value)
               (define name (if (= scalar-count 1) "K" (format "K~a" scalar-count)))
               (set! extras (cons (hash "name" name
                                        "value" (normalize-int field))
                                  extras))]
              [(number? field)
               (set! scalar-count (add1 scalar-count))
               (define name (if (= scalar-count 1) "K" (format "K~a" scalar-count)))
               (set! extras (cons (hash "name" name
                                        "value" field)
                                  extras))]))
          ;; Build the source data
          (if (and the-set the-mapping)
              (hash "objects"
                    (for/list ([obj (in-list (set->list the-set))])
                      (hash "name" (format "~a" obj)
                            "value" (normalize-int
                                     (hash-ref (dp-mapping-H the-mapping) obj #f))))
                    "extras" (reverse extras))
              #f))
        #f))

  (define data
    (hash "objects" (hash-values all-objects)
          "steps" step-data
          "sourceInstance" source-data
          "title" title))

  (define json-data (json->string data))

  (define html
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
  --new: #888888;
  --gadget: #333333;
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
  display: grid;
  grid-template-columns: 1fr 40px 1fr;
  gap: 0;
  padding: 20px;
  overflow: auto;
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
tr.new td { background: #e0e0e0; }
tr.gadget td { background: #d0d0d0; }
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
.legend-color.new { background: #e0e0e0; border: 1px solid #999999; }
.legend-color.gadget { background: #d0d0d0; border: 1px solid #888888; }
</style>
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
<script>
const data =
HTML
json-data
#<<HTML
;
document.getElementById('title').textContent = data.title;

const slider = document.getElementById('slider');
slider.max = data.steps.length;
let stepIndex = 0;

// Build source objects lookup
const sourceNames = new Set();
if (data.sourceInstance && data.sourceInstance.objects) {
  data.sourceInstance.objects.forEach(o => sourceNames.add(o.name));
}

function renderSource() {
  const container = document.getElementById('sourceContent');
  if (!data.sourceInstance) {
    document.getElementById('sourcePanel').style.display = 'none';
    return;
  }

  let html = '<table><thead><tr><th>Object</th><th>Value</th></tr></thead><tbody>';
  for (const obj of data.sourceInstance.objects) {
    html += `<tr><td>${obj.name}</td><td>${obj.value}</td></tr>`;
  }
  html += '</tbody></table>';

  if (data.sourceInstance.extras && data.sourceInstance.extras.length > 0) {
    html += '<div class="extras">';
    for (const extra of data.sourceInstance.extras) {
      html += `<div class="extra-row"><span class="extra-name">${extra.name}:</span><span class="extra-value">${extra.value}</span></div>`;
    }
    html += '</div>';
  }

  container.innerHTML = html;
}

function renderTarget() {
  const container = document.getElementById('targetContent');

  // Collect visible objects up to current step
  const visible = new Set();
  for (let i = 0; i < stepIndex; i++) {
    data.steps[i].objects.forEach(name => visible.add(name));
  }

  let html = '<table><thead><tr><th>Object</th><th>Value</th></tr></thead><tbody>';

  // Sort objects: source objects first, then gadgets
  const sortedObjects = [...data.objects].sort((a, b) => {
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

function setStep(n) {
  stepIndex = Math.max(0, Math.min(n, data.steps.length));
  slider.value = stepIndex;

  const label = stepIndex > 0 ? data.steps[stepIndex - 1].label : 'Click Next to begin';
  document.getElementById('stepLabel').textContent = label;
  document.getElementById('stats').textContent = `Step ${stepIndex} / ${data.steps.length}`;

  renderTarget();
}

document.getElementById('prev').onclick = () => setStep(stepIndex - 1);
document.getElementById('next').onclick = () => setStep(stepIndex + 1);
slider.oninput = (e) => setStep(parseInt(e.target.value));

renderSource();
setStep(0);
</script>
</body>
</html>
HTML
))

  (call-with-output-file output-path
    (lambda (out) (display html out))
    #:exists 'truncate)
  output-path)
