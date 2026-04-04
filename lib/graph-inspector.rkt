#lang racket

(require (except-in racket/gui set-equal?)
         (except-in mrlib/graph dot-positioning)
         (only-in "../private/core-structures.rkt"
                  set-equal?
                  set-∪
                  dp-list->set
                  dp-set-members->list
                  [set dp-set]
                  dp-tuple?)
         (only-in "modified/dot.rkt" dot-positioning)
         (prefix-in gviz-wrap: "../gviz-wrapper/interface.rkt") 
         (prefix-in mrlib: mrlib/image-core)
         "graph.rkt")

(provide visualize visualize/step render-graph/snip)

(define vertex-snip-class%
  (class snip-class%
    (super-new)
    ))
   
(define vertex-snip-class (new vertex-snip-class%))

(define vertex-snip%
  (class (graph-snip-mixin snip%)
    (inherit set-snipclass
             get-admin)
    (init-field k-v size)
      
    (super-new)
    (set-snipclass vertex-snip-class)
    (send (get-the-snip-class-list) add vertex-snip-class)
      
    (define/override (get-extent dc x y	 	 	 	 
                                 [w #f]
                                 [h #f]
                                 [descent #f]
                                 [space #f]
                                 [lspace #f]
                                 [rspace #f])
      (define (maybe-set-box! b v) (when b (set-box! b v)))
      (maybe-set-box! w (+ 2.0 size))
      (maybe-set-box! h (+ 2.0 size))
      (maybe-set-box! descent 1.0)
      (maybe-set-box! space 1.0)
      (maybe-set-box! lspace 1.0)
      (maybe-set-box! rspace 1.0))
      
    (define/override (draw dc x y left top right bottom dx dy draw-caret)
      (define out (open-output-string))
      (print k-v out)
      (define label (get-output-string out))
      (define-values (w h d a) (send dc get-text-extent label))

      (define size-w-text (+ (max w h size) 5.0))
        
      (send dc draw-ellipse (+ x 1.0) (+ y 1.0) size size)
      (send dc draw-text label (+ x 2.0) (+ y 4.0)))
      
    #;(define/override (copy)
      (new vertex-snip% [size size]))
      
    (define/override (write f)
      (send f put size))
      
    ))

(define graph-pasteboard% 
  (class (graph-pasteboard-mixin pasteboard%)   
    (super-new)))

; a-k-graph -- a karp graph
(define (to-graph-pb a-k-graph [v-size 20.0])
  (define directed? (dp-graph-directed? a-k-graph))

  (define graph-pb
    (let ([pb (new graph-pasteboard%)])
      (send pb set-flip-labels? #f)
      pb))

  (define V-lst (dp-set-members->list (dp-graph-V a-k-graph)))

  (define vertex-snip%-lst
    (map (λ (a-karp-v)
           (new vertex-snip% [k-v a-karp-v] [size v-size] )) V-lst))

  (map (λ (a-v) (send graph-pb insert a-v)) vertex-snip%-lst)

  (define link-created? (make-hash))
  (for* ([u vertex-snip%-lst]
         [v vertex-snip%-lst])
    (when (and (has-edge? (get-field k-v u) (get-field k-v v) a-k-graph)
               (or directed? (not (hash-ref! link-created? (cons u v) #f))))
      (hash-set! link-created? (cons u v) #t)
      (add-links u v)))
  
  (dot-positioning graph-pb dot-label #f directed?)
  (send graph-pb set-draw-arrow-heads? directed?)
  
  graph-pb)

;; ASSUME no v-e can be both empty v and empty e
;; (ListOf (List (Setof Vertex) (Setof Edge))) --> ()
(define (visualize/step verts-and-edges [title "Graph"])
  (define index 0) ;; () -> bitmap

  (define (next-graph!)
    ;; TODO (set? es/vs) set predicate? contract?

    (let* ([shrunk-list (take verts-and-edges index)]
           [just-verts (map first shrunk-list)]
           [just-edges (map second shrunk-list)]
           [edges (foldl (lambda (s acc) (set-∪ s acc)) (dp-set) just-edges)]
           [vertices (foldl (lambda (s acc) (set-∪ s acc)) (dp-set) just-verts)]
           [directed? (ormap dp-tuple? (dp-set-members->list edges))]
           [racket-graph (dp-graph->racket-graph (create-graph vertices edges #:directed? directed?))]
           [gviz-bitmap (gviz-wrap:racket-graph->bitmap racket-graph)])
      (send canvas set-image gviz-bitmap)))

  (define frame
      (new frame% [label title] [width 800] [height 600]))

  (define root
    (new vertical-panel% [parent frame]
         [stretchable-width #t] [stretchable-height #t]))

  (define toolbar
    (new horizontal-panel% [parent root]
         [stretchable-height #f] [stretchable-width #t]))

  (define graph-canvas%
    (class canvas%
      (init-field [img #f])
      (super-new)
      (inherit get-dc)

      (define/public (set-image new-img)
        (set! img new-img)
        (send this refresh))

      (define/override (on-paint)
        (define dc (get-dc))
        (send dc clear)
        (when img
          (mrlib:render-image img dc 0 0)))))

  (define canvas
    (new graph-canvas% [parent root]
         [img (make-object bitmap% 100 100)]))

  (define (enable-and-disable-buttons!)
    (send step-button enable #t)
    (send back-all-the-way-button enable #t)
    (send back-button enable #t)
    (send step-all-the-way-button enable #t)
    (when (= index 0)
       (send back-button enable #f)
       (send back-all-the-way-button enable #f))
    (when (= index (length verts-and-edges))
       (send step-button enable #f)
       (send step-all-the-way-button enable #f)))

  (define back-all-the-way-button
    (new button% [parent toolbar] [label "<<"]
       [callback
        (λ (_btn _evt) 
          (set! index 0)
          (enable-and-disable-buttons!)
          (next-graph!))]))

  (define back-button
    (new button% [parent toolbar] [label "<"]
       [callback
        (λ (_btn _evt) 
          (set! index (sub1 index))
          (enable-and-disable-buttons!)
          (next-graph!))]))

  (define step-button
    (new button% [parent toolbar] [label ">"]
       [callback
        (λ (_btn _evt) 
          (set! index (add1 index))
          (enable-and-disable-buttons!)
          (next-graph!))]))

  (define step-all-the-way-button
    (new button% [parent toolbar] [label ">>"]
       [callback
        (λ (_btn _evt) 
          (set! index (length verts-and-edges))
          (enable-and-disable-buttons!)
          (next-graph!))]))

  (enable-and-disable-buttons!)
  (send frame show #t))

(define (visualize a-k-graph [title "Graph"])
  (define toplevel (new frame% [label title] [width 800] [height 600]))

  ;; Layout: toolbar on top, canvas fills the rest
  (define root (new vertical-panel% [parent toplevel]
                    [stretchable-width #t] [stretchable-height #t]))
  (define toolbar (new horizontal-panel% [parent root]
                       [stretchable-height #f] [stretchable-width #t]))

  (define the-graph-pb (to-graph-pb a-k-graph))
  (define canvas (new editor-canvas% [parent root] [editor the-graph-pb]
                      [style '(auto-hscroll auto-vscroll)]))

  ;; Examples
  (new button% [parent toolbar] [label "Re-layout"]
       [callback (λ (_btn _evt)
                   (dot-positioning the-graph-pb dot-label #f (dp-graph-directed? a-k-graph))
                   (send the-graph-pb refresh-now))])

  (new button% [parent toolbar] [label "Center View"]
       [callback (λ (_btn _evt)
                   (send the-graph-pb scroll-to 0 0)
                   (send the-graph-pb refresh-now))])

  (send toplevel show #t))

; See rosette/value-browser.rkt

(define snip-class (new snip-class%))
(define graph-editor-snip%
  (class editor-snip%
    (init-field graph-pb)
  
    (super-new [editor graph-pb] [min-height 200] [min-width 800])

    (define/override (copy) (new graph-editor-snip% [graph-pb graph-pb]))
    (define/override (write _) (void))
    (inherit set-snipclass)
    (set-snipclass snip-class)))

(define (render-graph/snip a-k-graph)

  (define the-graph-pb (to-graph-pb a-k-graph 15.0))

  (new graph-editor-snip% [graph-pb the-graph-pb]))
