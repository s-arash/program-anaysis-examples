#lang racket

(require data/gvector)

;; Predicates for CESK*

(define (expr? e)
  (match e
    [(? symbol?) #t]
    [`(,(? expr?) ,(? expr?)) #t]
    [`(lambda (,x) ,(? expr?)) #t]
    [else #f]))

(define addr? (λ (a) #t))

(define time? number?)

(define (env? e)
  (and (andmap (lambda (key) (symbol? key)) (hash-keys e))
       (andmap addr? (hash-values e))))

(define (kont? k)
  (match k
    ['mt #t]
    [`(ar ,(? expr?) ,(? env?) ,(? addr?)) #t]
    [`(fn (lambda (,x) ,(? expr?)) ,(? env?) ,(? addr?)) #t]
    [else #f]))

(define (clo? c)
  (match c
    [`(clo (lambda (,x) ,(? expr?)) ,(? env?)) #t]
    [else #f]))

(define (storable? v)
  (match v
    [(? clo?) #t]
    [(? kont?) #t]))

(define (store? e)
  (and (andmap addr? (hash-keys e))
       (andmap (lambda (v) (andmap storable? v)) (hash-values e))))

(define (cesk*-state? state)
  (match state
    [`(,(? expr?) ,(? env?) ,(? store?) ,(? addr?) ,(? time?)) #t]
    [else #f]))

(define (tick state kont)
  (match state [`(,expr ,env ,store ,kont ,time) (remainder (+ time 1) 1)]))

(define (tick-0cfa state kont) 'nothing)

(define (alloc state kont)
  (match state [`(,expr ,env ,store ,kont ,time) time]))

;; Value allocator for 0CFA
(define (alloc-v-0cfa x) x)

;; Continuation allocator for 0CFA
(define (alloc-k state) (match state [`(,expr ,env ,store ,kont ,time) expr]))

;; Create a CESK* state from e
(define (inject e)
  `(,e ,(hash) ,(hash 0 (set 'mt)) 0 'nothing))

;; Examples
(define id-id '((lambda (x) x) (lambda (x) x)))
(define omega '((lambda (x) (x x)) (lambda (x) (x x))))

;; store utils
(define (store-ref-val σ a)
  (stream-filter clo? (hash-ref σ a)))

(define (store-ref-kont σ a)
  (stream-filter kont? (hash-ref σ a)))

(define (store-set σ a v)
  (hash-set σ a (set-add (hash-ref σ a set) v)))

;; Step relation
(define (step state)
  (match state
    ;; Variable lookup
    [`(,(? symbol? x) ,ρ ,σ ,a ,t)
      (stream-flatmap 
        (lambda (val) 
          (stream-map 
            (lambda (k) (match val
                [`(clo ,v ,ρ1)
                 `(,v ,ρ1 ,σ ,a nothing #;,(tick state k))]))
            (store-ref-kont σ a)))   
        (store-ref-val σ (hash-ref ρ x)))]
    ;; Application
    [`((,e0 ,e1) ,ρ ,σ ,a ,t)
    (stream-map (lambda (k)
     (let* ([b (alloc-k state)]
            [new-k `(ar ,e1 ,ρ ,a)]
            [new-σ (store-set σ b new-k)])
       `(,e0 ,ρ ,new-σ ,b nothing #;,(tick state k))))
    (store-ref-kont σ a))]
    ;; Lambdas...
    [`(,v ,ρ ,σ ,a ,t)
      (stream-flatmap (lambda (k)
        (let ([b-k (alloc-k state)])
          (match k
            [`(ar ,e ,ρ1 ,c)
              (stream `(,e ,ρ1 ,(store-set σ b-k `(fn ,v ,ρ ,c)) ,b-k nothing #;,(tick state k)))]
            [`(fn (lambda (,x) ,e) ,ρ1 ,c)
             (let ([b-v (alloc-v-0cfa x)])
               (stream `(,e ,(hash-set ρ1 x b-v) ,(store-set σ b-v `(clo ,v ,ρ)) ,c nothing)))]
            [else empty-stream])))
        (store-ref-kont σ a))]))

(define (iterate state)
  (displayln "Iterating state...")
  (pretty-print state)
  (let ([next-state (stream->list (step state))])
    (if (equal? next-state '())
        ;; Done
        (displayln "Done w/ evaluation.")
        (iterate (car next-state)))))

;; Fine all states reachable from state, generate a graph whose root
;; is state.
(define (gen-graph state)
  ;; h is a hash from states -> set of states
  ;; Idea: each iteration, we map the step function over the keys of `h` and add any newly-discovered states
  (define (iterate-hash h)
    (let* ([next-states (map (lambda (state) (cons state (list->set (stream->list (step state))))) (hash-keys h))]
           [next-graph 
            (foldl
             (match-lambda** [((cons state next-states) h)
                              (let* ([graph-after-connecting (hash-set h state (set-union (hash-ref h state) next-states))]
                                     [graph-after-adding-states
                                      (foldl (lambda (next-state h)
                                               (if (hash-has-key? h next-state) h (hash-set h next-state (set))))
                                             graph-after-connecting
                                             (set->list next-states))])
                                graph-after-adding-states)])
             h
             next-states)])
      (if (equal? next-graph h)
          ;; No more 
          h
          ;; Otherwise, keep going...
          (iterate-hash next-graph))))
  (iterate-hash (hash state (set))))

;; Convert a hash of the type e -> set(e) into a DOT digraph
(define (graphify h)
  (define lines
    (flatten (hash-map h (lambda (key value) (map (lambda (v) (format "\"~a\" -> \"~a\"" key v)) (set->list value))))))
  (displayln "digraph {")
  (for ([line lines]);
    (displayln (format "  ~a" line)))
  (displayln "}"))

;; Finds all states reachable from state?
(define (reachable state)
  (define ind 0)
  (define known-states (mutable-set state))
  (define states (gvector state))
  (define (loop)
    (define current (gvector-ref states ind))
    (for ([s (step current)])
      (when (not (set-member? known-states s))
          (begin
            (gvector-add! states s)
            (set-add! known-states s))))
    (set! ind (+ ind 1))
    (when (< ind (gvector-count states)) (loop)))
  (loop)
  known-states)
  

;; helper functions
(define (stream-flatmap f s)
  (stream-fold (lambda (accu s) (stream-append accu (f s))) empty-stream s))

(define (stream-flatten ss)
  ;; WTF? NOW fold behaves normally??
  (stream-fold (lambda (accu s) (stream-append accu s)) empty-stream ss))

;; repl
(define (repl)
  (displayln "Type an expression...")
  (display "> ")
  (let ([input (read)])
    ;; Execute the expression
    (pretty-print (set-count (reachable (inject input))))
    ;(pretty-print (gen-graph (inject input)))
    (graphify (gen-graph (inject input)))
    (repl)))

(repl)

(stream->list (step `(x #hash((x . x))
    #hash(
          (0 . ,(set 'mt))
          ((x x) . ,(set '(ar x #hash((x . x)) 0)))
          ((lambda (x) (x x)) . ,(set '(fn (lambda (x) (x x)) #hash() 0)))
          (((lambda (x) (x x)) (lambda (x) (x x))) . ,(set '(ar (lambda (x) (x x)) #hash() 0)))
          (x . ,(set '(clo (lambda (x) (x x)) #hash()))))
    (x x)
    nothing)))