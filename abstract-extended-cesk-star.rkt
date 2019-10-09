#lang racket

(require data/gvector)

(require "lang-def.rkt")

(define (env? e)
  (and (andmap (lambda (key) (symbol? key)) (hash-keys e))
       (andmap addr? (hash-values e))))

(define (kont? k)
  (match k
    ['mt #t]
    [`(ar ,(? tagged-expr? arg) ,(? env? env) ,(? addr? k)) #t]
    [`(fn ,f ,(? env?) ,(? addr? k)) #t]
    [`(if ,(? tagged-expr? then) ,(? tagged-expr? else) ,(? env? env) ,(? addr? k)) #t]
    [`(set ,(? addr? addr) ,(? addr? k)) #t]
    [else #f]))

(define (clo? c)
  (match c
    [`(clo ((lambda (,x) ,(? tagged-expr?)) . ,l) ,(? env?)) #t]
    [else #f]))

(define (storable? v)
  (match v
    [(? clo?) #t]
    [`(const (,(? const?) . ,l)) #t]
    [(? kont?) #t]
    [else #f]))

(define (store? e)
  (and (andmap addr? (hash-keys e))
       (andmap (lambda (v) (andmap storable? (set->list v))) (hash-values e))))

(define (state? state)
  (match state
    [`(,expr ,(? env?) ,(? store?) ,(? addr?) ,(? time?)) #t]
    [else #f]))

(define (validate-state state)
  (match state
    [`(,expr ,env ,store ,addr ,time)
    (begin
      (when (not (env? env)) (error (format "not a valid env: ~v" env)))
      (when (not (store? store)) (error (format "not a valid store: ~v" store)))
      (when (not (addr? addr)) (error (format "not a valid addr: ~v" addr)))
      (when (not (time? time)) (error (format "not a valid time: ~v" time)))
      (when (not (tagged-expr? (car state))) (error (format "not a tagged expr: ~v" (car state)))))]))

(define (addr? a)
  (match a
    [x #t] ; TODO REMOVE
    [`(,x . ,δ) (and (or (symbol? x) (number? x))
                    (andmap number? δ))]
    [else #f]))

(define (time? t)
  (match t
    [x #t] ; TODO REMOVE
    [`(,l . ,δ) (and (andmap number? δ)
                     (or (number? l) (equal? l '•)))]
    [else #f]))

(define (take-at-most l n)
  (if (<= (length l) n) l (take l n)))

(define k-cfa-k 0)

; The paper's definition
(define (tick state kont)
  (let ([res (match state
    [`((,(? (and/c symbol? (not/c const?)) x) . ,l) ,ρ ,σ ,a ,t) t]
    [`(((,e0 ,e1) . ,l) ,ρ ,σ ,a (,_ . ,δ)) #:when (not (eq? e0 '<--kont-->)) (cons l δ)]
    [`(((if ,e-cond ,e-then ,e-else) . ,l) ,ρ ,σ ,a (,_ . ,δ)) (cons l δ)]
    [`(((set! ,x ,e) . ,l) ,ρ ,σ ,a ,t) t]
    [`((,v . ,_) ,ρ ,σ ,a (,l . ,δ))
     (match kont
       [`(ar ,e ,ρ1 ,c) `(,l . ,δ)]
       [`(fn (,fn . ,l1) ,ρ1 ,c)      (cons '• (take-at-most (cons l δ) k-cfa-k))]
       
       [`(if ,then ,else ,(? env? ρ) ,(? addr? a)) `(,l . ,δ)]
       [`(set ,(? addr? addr) ,(? addr? a)) `(,l . ,δ)]
       ['mt `(,l . ,δ)])])])
    (when (not (time? res)) (error (format "not a valid time: ~v \nstate: ~v \nkont:~a" res state kont)))
    res))

; My hackery...
#;(define (tick state kont)
  (let ([res (match state
    [`((,(? (and/c symbol? (not/c const?)) x) . ,l) ,ρ ,σ ,a ,t) t]
    [`(((,e0 ,e1) . ,l) ,ρ ,σ ,a (,s . ,δ)) #:when (not (eq? e0 '<--kont-->)) (cons (cons l s) δ)]
    [`(((if ,e-cond ,e-then ,e-else) . ,l) ,ρ ,σ ,a (,_ . ,δ)) (cons l δ)]
    [`(((set! ,x ,e) . ,l) ,ρ ,σ ,a ,t) t]
    [`((,v . ,_) ,ρ ,σ ,a (,l . ,δ))
     (match kont
       [`(ar ,e ,ρ1 ,c) `(,l . ,δ)]
       [`(fn (,fn . ,l1) ,ρ1 ,c)
        (if (equal? l '())
            (cons l (take-at-most δ k-cfa-k))  
            (cons (cdr l) (take-at-most (cons (car l) δ) k-cfa-k)))]
       
       [`(if ,then ,else ,(? env? ρ) ,(? addr? a)) `(,l . ,δ)]
       [`(set ,(? addr? addr) ,(? addr? a)) `(,l . ,δ)]
       ['mt `(,l . ,δ)])])])
    (when (not (time? res)) (error (format "not a valid time: ~v \nstate: ~v \nkont:~a" res state kont)))
    res))

;; allocator for k-CFA
(define (alloc state kont)
  (match state
    [`((((,e0 . ,l) ,e1) . ,l1) ,ρ ,σ ,a (,_ . ,δ)) #:when (not (eq? e0 '<--kont-->)) (cons l δ)]
    [`(((if (,e-cond . ,e-cond-l) ,e-then ,e-else) . ,l1) ,ρ ,σ ,a (,_ . ,δ)) (cons l1 δ)]
    [`((,v . ,l) ,ρ ,σ ,a (,_ . ,δ)) #:when (val->storable `(,v . ,l) ρ σ)
     (match kont
       [`(ar (,e . ,l1) ,ρ1 ,c) (cons l1 δ)]
       [`(fn ((lambda (,x) ,e) . ,l1) ,ρ1 ,c) (cons x δ)]
       [`(if (,then . ,then-l) (,else . ,else-l) ,(? env? ρ) ,(? addr? a)) `(,(if v then-l else-l) . ,δ)])]))

(define (apply-builtin builtin v)
  ((hash-ref builtins builtin) v))

;; Create a CESK* state from e
(define (inject e)
  (let ([a0 '(0 . ())])
    `(,e ,(hash) ,(hash a0 (set 'mt)) ,a0 (• . ()))))

(define (val->storable v ρ σ)
  (match (car v)
    [(? const?) `(const ,v)]
    [`(<--kont--> ,a) (hash-ref σ a)]
    [`(lambda (,x) ,e) `(clo ,v ,ρ)]))

;; store utils
(define (store-ref-val σ a)
  (stream-filter clo? (hash-ref σ a)))

(define (store-ref-kont σ a)
  (stream-filter kont? (hash-ref σ a)))

(define (store-set σ a v)
  (hash-set σ a (set-add (hash-ref σ a set) v)))

;; Step relation
(define (step state)
  (validate-state state)      
  (match state
    ;; Variable lookup
    [`((,(? (and/c symbol? (not/c const?)) x) . ,l) ,ρ ,σ ,a ,t) 
     (for*/set ([val (store-ref-val σ (hash-ref ρ x))]
                [k (store-ref-kont σ a)])
       (match val
         ;; when your brain gives up ...
         [(? kont?) `((<--kont--> ,(hash-ref ρ x)) ,ρ ,σ ,a ,(tick state k))]
         [`(clo ,lam ,ρ1)
          `(,lam ,ρ1 ,σ ,a ,(tick state k))]
         [`(const ,v)
          `(,v (hash) ,σ ,a ,(tick state k))]))]
    ;; Application
    [`(((,e0 ,e1) . ,l) ,ρ ,σ ,a ,t) #:when (not (eq? e0 '<--kont-->))
      (for*/set ([k (store-ref-kont σ a)])
        (let* ([b (alloc state k)]
               [new-k `(ar ,e1 ,ρ ,a)]
               [new-σ (store-set σ b new-k)])
          `(,e0 ,ρ ,new-σ ,b ,(tick state k))))]
    ;; if expression
    [`(((if ,e-cond ,e-then ,e-else) . ,l) ,ρ ,σ ,a ,t)
     (for*/set ([k (store-ref-kont σ a)])
       (let* ([b (alloc state k)]
              [new-k `(if ,e-then ,e-else ,ρ ,a)])
         `(,e-cond ,ρ ,(store-set σ b new-k) ,b ,(tick state k))))]
    ;; set!
    [`(((set! ,x ,e) . ,l) ,ρ ,σ ,a ,t)
     (for*/set ([k (store-ref-kont σ a)])
       (let ([b (alloc state k)]
             [new-kont `(set ,(hash-ref ρ x) ,a)])
         `(,e ,ρ ,(store-set σ b new-kont) ,b ,(tick state k))))]
    ;; Lambdas and constants...
    [`((,v . ,l) ,ρ ,σ ,a ,t)
     (set-remove
      (for*/set ([k (store-ref-kont σ a)])
        (match k
          [`(ar ,e ,ρ1 ,c)
           (let ([b-k (alloc state k)])
             `(,e ,ρ1 ,(store-set σ b-k `(fn (,v . ,l) ,ρ ,c)) ,b-k ,(tick state k)))]
          [`(fn ((lambda (,x) ,e) . ,l1) ,ρ1 ,c)
           (let ([b-v (alloc state k)])
             `(,e ,(hash-set ρ1 x b-v) ,(store-set σ b-v (val->storable (cons v l) ρ σ)) ,c ,(tick state k)))]
          [`(fn ((<--kont--> ,a1) . ,l1) ,ρ1 ,c)
           `((,v . ,l) ,ρ ,σ ,a1 ,(tick state k))]
          [`(fn (call/cc . ,l1) ,ρ1 ,c)
           (match v
             [`(lambda (,k1) ,e) `(,e ,(hash-set ρ k1 c) ,σ ,c ,(tick state k))]
             #;[`(<--kont--> ,k-a) `(((lambda (x) (,v x)) . ,l) ,ρ ,σ ,a ,(tick state k))] ;η-exapnsion
             #;[`(<--kont--> ,k-a) `(((<--kont--> ,a) . NO-LABEL) ,ρ ,σ ,k-a ,(tick state k))] ; from paper
             [`(<--kont--> ,k-a) `(((<--kont--> ,c) . NO-LABEL) ,ρ ,σ ,k-a ,(tick state k))] ; what I think is right
             )]
          [`(fn (,(? builtin? builtin) . ,l1) ,ρ1 ,c)
           `((,(apply-builtin builtin v) . ,l1) ,ρ ,σ ,c ,(tick state k))]
          [`(if ,then ,else ,(? env? ρ) ,(? addr? a))
           (let ([cond-eval (if v #t #f)])  
             `(,(if cond-eval then else) ,ρ ,σ ,a ,(tick state k)))]
          [`(set ,(? addr? addr) ,(? addr? a))
           (match (hash-ref σ addr) ;TODO (hash-ref σ addr) is wrong?
             [`(clo ,e ,ρ1)   `(,e ,ρ1                            ,(store-set σ addr (val->storable (cons v l) ρ σ)) ,a ,(tick state k))]
             [`(const ,const) `(,const ,(hash)             ,(store-set σ addr (val->storable (cons v l) ρ σ)) ,a ,(tick state k))]
             [(? kont?)       `(((<--kont--> ,addr) . ,l) ,(hash) ,(store-set σ addr (val->storable (cons v l) ρ σ)) ,a ,(tick state k))])]
          [else '()]))
      '())]))

(define (iterate state)
  (displayln "Iterating state...")
  (pretty-print state)
  (let ([next-states (set->list (step state))])
    (if (equal? next-states '())
        ;; Done
        (displayln (format "Done w/ evaluation. value: ~a" (car state)))
        ;; Otherwise
        (iterate (car next-states)))))

;; Find all states reachable from state, generate a graph whose root
;; is state.
(define (gen-graph state)
  ;; h is a hash from states -> set of states
  ;; Idea: each iteration, we map the step function over the keys of `h` and add any newly-discovered states
  (define (iterate-hash h)
    (let* ([next-states (map (lambda (state) (cons state (step state))) (hash-keys h))]
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
    (flatten (hash-map h (lambda (key value) (map (lambda (v) (format "\"~a\" -> \"~a\";" key v)) (set->list value))))))
  (define output (open-output-string))
  (displayln "digraph {" output)
  (define (labeler node) (format "\"~a\"" (car node)))
  (for ([node (hash-keys h)])
    (displayln (format "  \"~a\" [label = ~a];" node (labeler node)) output))  
  (for ([line lines]);
    (displayln (format "  ~a" line) output))
  (displayln "}" output)
  (get-output-string output))

;; Finds all states reachable from state
(define (reachable state)
  (define ind 0)
  (define known-states (make-hash))
  (hash-set! known-states state (mutable-set))
  (define states (gvector state))
  (define (loop)
    (define current (gvector-ref states ind))
    (for ([s (step current)])
      (set-add! (hash-ref known-states current) s)
      (when (not (hash-has-key? known-states s))
          (begin
            (gvector-add! states s)
            (hash-set! known-states s (mutable-set)))))
    (set! ind (+ ind 1))
    (when (< ind (gvector-count states)) (loop)))
  (loop)
  known-states)


(define (with-store state store)
  (match state
    [`(,e ,ρ ,σ ,a ,t) `(,e ,ρ ,store ,a ,t)]))
(define (combine-stores σ1 σ2)
  (foldl (λ (key-val store) (hash-set store (car key-val) (set-union (hash-ref store (car key-val) (set)) (cdr key-val)))) σ1 (hash->list σ2)))

(define (reachable-widened state)
  (define store (third state))
  (set! state (with-store state (hash)))
  
  (define ind 0)
  (define known-states (make-hash))
  (hash-set! known-states state (mutable-set))
  (define states (gvector state))
  (define (loop)
    (define current (gvector-ref states ind))
    (match-define `(,step-states . ,new-store) (store-widened-step current store))
    (set! store new-store)
    (for ([s step-states])
      (set-add! (hash-ref known-states current) s)
      (when (not (hash-has-key? known-states s))
          (begin
            (gvector-add! states s)
            (hash-set! known-states s (mutable-set)))))
    (set! ind (+ ind 1))
    (when (< ind (gvector-count states)) (loop)))
  (loop)
  known-states)

;; returns a pair of type (Set State, Store), where all states have an empty store
(define (store-widened-step state store) 
  (let* ([new-states (step (with-store state store))]
         [new-store (foldl (λ (state store) (combine-stores (third state) store)) store (set->list new-states))]
         [new-store-widened-states (set-map new-states (λ (state) (with-store state (hash))) )])
    (cons new-store-widened-states new-store)))
  
(define (repl)
  (displayln (format "[k = ~a] Type an expression..." k-cfa-k))
  (display "> ")
  (let ([input (read)])
    ;; Execute the expression
    (if (not (sugared-expr? input))
        (displayln "NOT a valid expression.")
        (let* ([input (tag (desugar (a-normalize input)))]
              [graph-widened (reachable-widened (inject input))]
              [graph (reachable (inject input))])
          (displayln (format "states: ~a, widened-states: ~a" (hash-count graph) (hash-count graph-widened)))
          (display-to-file (graphify graph) "graph.dot" #:exists 'truncate)
          (display-to-file (graphify graph-widened) "graph-widened.dot" #:exists 'truncate)
          #;(iterate (inject input)))))
  (repl))

(define example-viz
  (let* ([u (lambda(x)(x x))]
         [i (lambda(y) y)])
    ((i i) u)))

(define example-viz-large
  (let* ([a #f]
        [b (lambda(x)(x x))]
        [c (lambda(y) y)])
    (let* ([d #t]
          [e (lambda(r)(if r #f #t))])
      (((b c) e)(e d)))))

(define example-8 
  (let* ([u (lambda(x)(x x))]
         [i (lambda(y) y)]
         [apply (lambda (f) (lambda (arg) (f arg)))]
         [dummy1 ((apply i) u)])
    ((apply u) i)))

(repl) 
