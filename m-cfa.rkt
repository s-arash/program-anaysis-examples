#lang racket

(require data/gvector)
(require json)
(require "viz-tool-output.rkt")
(require "abstract-extended-cesk-star-helpers.rkt")
(require "lang-def.rkt")
(require "util.rkt")

(provide (all-defined-out))

(define/contract (ae->vals ae ρ σ)
  (tagged-ae? env? store? . -> . (set/c val?))
  (match ae
    [`((lambda (,x) ,e0) . ,_) (set `(clo ,ae ,ρ))]
    [`(,(? builtin? b) . ,_) (set `(builtin ,b))]
    [`(,(? (or/c boolean? number?) lit) . ,_) (set `(lit ,lit))]
    [`(,(? symbol? x) . ,_)
     (for/set ([v (hash-ref σ (hash-ref ρ x))])
       (if (kont? v)
           `(kont ,(hash-ref ρ x))
           v))]))

(define k-cfa-k 1)
(define (set-k-cfa-k k) (set! k-cfa-k k))

(define strategy-is-a-normalization #f)
(define (transform-input-tagged e) (if strategy-is-a-normalization (a-normalize-tagged e) e))

; My hackery...
(define/contract (tick state kont)
  (state? (nullable kont?) . -> . time?)
  (let ([res (match state
    [`(E ,(? tagged-ae?) ,ρ ,σ ,a (,l . ,δ)) 
      #;`(,l . ,δ) 
      `(,l . ,(if (empty? δ) δ (cdr δ)))]
    [`(E ((,e0 ,e1) . ,l) ,ρ ,σ ,a (,ls . ,δ)) (cons (cons l ls) δ)]
    [`(E ((if ,e-cond ,e-then ,e-else) . ,l) ,ρ ,σ ,a (,ls . ,δ)) (cons (cons l ls) δ)]
    [`(E ((set! ,x ,e) . ,l) ,ρ ,σ ,a (,ls . ,δ)) (cons (cons l ls) δ)]
    [`(T ,v ,σ ,a (,l . ,δ))
     (match kont
       [`(ar ,e ,ρ1 ,c) `(,l . ,δ)]
       [`(fn ,fn ,c)
        (if (or (equal? l '()) (equal? l '•))
            (cons l (take-at-most δ k-cfa-k))  
            (cons (cdr l) (take-at-most (cons (car l) δ) k-cfa-k)))]
       
       [`(if ,then ,else ,(? env? ρ) ,(? addr? a)) `(,l . ,δ)]
       [`(set ,(? addr? addr) ,(? addr? a)) `(,l . ,δ)]
       ['mt `(,l . ,δ)])])])
    (when (not (time? res)) (error (format "not a valid time: ~v \nstate: ~v \nkont:~a" res state kont)))
    res))

(define (val-truthy v)
  (match v
    ['(lit #f) #f]
    [else #t]))

;; allocator for k-CFA
(define/contract (alloc state kont)
  (state? kont? . -> . addr?)
  (match state
    [`(E (((,e0 . ,l) ,e1) . ,l1) ,ρ ,σ ,a (,_ . ,δ)) (cons l δ)]
    [`(E ((if (,e-cond . ,e-cond-l) ,e-then ,e-else) . ,l1) ,ρ ,σ ,a (,_ . ,δ)) (cons e-cond-l δ)]
    [`(E ((set! ,_ (,e0 . ,l)) . ,l1) ,ρ ,σ ,a (,_ . ,δ)) (cons l δ)]
    [`(T ,v ,σ ,a (,_ . ,δ))
     (match kont
       [`(ar (,e . ,l1) ,ρ1 ,c) (cons l1 δ)]
       [`(fn (clo ((lambda (,x) ,e) . ,l1) ,ρ1) ,c) (cons x δ)]
       [`(if (,then . ,then-l) (,else . ,else-l) ,(? env? ρ) ,(? addr? a)) (cons (if (val-truthy v) then-l else-l) δ)])]))

;; the old kont allocator
#;(define (alloc-k state kont target-expr target-env)
  (alloc state kont))

;; p4f kont allocator
(define (alloc-k state kont target-expr target-env)
  (cons target-expr target-env))

(define (alloc-var var state)
  (match state
    [`(T ,v ,σ ,a (,_ . ,δ)) (cons var δ)]))

(define (apply-builtin builtin v)
  ((hash-ref builtins builtin) v))

;; Create a CESK* state from e
(define/contract (inject e)
  (tagged-expr? . -> . state?)
  (let ([a0 '(0 . ())]
        [init-time (if strategy-is-a-normalization '(• . ()) '(() . ()))])
    `(E ,e ,(hash) ,(hash a0 (set 'mt)) ,a0 ,init-time)))


;; env-copy handler
;; produces a set of pairs of new envs and new stores
(define (env-copy-branching ρ-as-list σ state kont)
  (match ρ-as-list 
    ['() (set (cons (hash) σ))]
    [(cons var-addr rest)
      (for*/set ([rest-copy (env-copy-branching rest σ state kont)]
                 [val (store-ref-val σ (cdr var-addr))])
        (let ([ρ′ (car rest-copy)]
              [σ′ (cdr rest-copy)]
              [new-addr ('?)])
          (cons (hash-set ρ′ (car var-addr) new-addr) (store-set σ′ new-addr val))))]))

(define (env-copy ρ σ state kont)
  (foldl (match-lambda** [(var (cons ρ′ σ′))
                          (let ([new-addr (alloc-var var state)])
                            (cons (hash-set ρ′ var new-addr) (hash-set σ′ new-addr (hash-ref σ′ (hash-ref ρ var)))))])
         (cons (hash) σ)
         (hash-keys ρ)))

;; store utils
(define (store-ref-val σ a)
  (stream-filter (not/c kont?) (hash-ref σ a)))

(define (store-ref-kont σ a)
  (stream-filter kont? (hash-ref σ a)))

(define (store-set σ a v)
  (hash-set σ a (set-add (hash-ref σ a set) v)))

;; Step relation
(define/contract (step state)
  (state? . -> . (set/c state?))
  #;(validate-state state)      
  (match state
    ;; Atomic expression 
    [`(E ,(? tagged-ae? ae) ,ρ ,σ ,a ,t) 
     (for*/set ([val (ae->vals ae ρ σ)])
       `(T ,val ,σ ,a ,(tick state 'null)))]
    ;; Application
    [`(E ((,e0 ,e1) . ,l) ,ρ ,σ ,a ,t)
      (for*/set ([k (store-ref-kont σ a)])
        (let* ([kb (alloc-k state k e0 ρ)]
               [new-k `(ar ,e1 ,ρ ,a)]
               [new-σ (store-set σ kb new-k)])
          `(E ,e0 ,ρ ,new-σ ,kb ,(tick state k))))]
    ;; Let binding
    [`(E ((let ([,x ,e0]) ,e1) . ,l) ,ρ ,σ ,a ,t)
     (for*/set ([k (store-ref-kont σ a)])
       (let* ([kb (alloc-k state k e0 ρ)]
              [new-k `(let ,x ,e1 ,ρ ,a)]
              [new-σ (store-set σ kb new-k)])
         `(E ,e0 ,ρ ,new-σ kb ,(tick state k))))]
    ;; if expression
    [`(E ((if ,e-cond ,e-then ,e-else) . ,l) ,ρ ,σ ,a ,t)
     (for*/set ([k (store-ref-kont σ a)])
       (let* ([kb (alloc-k state k e-cond ρ)]
              [new-k `(if ,e-then ,e-else ,ρ ,a)])
         `(E ,e-cond ,ρ ,(store-set σ kb new-k) ,kb ,(tick state k))))]
    ;; set!
    [`(E ((set! ,x ,e) . ,l) ,ρ ,σ ,a ,t)
     (for*/set ([k (store-ref-kont σ a)])
       (let ([kb (alloc-k state k e ρ)]
             [new-kont `(set ,(hash-ref ρ x) ,a)])
         `(E ,e ,ρ ,(store-set σ kb new-kont) ,kb ,(tick state k))))]
    ;; Lambdas and constants...
    [`(T ,v ,σ ,a ,t)
     (set-remove
      (for*/set ([k (store-ref-kont σ a)])
        (match k
          [`(ar ,e ,ρ1 ,c)
           (let ([b-k (alloc-k state k e ρ1)])
             `(E ,e ,ρ1 ,(store-set σ b-k `(fn ,v ,c)) ,b-k ,(tick state k)))]
          [`(fn (clo ((lambda (,x) ,e) . ,l1) ,ρ) ,c)
           (match-let* ([(cons ρ′ σ′) (env-copy ρ σ state k)]
                        [b-v (alloc state k)])
             `(E ,e ,(hash-set ρ′ x b-v) ,(store-set σ′ b-v v) ,c ,(tick state k)))]
          [`(fn (kont ,a1) ,c)
           `(T ,v ,σ ,a1 ,(tick state k))]
          [`(fn (builtin call/cc) ,c)
           (match v
             [`(clo ((lambda (,k1) ,e) . ,_) ,ρ) `(E ,e ,(hash-set ρ k1 c) ,σ ,c ,(tick state k))]
             #;[`(kont ,k-a) `(T (clo ((lambda (x) ((,v x) . NO-LABEL)) . ,l) ,ρ) ,σ ,a ,(tick state k))] ;η-exapnsion
             #;[`(kont ,k-a) `(T (kont ,a) ,σ ,k-a ,(tick state k))] ; from paper
             [`(kont ,k-a) `(T (kont ,c) ,σ ,k-a ,(tick state k))] ; what I think is right
             )]
          [`(fn (builtin ,builtin) ,c)
           (match v
             [`(lit ,lit) `(T (lit ,(apply-builtin builtin lit)) ,σ ,c ,(tick state k))])]
          [`(let ,x ,e1 ,ρ ,c)
           (match-let* ([(cons ρ′ σ′) (env-copy ρ σ state k)]
                        [b-v (alloc state k)])
             `(E ,e1 ,(hash-set ρ′ x b-v) ,(store-set σ′ b-v v) ,c ,(tick state k)))]
          [`(if ,then ,else ,(? env? ρ) ,(? addr? a))
           (let ([cond-eval (match v ['(lit #f) #f] [else #t])])  
             `(E ,(if cond-eval then else) ,ρ ,σ ,a ,(tick state k)))]
          [`(set ,(? addr? addr) ,(? addr? a))
           `(T (lit #f) ,(store-set σ addr v) ,a ,(tick state k))]
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


(define/contract (with-store state store)
  (state? store? . -> . state?)
  (match state
    [`(E ,e ,ρ ,σ ,a ,t) `(E ,e ,ρ ,store ,a ,t)]
    [`(T ,v ,σ ,a ,t) `(T ,v ,store ,a ,t)]))

(define/contract (store-of state)
  (state? . -> . store?)
  (match state
    [`(E ,e ,ρ ,σ ,a ,t) σ]
    [`(T ,v ,σ ,a ,t) σ]))

(define (combine-stores σ1 σ2)
  (foldl (λ (key-val store) (hash-set store (car key-val) (set-union (hash-ref store (car key-val) (set)) (cdr key-val)))) σ1 (hash->list σ2)))

(define/contract (reachable-widened state)
  (state? . -> . any/c)
  (define store (store-of state))
  (set! state (with-store state (hash)))
  
  (define ind 0)
  (define known-states (make-hash))
  (hash-set! known-states state (mutable-set))
  (define states (gvector state))
  (define (loop)
    (define current (gvector-ref states ind))
    (match-define `(,step-states . ,new-store) (store-widened-step current store))
    (set! store new-store)
    (for/set ([s step-states])
      (set-add! (hash-ref known-states current) s)
      (when (not (hash-has-key? known-states s))
          (begin
            (gvector-add! states s)
            (hash-set! known-states s (mutable-set)))))
    (set! ind (+ ind 1))
    (when (< ind (gvector-count states)) (loop)))
  (loop)
  (list known-states store))

;; returns a value of type (Set State, Store), where all states have an empty store
(define (store-widened-step state store) 
  (let* ([new-states (step (with-store state store))]
         [new-store (foldl (λ (state store) (combine-stores (store-of state) store)) store (set->list new-states))]
         [new-store-widened-states (for/set ([state new-states]) (with-store state (hash)))])
    (cons new-store-widened-states new-store)))

(define (analyze input-str)
  (unless (sugared-expr? (read (open-input-string input-str)))
    (displayln "NOT a valid expression."))
  (match-let*
      ([input-parsed (parse-tagged-expr input-str)]
       [input-parsed-processed (transform-input-tagged input-parsed)] 
       [input-parsed-processed (desugar-tagged input-parsed-processed)]
       [s0 (inject input-parsed-processed)]
       [(list graph-widened store-widened) (reachable-widened s0)]
       #;[graph (reachable (inject input-desugared))])
    (displayln (format "widened-states: ~a" (hash-count graph-widened)))
    #;(displayln (format "states: ~a" (hash-count graph)))
    #;(display-to-file (graphify graph) "graph.dot" #:exists 'truncate)
    #;(display-to-file (graphify graph-widened) "graph-widened.dot" #:exists 'truncate)
    (display-to-file (jsexpr->string (jsonify input-str input-parsed (with-store s0 (hash)) graph-widened store-widened
                                              #:analysis (format "~a-cfa" k-cfa-k)))
                     "aam-vis-arash-test.json" #:exists 'truncate)))

(define (repl)
  (displayln (format "[k = ~a] Type an expression..." k-cfa-k))
  (display "> ")
  (let ([input (read)])
    (analyze input))
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

;(repl) 
(analyze
 "(let* ([u (lambda (x)(x x))]
         [i (lambda (y) y)])
    (((u i) u) (u (i u))))")
