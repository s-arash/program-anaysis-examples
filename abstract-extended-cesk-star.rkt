#lang racket

(require data/gvector)

;; The language
(define (proto-expr? expr? e)
  (match e
    [(? symbol?) #t]
    [`(,(? expr?) ,(? expr?)) #t]
    [`(lambda (,x) ,(? expr?)) #t]
    [`(if ,(? expr?) ,(? expr?) ,(? expr?)) #t]
    [`(set! ,(? symbol?) ,(? expr?)) #t]
    [(? const?) #t]
    [else #f]))

;;it's not just theory!
(define (Y f) (λ (x) (f (Y f) x)))

(define expr? (Y proto-expr?))

(define (proto-sugared-expr? expr? e)
  (match e
    [(? ((curry proto-expr?) expr?)) #t]
    [`(let* ([,(? symbol? xs) ,(? expr? xes)]...) ,(? expr? e)) #t]
    [else #f]))

(define sugared-expr? (Y proto-sugared-expr?))

(define (desugar e)
  (match e
    [(? symbol? sym) sym]
    [`(,(? sugared-expr? f) ,(? sugared-expr? arg)) `(,(desugar f) ,(desugar arg))]
    [`(lambda (,x) ,(? sugared-expr? e)) `(lambda (,x) ,(desugar e))]
    [`(if ,(? sugared-expr? cond-e) ,(? sugared-expr? then-e) ,(? sugared-expr? else-e)) `(if ,(desugar cond-e) ,(desugar then-e) ,(desugar else-e))]
    [`(set! ,(? symbol? x) ,(? sugared-expr? e)) `(set! ,x ,(desugar e))]
    [(? const? c) c]
    [(? builtin? builtin) builtin]
    [`(let* ([,(? symbol? xs) ,(? sugared-expr? xes)]...) ,(? sugared-expr? e))
     (foldr (λ (x xe e) `((lambda (,x) ,e) ,(desugar xe))) (desugar e) xs xes)]
    [else #f]))

(define (tag e)
  (define (tag e counter)
    (match e
      [(? symbol? s) `((,s . ,counter) . ,(add1 counter))]
      [`(,(? expr? l) ,(? expr? r))
       (let* ([l-t (tag l (add1 counter))]
              [r-t (tag r (cdr l-t))])
         `(((,(car l-t) ,(car r-t)) . ,counter) . ,(cdr r-t)))]
      [`(lambda (,x) ,(? expr? e))
       (let ([et (tag e (add1 counter))])
         `(((lambda (,x) ,(car et)) . ,counter) . ,(cdr et)))]
      [`(if ,(? expr? e-cond) ,(? expr? e-then) ,(? expr? e-else))
       (let* ([e-cond-t (tag e-cond (add1 counter))]
              [e-then-t (tag e-then (cdr e-cond-t))]
              [e-else-t (tag e-else (cdr e-then-t))])
         `(((if ,(car e-cond-t) ,(car e-then-t) ,(car e-else-t)) . ,counter) . ,(cdr e-else-t)))]
      [`(set! ,(? symbol? x) ,(? expr? e))
       (let ([et (tag e (add1 counter))])
         `(((set! ,x ,(car et)) . ,counter) . ,(cdr et)))]
      [(? const? c) `((,c . ,counter) . ,(add1 counter))]
      [else 'BAD-INPUT]))
  (car (tag e 1)))

(define (untag et)
  (match (car et)
    [(? symbol? x) x]
    [`(,l-t  ,r-t) `(,(untag l-t) ,(untag r-t))]
    [`(lambda (,x) ,e-t) `(lambda (,x) ,(untag e-t))]
    [`(if ,e-cond-t ,e-then-t ,e-else-t) `(if ,(untag e-cond-t) ,(untag e-then-t) ,(untag e-else-t))]
    [`(set! ,x-t ,e-t) `(set! ,(untag x-t) ,(untag e-t))]
    [(? const? c) c]
    [else 'BAD-INPUT]))
(define (tagged-expr? et)
  (define (helper e)
    (match e
      [(cons head tail) (and (helper head) (helper tail))]
      [sym (not (equal? sym 'BAD-INPUT))]))
  (helper (untag et)))

(define (builtin? x) (hash-ref builtins x #f))
(define const? (or/c boolean? number? builtin?))
(define builtins (hash
                  'add1 add1
                  'sub1 sub1
                  'not not
                  'zero? zero?
                  'call/cc 'call/cc))

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

(define (take-at-most l n)
  (if (<= (length l) n) l (take l n)))

(define k-cfa-k 1)

(define (tick state kont)
  (let ([res (match state
    [`((,(? (and/c symbol? (not/c const?)) x) . ,l) ,ρ ,σ ,a ,t) t]
    [`(((,e0 ,e1) . ,l) ,ρ ,σ ,a (,_ . ,δ)) #:when (not (eq? e0 '<--kont-->)) (cons l δ)]
    [`(((if ,e-cond ,e-then ,e-else) . ,l) ,ρ ,σ ,a (,_ . ,δ)) (cons l δ)]
    [`(((set! ,x ,e) . ,l) ,ρ ,σ ,a ,t) t]
    [`((,v . ,_) ,ρ ,σ ,a (,l . ,δ))
     (match kont
       [`(ar ,e ,ρ1 ,c) `(,l . ,δ)]
       [`(fn ((lambda (,x) ,e) . ,l1) ,ρ1 ,c) (cons '• (take-at-most (cons l δ) k-cfa-k))]
       [`(fn ((<--kont--> ,a1) . ,l1) ,ρ1 ,c) (cons '• (take-at-most (cons l δ) k-cfa-k))]
       [`(fn (call/cc . ,l1) ,ρ1 ,c) (cons '• (take-at-most (cons l δ) k-cfa-k))]
       [`(fn (,(? builtin? builtin) . ,l1) ,ρ1 ,c) (cons '• (take-at-most (cons l δ) k-cfa-k))]
       [`(if ,then ,else ,(? env? ρ) ,(? addr? a)) `(,l . ,δ)]
       [`(set ,(? addr? addr) ,(? addr? a)) `(,l . ,δ)]
       ['mt `(,l . ,δ)])])])
    (when (not (time? res)) (error (format "not a valid time: ~v \nstate: ~v \nkont:~a" res state kont)))
    res))

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

;; allocator for k-CFA
(define (alloc state kont)
  (match state
    [`((((,e0 . ,l) ,e1) . ,l1) ,ρ ,σ ,a (,_ . ,δ)) #:when (not (eq? e0 '<--kont-->)) (cons l δ)]
    [`(((if (,e-cond . ,e-cond-l) ,e-then ,e-else) . ,l1) ,ρ ,σ ,a (,_ . ,δ)) (cons l1 δ)]
    [`((,v . ,l) ,ρ ,σ ,a (,_ . ,δ))
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
  (match state
    [`(,expr ,env ,store ,addr ,time)
    (begin
      (when (not (env? env)) (error (format "not a valid env: ~v" env)))
      (when (not (store? store)) (error (format "not a valid store: ~v" store)))
      (when (not (addr? addr)) (error (format "not a valid addr: ~v" addr)))
      (when (not (time? time)) (error (format "not a valid time: ~v" time))))])    
  (when (not (state? state)) (pretty-print state) (error (format "not a valid state: ~v" state)) )
  (when (not (tagged-expr? (car state))) (error (format "not a tagged expr: ~v" (car state))))
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
    [`(((,e0 ,e1) . ,l) ,ρ ,σ ,a ,t) #:when (not (eq? (car e0) '<--kont-->))
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
        (let ([b-k (lambda () (alloc state k))])
          (match k
            [`(ar ,e ,ρ1 ,c)
             `(,e ,ρ1 ,(store-set σ (b-k) `(fn (,v . ,l) ,ρ ,c)) ,(b-k) ,(tick state k))]
            [`(fn ((lambda (,x) ,e) . ,l1) ,ρ1 ,c)
             (let ([b-v (alloc state k)])
               `(,e ,(hash-set ρ1 x b-v) ,(store-set σ b-v (val->storable (cons v l) ρ σ)) ,c ,(tick state k)))]
            [`(fn ((<--kont--> ,a1) . ,l1) ,ρ1 ,c)
             `((,v . ,l) ,ρ ,σ ,a1 ,(tick state k))]
            [`(fn (call/cc . ,l1) ,ρ1 ,c)
             (match v
               [`(lambda (,k) ,e) `(,e ,(hash-set ρ k c) ,σ ,c ,(tick state k))]
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
             (match (hash-ref σ addr)
               [`(clo ,e ,ρ1)   `(,e ,ρ1                            ,(store-set σ addr (val->storable (cons v l) ρ σ)) ,a ,(tick state k))]
               [`(const ,const) `(,const ,(hash)             ,(store-set σ addr (val->storable (cons v l) ρ σ)) ,a ,(tick state k))]
               [(? kont?)       `(((<--kont--> ,addr) . ,l) ,(hash) ,(store-set σ addr (val->storable (cons v l) ρ σ)) ,a ,(tick state k))])]
            [else '()])))
      '())]))

(define (iterate state)
  (displayln "Iterating state...")
  (pretty-print state)
  (let ([next-state (stream->list (step state))])
    (if (equal? next-state '())
        ;; Done
        (displayln "Done w/ evaluation.")
        (iterate (car next-state)))))

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
  
(define (repl)
  (displayln "Type an expression...")
  (display "> ")
  (let ([input (read)])
    ;; Execute the expression
    (if (not (sugared-expr? input))
        (displayln "NOT a valid expression.")
        (let ([input (tag (desugar input))])
          ;; Execute the expression
          (pretty-print (set-count (reachable (inject input))))
          ;(pretty-print (gen-graph (inject input)))
          (display-to-file (graphify (gen-graph (inject input))) "graph.dot" #:exists 'truncate)
          ;(iterate (inject (desugar input)))))
    (repl)))))

;; Examples
(define id-id '((lambda (x) x) (lambda (x) x)))
(define omega '((lambda (x) (x x)) (lambda (x) (x x))))
;; This should not terminate
(define sugared-example
  '(let* ([f #f]
          [dummy (set! f (lambda (x) (f x)))])
     (f #f)))
; desugared:
#;((lambda (f)
   ((lambda (dummy) (f #f))
    (set! f (lambda (x) (f x)))))
 #f) 
(define sugared-example-2 '(let* ([id (lambda (x) x)]) (id #t)))
(define sugared-example-3 '((lambda (x) (let* ([res #f]) res)) #t))
(define example-4
  (let* ([counter 0]
         [count-down #t]
         [dummy (set! count-down (lambda (x) (if (zero? x) x (let* ([dummy3 (set! counter (add1 counter))]) (count-down (sub1 x))))))]
         [dummy2 (count-down 5)]
         [dummy3 (count-down 6)])
    counter))
(define example-5 (let* ([foo (call/cc (lambda (k) (let* ([dummy (k 6)]) 7)))])
                    foo))
(define example-6
  (let* ([lbl (lambda (x) (call/cc (lambda (k) (k k))))]
         [goto (lambda (lbl) (lbl lbl))]
         [double (lambda (n)
              (let* ([i n]
                     [res 0]
                     [start (lbl #f)]
                     [dummy (set! res (add1 (add1 res)))]
                     [dummy2 (set! i (sub1 i))]
                     [dummy3 (if (zero? i) #f (goto start))])
                res))])
         (double 10)))

(define exmaple-7
  (let* ([i 0]
         [lbl1 (call/cc (lambda (k) k))]
         [dummy (set! i (add1 i))]
         [where-will-it-go (call/cc lbl1)]
         [dummy4 (call/cc where-will-it-go)]
         ) 
  i))
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
(define example-omega '((lambda (x) (x x)) (lambda (y) (y y))))

(define example-8 
  (let* ([u (lambda(x)(x x))]
         [i (lambda(y) y)]
         [apply (lambda (x) (lambda (y) (x y)))]
         [dummy1 ((apply i) u)])
    ((apply u) i)))

(repl)


