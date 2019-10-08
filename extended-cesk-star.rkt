#lang racket

;; Predicates for CESK*

(define (proto-expr? expr? e)
  (match e
    [(? symbol?) #t]
    [`(,(? expr?) ,(? expr?)) #t]
    [`(lambda (,x) ,(? expr?)) #t]
    [`(if ,(? expr?) ,(? expr?) ,(? expr?)) #t]
    [`(set! ,(? symbol?) ,(? expr?)) #t]
    [(? const?) #t]
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

(define addr? number?)
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
    [`(ar ,(? expr? arg) ,(? env? env) ,(? addr? k)) #t]
    [`(fn ,f ,(? env?) ,(? addr? k)) #t]
    [`(if ,(? expr? then) ,(? expr? else) ,(? env? env) ,(? addr? k)) #t]
    [`(set ,(? addr? addr) ,(? addr? k)) #t]
    [else #f]))

(define (storable? v)
  (match v
    [`(clo (lambda (,(? symbol?)) ,(? expr?)) ,(? env?)) #t]
    ['(const ,(? const?)) #t]
    [(? kont?) #t]
    [else #f]))

(define (store? e)
  (and (andmap addr? (hash-keys e))
       (andmap storable? (hash-values e))))

(define (cesk*-state? state)
  (match state
    [`(,(? expr?) ,(? env?) ,(? store?) ,(? addr?)) #t]
    [else #f]))

(define (apply-builtin builtin v)
  ((hash-ref builtins builtin) v))

;;
;; Store handling
;;
(define addr 0)

;; Return a new address
(define (fresh-addr)
  (set! addr (add1 addr))
  addr)

;; Create a CESK* state from e
(define (inject e)
  (let ([a0 (fresh-addr)])
    `(,e ,(hash) ,(hash a0 'mt) ,a0)))

(define (val->storable v ρ σ)
  (match v
    [(? const?) `(const ,v)]
    [`(<--kont--> ,a) (hash-ref σ a)]
    [else `(clo ,v ,ρ)]))

;; Step relation
(define (step state)
  (match state
    ;; Variable lookup
    [`(,(? (and/c symbol? (not/c const?)) x) ,ρ ,σ ,a) 
     (match (hash-ref σ (hash-ref ρ x))
       ;; when your brain gives up ...
       [(? kont?) `((<--kont--> ,(hash-ref ρ x)) ,ρ ,σ ,a)]
       [`(clo (lambda (,x) ,body) ,ρ1)
        `((lambda (,x) ,body) ,ρ1 ,σ ,a)]
       [`(const ,v)
        `(,v (hash) ,σ ,a)])]
    ;; Application
    [`((,e0 ,e1) ,ρ ,σ ,a) #:when (not (eq? e0 '<--kont-->))
     (let* ([b (fresh-addr)]
            [new-k `(ar ,e1 ,ρ ,a)]
            [new-σ (hash-set σ b new-k)])
       `(,e0 ,ρ ,new-σ ,b))]
    ;; if expression
    [`((if ,e-cond ,e-then ,e-else) ,ρ ,σ ,a)
     (let* ([b (fresh-addr)]
            [new-k `(if ,e-then ,e-else ,ρ ,a)])
     `(,e-cond ,ρ ,(hash-set σ b new-k) ,b))]
    ;; set!
    [`((set! ,x ,e) ,ρ ,σ ,a)
     (let ([b (fresh-addr)]
           [new-kont `(set ,(hash-ref ρ x) ,a)])
           `(,e ,ρ ,(hash-set σ b new-kont) ,b))]
    ;; Lambdas and constants...
    [`(,v ,ρ ,σ ,a)
     (let ([k (hash-ref σ a)]
           [b (fresh-addr)])
       (match k
         [`(ar ,e ,ρ1 ,c)
          `(,e ,ρ1 ,(hash-set σ b `(fn ,v ,ρ ,c)) ,b)]
         [`(fn (lambda (,x) ,e) ,ρ1 ,c)
          `(,e ,(hash-set ρ1 x b) ,(hash-set σ b (val->storable v ρ σ)) ,c)]
         [`(fn (<--kont--> ,a1) ,ρ1 ,c)
          `(,v ,ρ ,σ ,a1)]
         [`(fn call/cc ,ρ1 ,c)
          (match v
            [`(lambda (,k) ,e) `(,e ,(hash-set ρ k c) ,σ ,c)]
            [`(<--kont--> ,k-a) `((lambda (x) (,v x)) ,ρ ,σ ,a)] ;η-exapnsion
            #;[`(<--kont--> ,k-a) `((<--kont--> ,a) ,ρ ,σ ,k-a)] ; from paper
            #;[`(<--kont--> ,k-a) `((<--kont--> ,c) ,ρ ,σ ,k-a)] ; what I think is right
            )]
         [`(fn ,(? builtin? builtin) ,ρ1 ,c)
          `(,(apply-builtin builtin v) ,ρ ,σ ,c)]
         [`(if ,(? expr? then) ,(? expr? else) ,(? env? ρ) ,(? addr? a))
          (let ([cond-eval (if v #t #f)])  
          `(,(if cond-eval then else) ,ρ ,σ ,a))]
         [`(set ,(? addr? addr) ,(? addr? a))
           (match (hash-ref σ addr)
             [`(clo ,e ,ρ1)   `(,e ,ρ1     ,(hash-set σ addr (val->storable v ρ σ)) ,a)]
             [`(const ,l)     `(,l ,(hash) ,(hash-set σ addr (val->storable v ρ σ)) ,a)]
             [(? kont?)       `((<--kont--> addr) (hash) ,(hash-set σ addr (val->storable v ρ σ)) ,a)])]
         [else state]))]))

(define (iterate state)
  ;(displayln "Iterating state...")
  ;(pretty-print state)
  (let ([next-state (step state)])
    (if (equal? next-state state)
        ;; Done
        (displayln (format "Done w/ evaluation. value: ~a" (car state)))
        (iterate next-state))))

(define (repl)
  (displayln "Type an expression...")
  (display "> ")
  (let ([input (read)])
    ;; Execute the expression
    (if (not (sugared-expr? input))
        (displayln "NOT a valid expression.")
        (iterate (inject (desugar input))))
    (repl)))

(repl)


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


(define example-8 ((call/cc (lambda (k) (+ 1 (call/cc k)))) 5))



