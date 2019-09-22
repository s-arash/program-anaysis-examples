#lang racket

;; Predicates for CESK*

(define (expr? e)
  (match e
    [(? symbol?) #t]
    [`(,(? expr?) ,(? expr?)) #t]
    [`(lambda (,x) ,(? expr?)) #t]
    [`(if ,(? expr?) ,(? expr?) ,(? expr?)) #t]
    [`(set! ,(? symbol?) ,(? expr?)) #t]
    [(? lit?) #t]
    [(? builtin?) #t]
    [else #f]))

(define addr? number?)
(define (lit? x) (boolean? x))
(define (builtin? x) (hash-ref builtins x #f))
(define builtins (hash
                  'add1 add1
                  'not not
                  'zero? zero?))

(define (env? e)
  (and (andmap (lambda (key) (symbol? key)) (hash-keys e))
       (andmap addr? (hash-values e))))

(define (kont? k)
  (match k
    ['mt #t]
    [`(ar ,(? expr? arg) ,(? env? env) ,(? addr? k)) #t]
    [`(fn (lambda (,x) ,(? expr?)) ,(? env?) ,(? addr? k)) #t]
    [`(if ,(? expr? then) ,(? expr? else) ,(? env? env) ,(? addr? k)) #t]
    [`(set ,(? addr? addr) ,(? addr? k)) #t]))

(define (storable? v)
  (match v
    [`(clo (lambda (,x) ,(? expr?)) ,(? env?)) #t]
    [`(lit ,x) #t]
    [(? kont?) #t]))

(define (store? e)
  (and (andmap addr? (hash-keys e))
       (andmap storable? (hash-values e))))

(define (cesk*-state? state)
  (match state
    [`(,(? expr?) ,(? env?) ,(? store?) ,(? addr?)) #t]
    [else #f]))

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

;; Step relation
(define (step state)
  (match state
    ;; Variable lookup
    [`(,(? symbol? x) ,ρ ,σ ,a) 
     (match (hash-ref σ (hash-ref ρ x))
       [`(clo (lambda (,x) ,body) ,ρ1)
        `((lambda (,x) ,body) ,ρ1 ,σ ,a)]
       [`(lit ,v)
        `(,v (hash) ,σ ,a)])]
    ;; Application
    [`((,e0 ,e1) ,ρ ,σ ,a)
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
    ;; Lambdas and literals...
    [`(,v ,ρ ,σ ,a)
     (let ([k (hash-ref σ a)]
           [b (fresh-addr)])
       (match k
         [`(ar ,e ,ρ1 ,c)
          `(,e ,ρ1 ,(hash-set σ b `(fn ,v ,ρ ,c)) ,b)]
         [`(fn (lambda (,x) ,e) ,ρ1 ,c)
          `(,e ,(hash-set ρ1 x b) ,(hash-set σ b (if (lit? v) `(lit ,v) `(clo ,v ,ρ))) ,c)]
         #;[`(fn (? builtin? builtin) ,ρ1 ,c)
          `(,(apply-builtin builtin v) ,ρ ,σ ,c)]
         [`(if ,(? expr? then) ,(? expr? else) ,(? env? ρ) ,(? addr? a))
          (let ([cond-eval (if v #t #f)])  
          `(,(if cond-eval then else) ,ρ ,σ ,a))]
         [`(set ,(? addr? addr) ,(? addr? a))
           (match (hash-ref σ addr)
             [`(clo ,e ,ρ1) `(,e ,ρ1     ,(hash-set σ addr (if (lit? v) `(lit ,v) `(clo ,v ,ρ))) ,a)]
             [`(lit ,l)     `(,l ,(hash) ,(hash-set σ addr (if (lit? v) `(lit ,v) `(clo ,v ,ρ))) ,a)])]
         [else state]))]))

(define (iterate state)
  (displayln "Iterating state...")
  (pretty-print state)
  (let ([next-state (step state)])
    (if (equal? next-state state)
        ;; Done
        (displayln "Done w/ evaluation.")
        (iterate next-state))))

(define (repl)
  (displayln "Type an expression...")
  (display "> ")
  (let ([input (read)])
    ;; Execute the expression
    (iterate (inject input))
    (repl)))

(repl)

;; Examples
(define id-id '((lambda (x) x) (lambda (x) x)))
(define omega '((lambda (x) (x x)) (lambda (x) (x x))))

;(if #f (lambda (x) (x x)) (lambda (x) x))
;(if #f ((lambda (x) (x x)) (lambda (x) (x x))) (lambda (x) x))
;((lambda (x) x) #f)

;; This should not terminate
#;(let ([f #f])
  (let ([dummy (set! f (lambda (x) (f x)))])
      (f #f)))

#;((lambda (f)
   ((lambda (dummy) (f #f))
    (set! f (lambda (x) (f x)))))
 #f) 

  