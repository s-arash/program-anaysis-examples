#lang racket

(require data/gvector)

;; Predicates for CESK*

(define (expr? e)
  (match e
    [(? symbol?) #t]
    [`(,(? expr?) ,(? expr?)) #t]
    [`(lambda (,x) ,(? expr?)) #t]
    [else #f]))

(define addr? number?)

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
  (match state [`(,expr ,env ,store ,kont ,time) (remainder (+ time 1) 6)]))

(define (alloc state kont)
  (match state [`(,expr ,env ,store ,kont ,time) time]))


;; Create a CESK* state from e
(define (inject e)
  `(,e ,(hash) ,(hash 0 (set 'mt)) 0 1))

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
                 `(,v ,ρ1 ,σ ,a ,(tick state k))]))
            (store-ref-kont σ a)))   
        (store-ref-val σ (hash-ref ρ x)))]
    ;; Application
    [`((,e0 ,e1) ,ρ ,σ ,a ,t)
    (stream-map (lambda (k)
     (let* ([b (alloc state k)]
            [new-k `(ar ,e1 ,ρ ,a)]
            [new-σ (store-set σ b new-k)])
       `(,e0 ,ρ ,new-σ ,b ,(tick state k))))
    (store-ref-kont σ a))]
    ;; Lambdas...
    [`(,v ,ρ ,σ ,a ,t)
      (stream-flatmap (lambda (k)
        (let ([b (alloc state k)])
          (match k
            [`(ar ,e ,ρ1 ,c)
              (stream `(,e ,ρ1 ,(store-set σ b `(fn ,v ,ρ ,c)) ,b ,(tick state k)))]
            [`(fn (lambda (,x) ,e) ,ρ1 ,c)
              (stream `(,e ,(hash-set ρ1 x b) ,(store-set σ b `(clo ,v ,ρ)) ,c ,(tick state k)))]
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
    (repl)))

(repl)