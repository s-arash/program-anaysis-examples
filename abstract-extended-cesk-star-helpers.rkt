#lang racket

(provide (all-defined-out))
(require "util.rkt")
(require "lang-def.rkt")
(require data/gvector)

(define (env? e)
  (and (andmap symbol? (hash-keys e))
       (andmap addr? (hash-values e))))

(define (kont? k)
  (match k
    ['mt #t]
    [`(ar ,(? tagged-expr? arg) ,(? env? env) ,(? addr? k)) #t]
    [`(fn ,(? val? f) ,(? addr? k)) #t]
    [`(if ,(? tagged-expr? then) ,(? tagged-expr? else) ,(? env? env) ,(? addr? k)) #t]
    [`(set ,(? addr? addr) ,(? addr? k)) #t]
    [else #f]))

(define/contract (kont-kont k)
  (kont? . -> . any/c)
  (match k
    ['mt #f]
    [`(ar ,(?  tagged-expr? arg) ,(? env? env) ,(? addr? k)) k]
    [`(fn ,(? val? f) ,(? addr? k)) k]
    [`(if ,(? tagged-expr? then) ,(? tagged-expr? else) ,(? env? env) ,(? addr? k)) k]
    [`(set ,(? addr? addr) ,(? addr? k)) k]))

(define/contract (kont-type k)
  (kont? . -> . symbol?)
  (match k
    ['mt 'mt]
    [else (car k)]))

(define (val? v)
  (match v
    [`(builtin ,b) #t]
    [`(kont ,k) #t]
    [`(lit ,l) #t]
    [`(clo ((lambda (,x) ,(? tagged-expr?)) . ,l) ,(? env?)) #t]
    [else #f]))

(define (store? e)
  #t
  #;(and (andmap addr? (hash-keys e))
         (andmap (lambda (v) (and (store-count? (car v))
                                  (andmap (or/c val? kont?) (set->list (cdr v))))) (hash-values e))))

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

(define (state? state)
  (match state
    [`(E ,expr ,(? env?) ,(? store?) ,(? addr?) ,(? time?)) #t]
    [`(T ,(? val?) ,(? store?) ,(? addr?) ,(? time?)) #t]
    [else #f]))

(define/contract (state-kont state)
  (state? . -> . addr?)
  (if (equal? (car state) 'E) (fifth state) (fourth state)))


;; store utils

(define (store-ref σ a)
  (cdr (hash-ref σ a)))

(define (store-ref-val σ a)
  (stream-filter (not/c kont?) (store-ref σ a)))

(define (store-ref-kont σ a)
  (stream-filter kont? (store-ref σ a)))

(define (store-values σ)
  (map cdr (hash-values σ)))
(define (store-count? x)
  (match x
    [0 #t]
    [1 #t]
    ['∞ #t]))

(define (store-count-add x y)
  (match x
    [0 y]
    [1 (match y [0 1] [_ '∞])]
    [_ '∞]))

(define (store-count-add1 x)
  (store-count-add x 1))

(define (store-set σ a v)
  (let ([store-entry (hash-ref σ a (cons 0 (set)))])
    (hash-set σ a (cons (store-count-add1 (car store-entry)) (set-add (cdr store-entry) v)))))

(define (store-update σ a v)
  (let ([store-entry (hash-ref σ a (cons 0 (set)))])
    (if (and (<= (set-count (cdr store-entry)) 1) (not (equal? (car store-entry) '∞)))
        (hash-set σ a (cons '1 (set v)))
        (store-set σ a v))))

(define/contract (combine-stores σ1 σ2)
  (store? store? . -> . store?)
  (foldl (λ (key-val store)
           (let ([store-entry (hash-ref store (car key-val) (cons 0 (set)))])
             (hash-set store (car key-val) (cons (store-count-add (car store-entry) (car (cdr key-val)))
                                                 (set-union (cdr store-entry) (cdr (cdr key-val)))))))
         σ1 (hash->list σ2)))

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

(define (validate-state state)
  (match state
    [`(E ,expr ,env ,store ,addr ,time)
    (begin
      (when (not (env? env)) (error (format "not a valid env: ~v" env)))
      (when (not (store? store)) (error (format "not a valid store: ~v" store)))
      (when (not (addr? addr)) (error (format "not a valid addr: ~v" addr)))
      (when (not (time? time)) (error (format "not a valid time: ~v" time)))
      (when (not (tagged-expr? expr)) (error (format "not a tagged expr: ~v" (car state)))))]
    [`(T ,v ,store ,addr ,time)
    (begin
      (when (not (store? store)) (error (format "not a valid store: ~v" store)))
      (when (not (addr? addr)) (error (format "not a valid addr: ~v" addr)))
      (when (not (time? time)) (error (format "not a valid time: ~v" time))))]))


;; Garbage Collection
(define/contract (kont->reachable-addrs k state)
  (kont? state? . -> . any/c)
  (define σ (store-of state))
  (match k
    ['mt
     (set)]
    [`(ar ,(? tagged-expr? arg) ,(? env? env) ,(? addr? ka))
     (set-add (expr-env->reachable-addrs arg env state) ka)]
    [`(fn ,(? val? f) ,(? addr? ka))
     (set-add (val->reachable-addrs f state) ka)]
    [`(if ,(? tagged-expr? then) ,(? tagged-expr? else) ,(? env? env) ,(? addr? ka))
     (set-union (expr-env->reachable-addrs then env state) (expr-env->reachable-addrs else env state) (set ka))]
    [`(set ,(? addr? addr) ,(? addr? ka))
     (set addr ka)]))

(define (val->reachable-addrs v state)
  (define σ (store-of state))
  (match v
    [`(builtin ,b) (set)]
    [`(kont ,ka) (set-add (addr->reachable-addrs ka state) ka)]
    [`(lit ,l) (set)]
    [`(clo ((lambda (,x) ,e) . ,l) ,env) (expr-env->reachable-addrs e env state #:ignore (list x))]))

(define (addr->reachable-addrs a state)
  (foldl (λ (stored res)
           (let ([new-addrs (match stored
                              [(? kont?) (kont->reachable-addrs stored state)]
                              [(? val?)  ( val->reachable-addrs stored state)])])
             (set-union res new-addrs)))
         (set)
         (set->list (store-ref (store-of state) a))))
                                
(define (expr-env->reachable-addrs expr env state #:ignore [ignore '()])
  (define free (free-vars expr))
  (define filtered-env (hash-filter-keys (λ (k) (and (set-member? free k) (not (member k ignore)))) env))
  (list->set (hash-values filtered-env)))

;; Returns all alive addresses of the state as a hash of the form addr -> set addr
(define (all-alive-addrs state)
  (define roots (match state
                  [`(E ,e ,ρ ,(? store?) ,k ,(? time?)) (set-add (expr-env->reachable-addrs e ρ state) k)]
                  [`(T ,v ,(? store?) ,k ,(? time?)) (set-add (val->reachable-addrs v state) k)]))
  (crystalize-graph (λ (addr) (addr->reachable-addrs addr state)) (set->list roots)))

(define/contract (gc state)
  (state? . -> . state?)
  (define alive-addrs (all-alive-addrs state))
  (define σ′ (hash-filter-keys (λ (a) (hash-has-key? alive-addrs a)) (store-of state)))
  (with-store state σ′))

(define/contract (gc-hybrid state global-store)
  (state? store? . -> . state?)
  (define alive-addrs (all-alive-addrs (with-store state (combine-stores global-store (store-of state)))))
  (define σ′ (hash-filter-keys (λ (a) (hash-has-key? alive-addrs a)) (store-of state)))
  (with-store state σ′))

(define (crystalize-graph rel roots)
  (define res (make-hash))
  (define work-list (list->gvector roots))
  (define ind 0)
  (define (loop)
    (define node (gvector-ref work-list ind))
    (define node-neighbours (rel node))
    (hash-set! res node node-neighbours)
    (for ([node′ node-neighbours])
      (when (not (hash-has-key? res node′))
        (begin
          (gvector-add! work-list node′)
          (hash-set! res node′ 'DUMMY))))
    (set! ind (add1 ind))
    (when (< ind (gvector-count work-list)) (loop)))
  (when (< ind (gvector-count work-list)) (loop))
  res)
    