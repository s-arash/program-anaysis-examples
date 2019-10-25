#lang racket

(provide (all-defined-out))
(require "util.rkt")
(require "lang-def.rkt")
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
    [`(ar ,(? tagged-expr? arg) ,(? env? env) ,(? addr? k)) k]
    [`(fn ,(? val? f) ,(? addr? k)) k]
    [`(if ,(? tagged-expr? then) ,(? tagged-expr? else) ,(? env? env) ,(? addr? k)) k]
    [`(set ,(? addr? addr) ,(? addr? k)) k]))

(define/contract (kont-type k)
  (kont? . -> . any/c)
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
       (andmap (lambda (v) (andmap (or/c val? kont?) (set->list v))) (hash-values e))))

(define (state? state)
  (match state
    [`(E ,expr ,(? env?) ,(? store?) ,(? addr?) ,(? time?)) #t]
    [`(T ,(? val?) ,(? store?) ,(? addr?) ,(? time?)) #t]
    [else #f]))

(define (state-kont state)
  (state? . -> . addr?)
  (if (equal? (car state) 'E) (fifth state) (fourth state)))

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