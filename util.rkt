#lang racket

(provide (all-defined-out))

#;(define (setof c)
  (λ (set) (and (set? set)
                (andmap c (set->list set)))))

(define (setof c)
  (make-contract
   #:name 'setof
   #:projection
   (lambda (blame)
       (lambda (s)
         (for/set ([x s])
           (unless (c x)
             (raise-blame-error blame x "set element expected to be ~a, but got: ~v" c x)))
         s))
   #:first-order (λ (set) (and (set? set)
                               (andmap c (set->list set))))))

(define (set-filter f s)
  (list->set (filter f (set->list s))))

(define (nullable predicate)
  (λ (x)
    (match x
      ['null #t]
      [else (predicate x)])))

(define (take-at-most l n)
  (if (<= (length l) n) l (take l n)))

(define (remove-at lst ind)
  (match ind
    [0 (cdr lst)]
    [_ (cons (car lst) (remove-at (cdr lst) (- ind 1)))]))

(define (hash-filter-keys filter h)
  (foldl (λ (k res) (if (filter k) (hash-set res k (hash-ref h k)) res))
         (hash)
         (hash-keys h)))