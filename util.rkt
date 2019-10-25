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
