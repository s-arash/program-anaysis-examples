#lang racket
 
(require rackunit
         "lang-def.rkt")

(define test-cases 
  '(((let* ([u (lambda(x)(x x))]
         [i (lambda(y) y)]
         [apply (lambda (f) (lambda (arg) (f arg)))]
         [dummy1 ((apply i) u)])
    ((apply u) i)) 42)
    (let* ([a #f]
        [b (lambda(x)(x x))]
        [c (lambda(y) y)])
    (let* ([d #t]
          [e (lambda(r)(if r #f #t))])
      (((b c) e)(e d))))
    ((lambda (x) (let* ([res #f]) res)) #t)
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
         (double 10))))

(test-begin
  (for-each
   (λ (item)
     (let ([item-val (eval item (make-base-namespace))])
       (check-equal? (eval (a-normalize item) (make-base-namespace)) item-val)
       (check-equal? (eval (desugar item) (make-base-namespace)) item-val)))
   test-cases))

(test-begin
 (for-each
  (λ (item)
    (let ([e (desugar (car item))])
      (check-equal? (untag (tag e)) e)))
  test-cases))