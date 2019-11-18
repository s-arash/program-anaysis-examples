#lang racket

(require rackunit
         "lang-def.rkt"
         "abstract-extended-cesk-star.rkt")

(define test-cases
  '(
    (let* ([lbl (lambda (x) (call/cc (lambda (k) k)))]
         [goto (lambda (clbl) (clbl clbl))]
         [double (lambda (n)
              (let* ([i n]
                     [res 0]
                     [start (lbl #f)]
                     [dummy (set! res (add1 (add1 res)))]
                     [dummy2 (set! i (sub1 i))]
                     [dummy3 (if (zero? i) #f (goto start))])
                res))])
         (double 10))

    (let* ([x 0]
           [double #f]
           [dummy0 (set! double (lambda (n)
                     (if (zero? n)
                         x
                         (let* ([dummy1 (set! x (add1 (add1 x)))])
                           (double (sub1 n))))))]
           [res1 (double 2)]
           [dummy2 (set! x 0)])
         (double 3))
    
    (let* ([blackhole (lambda (die) (let* ([x 0]
                                         [double #f]
                                         [dummy0 (set! double (lambda (n)
                                                                (if (zero? n)
                                                                    x
                                                                    (let* ([dummy1 (set! x (add1 (add1 x)))])
                                                                      (double (sub1 n))))))]
                                         [res1 (double 2)]
                                         [dummy2 (set! x 0)])
                                    (if die (double 3) #f)))]
           [id (lambda (_f) (_f _f))]
           [func (lambda (x)
                   (let* ([f (lambda (x) (x x))]
                          [dummy3 (set! f (if x (lambda (z) z) blackhole))]
                          [g (if x (lambda (z) z) (lambda (y) (y y)))])
                     (f x)))]
           [func1 (lambda (xx) (func xx))]
           [func2 (lambda (xxx) (func1 xxx))]
           [_dummy1 (func2 #f)])
      (func2 #f))
    
    (let* ([x 0]
           [dummy (set! x 1)])
      x)

    (let* ([u (lambda(x)(x x))]
         [i (lambda(y) y)]
         [apply (lambda (f) (lambda (arg) (f arg)))]
         [dummy1 ((apply i) u)])
    (((apply u) i) 2))

    (let* ([a #f]
        [b (lambda(x)(x x))]
        [c (lambda(y) y)])
    (let* ([d #t]
          [e (lambda(r)(if r #f #t))])
      (((b c) e)(e d))))

    (let* ([foo (call/cc (lambda (k) (let* ([dummy (k 6)]) 7)))])
      foo)

    (let* ([count (lambda (n)
                    (let* ([i n]
                           [start (call/cc (lambda (k) k))]
                           [dummy2 (set! i (sub1 i))]
                           [dummy3 (if (zero? i) #f (start start))])
                      i))])
      (count 2))
    ))


(test-begin
 (set-k-cfa-k 1000)
 (for-each
  (λ (item)
    (let* ([input (parse-tagged-expr (~a item))]
           [graph (reachable (inject input))]
           [final-nodes (filter (λ (s) (set-empty? (hash-ref graph s))) (hash-keys graph))])
      (check-equal? (length final-nodes) 1)
      (match-let ([`(T (lit ,v) ,σ ,a ,t) (car final-nodes)])
        (check-equal? v (eval item (make-base-namespace))))))
  test-cases)
 (set-k-cfa-k 1))