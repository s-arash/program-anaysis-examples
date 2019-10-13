#lang racket
 
(require rackunit
         "lang-def.rkt")

(define test-cases 
  '(
    ((let* ([u (lambda(x)(x x))]
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
         (double 10))

    (let* ([i 0]
           [lbl1 (call/cc (lambda (k) k))]
           [dummy (set! i (add1 i))]
           [where-will-it-go (call/cc lbl1)]
           [dummy4 (call/cc where-will-it-go)]) 
      i)

    (let* ([counter 0]
           [count-down #t]
           [dummy (set! count-down (lambda (x) (if (zero? x) x (let* ([dummy3 (set! counter (add1 counter))]) (count-down (sub1 x))))))]
           [dummy2 (count-down 5)]
           [dummy3 (count-down 6)])
      counter)))

;; checking that a-normalization and desugaring produce equivalent expressions
(test-begin
  (for-each
   (λ (item)
     (let ([item-val (eval item (make-base-namespace))])
       (check-equal? (eval (a-normalize item) (make-base-namespace)) item-val)
       (check-equal? (eval (desugar item) (make-base-namespace)) item-val)))
   test-cases))

;; checking tagging and untagging
(test-begin
 (for-each
  (λ (item)
    (let ([e (desugar item)])
      (check-equal? (untag (tag e)) e)))
  test-cases))


;; checking parser and untag
(test-begin
 (for-each
  (λ (item)
    (let* ([e (identity item)]
           [e-string (format "~a" e)])
      (check-equal?
       (untag (parse-tagged-expr e-string))
       e)))
  test-cases))
