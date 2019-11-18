#lang racket
 
(require rackunit
         "lang-def.rkt")

(define test-cases 
  '(
    (let* ([i (lambda (x) x)]
           [u (lambda (y)(y y))]) (i #t))
     
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
      (check-equal? (untag (tag e)) e)
      (check-equal? (untag (tag item)) item)))
  test-cases))

;; testing free-vars
(test-begin
  (for-each
   (λ (item)
     (let* ([item-tagged (tag item)])
       (check-equal? (free-vars item-tagged) '())))
   test-cases)

  (check-equal? (free-vars (tag '(let* ([lbl (lambda (x) (call/cc (lambda (k) (_k k))))]
                                        [goto (lambda (lbl) (lbl lbl))]
                                        [double (lambda (n)
                                                  (let* ([i _n]
                                                         [res 0]
                                                         [start (_lbl #f)]
                                                         [dummy (set! res (add1 (add1 res)))]
                                                         [dummy2 (set! i (sub1 _i))]
                                                         [dummy3 (if (zero? i) #f (_goto start))])
                                                    res))])
                                   (double 10))))
                '(_k _n _lbl _i _goto)))

;; testing a-normalize-tagged
(test-begin
  (for-each
   (λ (item)
     (let* ([item-tagged (tag item)]
            #;[_ (pretty-print item)]
            #;[_ (pretty-print (untag (a-normalize-tagged (tag item))))])
       (check-equal? (untag (a-normalize-tagged (tag item))) (a-normalize item))))
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

;; testting var-mutated?
(test-begin
 (check-equal? (var-mutated? 'x
                             (tag '(lambda (x) (set! x 42))))
               #f)
 (check-equal? (var-mutated? 'x
                             (tag '(let* ([i (lambda (x) x)]
                                     [u (lambda (y)(y y))]
                                     [_ (set! x 42)]) (i #t))))
               #t)
 (check-equal? (var-mutated? 'x
                             (tag '(let* ([i (lambda (x) (set! x 42))]
                                          [u (lambda (y)(y y))]) (i #t))))
               #f))
                             