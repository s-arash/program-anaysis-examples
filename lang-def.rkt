#lang racket

(provide (all-defined-out))

;; The language
(define (proto-expr? expr? e)
  (match e
    [(? symbol?) #t]
    [`(,(? expr?) ,(? expr?)) #t]
    [`(lambda (,x) ,(? expr?)) #t]
    [`(if ,(? expr?) ,(? expr?) ,(? expr?)) #t]
    [`(set! ,(? symbol?) ,(? expr?)) #t]
    [(? const?) #t]
    [else #f]))

;;it's not just theory!
(define (Y f) (λ (x) (f (Y f) x)))

(define expr? (Y proto-expr?))

(define (proto-sugared-expr? expr? e)
  (match e
    [(? ((curry proto-expr?) expr?)) #t]
    [`(λ (,x) ,(? expr? e)) #t]
    [`(let* ([,(? symbol? xs) ,(? expr? xes)]...) ,(? expr? e)) #t]
    [else #f]))

(define sugared-expr? (Y proto-sugared-expr?))

(define (desugar e)
  (match e
    [(? symbol? sym) sym]
    [`(,(? sugared-expr? f) ,(? sugared-expr? arg)) `(,(desugar f) ,(desugar arg))]
    [`(lambda (,x) ,(? sugared-expr? e)) `(lambda (,x) ,(desugar e))]
    [`(λ (,x) ,(? sugared-expr? e)) `(lambda (,x) ,(desugar e))]
    [`(if ,(? sugared-expr? cond-e) ,(? sugared-expr? then-e) ,(? sugared-expr? else-e)) `(if ,(desugar cond-e) ,(desugar then-e) ,(desugar else-e))]
    [`(set! ,(? symbol? x) ,(? sugared-expr? e)) `(set! ,x ,(desugar e))]
    [(? const? c) c]
    [(? builtin? builtin) builtin]
    [`(let* ([,(? symbol? xs) ,(? sugared-expr? xes)]...) ,(? sugared-expr? e))
     (foldr (λ (x xe e) `((lambda (,x) ,e) ,(desugar xe))) (desugar e) xs xes)]
    [else #f]))

(define (remove-at lst ind)
  (match ind
    [0 (cdr lst)]
    [_ (cons (car lst) (remove-at (cdr lst) (- ind 1)))]))

(define (iter-to-fp f) (λ (e)
  (let ([e′ (f e)])
    (if (equal? e e′)
        e
        ((iter-to-fp f) e′)))))

(define (ae? e)
    (match e
      [(? symbol?) #t]
      [(? const?) #t]
      [`(lambda (,x) ,e) #t]
      [`(λ (,x) ,e) #t]
      [else #f]))

(define (replace-free e free-var replace-val)
    (match e
      [(? symbol? x) (if (equal? x free-var) replace-val x)]
      [`(let* ([,vars ,vals]...) ,e0)
       (let ([new-vars-vals (foldl (λ (var val list-isbound)
                                     (if (cdr list-isbound)
                                         (cons (append (car list-isbound) `([,var ,val])) #t)
                                         (cons (append (car list-isbound) `([,var ,(replace-free val free-var replace-val)]))
                                               (equal? var free-var)))) (cons '() #f) vars vals)])
         `(let* ,(car new-vars-vals) ,(if (cdr new-vars-vals) e0 (replace-free e0 free-var replace-val))))]
      [`(,(? expr? e0) ,(? expr? e1)) `(,(replace-free e0 free-var replace-val) ,(replace-free e1 free-var replace-val))]
      [`(lambda (,x) ,(? expr? e0)) (if (equal? x free-var) e `(lambda (,x) ,(replace-free e0 free-var replace-val)))]
      [`(if ,(? expr? e-cond) ,(? expr? e-then) ,(? expr? e-else))
       `(if ,(replace-free e-cond free-var replace-val) ,(replace-free e-then free-var replace-val) ,(replace-free e-else free-var replace-val))]
      [`(set! ,(? symbol? x) ,(? expr? e0)) `(set! ,x ,(replace-free e0 free-var replace-val))]
      [(? const? c) c]))

(define (a-normalize-WRONG e)
  (define i 0)
  (define (fresh-id) (set! i (add1 i)) (string->symbol (format "__x~a" i)))
  
 
  (define simplify
    (iter-to-fp (λ (e)
                  (match e
                    [`(let* ([,vars1 ,vals1]...) (let* ([,vars2 ,vals2]...) ,e))
                     `(let* ,(map (λ (var val) `[,var ,val]) (append vars1 vars2) (append vals1 vals2)) ,(simplify e))]
                    [`(,(? expr? e0) ,(? expr? e1)) `(,(simplify e0) ,(simplify e1))]
                    [`(lambda (,x) ,(? expr? e)) `(lambda (,x) ,(simplify e))]
                    [`(if ,(? expr? e-cond) ,(? expr? e-then) ,(? expr? e-else)) `(if ,(simplify e-cond) ,(simplify e-then) ,(simplify e-else))]
                    [`(set! ,(? symbol? x) ,(? expr? e)) `(set! ,x ,(simplify e))]
                    [`(let* ,bindings ,e) `(let* ,bindings ,(simplify e))]
                    [`(lambda (,x) ,e0) `(lambda (,x) ,(simplify e0))]
                    [`(λ (,x) ,e0) `(λ (,x) ,(simplify e0))]
                    [x x]))))
  
  (define remove-unnecessary-bindings
    (iter-to-fp
     (λ (e) (match e
              [`(let* ([,vars ,vals]...) ,e0)
               (let ([ind (index-where vals ae?)])
                 (if (equal? ind #f)
                     e
                     (let* ([var (list-ref vars ind)]
                            [val (list-ref vals ind)]
                            [new-vars (remove-at vars ind)]
                            [new-vals (remove-at vals ind)])
                       (if (= (length new-vars) 0)
                           (replace-free e0 var val)
                           `(let* ,(map (λ (var val) `[,var ,val]) new-vars new-vals) ,(replace-free e0 var val))))))]
              [e e]))))

         

  (define (a-normalize e)
    (match e
      [`(let* ([,vars ,vals]...) ,e0)
          `(let* ,(map (λ (var val) `[,var ,(a-normalize val)]) vars vals) ,(a-normalize e0))]
      [`(lambda (,x) ,e) `(lambda (,x) ,(a-normalize e))]
      [(? symbol? x) x]
      [`((lambda (,x) ,e) ,e1) #:when (not (ae? e1))
                               (let ([id (fresh-id)])
                                 `(let* ([,id ,(a-normalize e1)]) (lambda (,x) ,(a-normalize e)) ,id))]
      [`((lambda (,x) ,e) ,e1) `((lambda (,x) ,(a-normalize e)) ,(a-normalize e1))]
      [`(,(? symbol? x) ,e1) #:when (not (ae? e1))
                            (let ([id (fresh-id)])
                              `(let* ([,id ,(a-normalize e1)]) (,x ,id)))]
      [`(,(? symbol? x) ,e) `(,x ,(a-normalize e))]
      [`(,e1 ,e2) (let ([e1-id (fresh-id)]
                        [e2-id (fresh-id)])
                    (remove-unnecessary-bindings `(let* ([,e1-id ,(a-normalize e1)]
                                                         [,e2-id ,(a-normalize e2)])
                                                    (,e1-id ,e2-id))))]
      [`(if ,e-cond ,e-then ,e-else)
       (let ([id-cond (fresh-id)])
         (remove-unnecessary-bindings `(let* ([,id-cond ,(a-normalize e-cond)])
                                         (if ,id-cond ,(a-normalize e-then) ,(a-normalize e-else)))))]
      [`(set! ,x ,e0)
       (let ([id (fresh-id)])
         (remove-unnecessary-bindings `(let* ([,id ,(a-normalize e0)]) (set! ,x ,id))))]
      [(? const? c) c]))
  (simplify (a-normalize e)))


(define (a-normalize e)
  (define i 0)
  (define (fresh-id) (set! i (add1 i)) (string->symbol (format "__x~a" i)))
  
  ;; Merges consecutive let*s together
  (define simplify
    (iter-to-fp (λ (e)
                  (match e
                    [`(let* ([,vars1 ,vals1]...) (let* ([,vars2 ,vals2]...) ,e))
                     `(let* ,(map (λ (var val) `[,var ,val]) (append vars1 vars2) (append vals1 vals2)) ,(simplify e))]
                    [`(,(? expr? e0) ,(? expr? e1)) `(,(simplify e0) ,(simplify e1))]
                    [`(lambda (,x) ,(? expr? e)) `(lambda (,x) ,(simplify e))]
                    [`(if ,(? expr? e-cond) ,(? expr? e-then) ,(? expr? e-else)) `(if ,(simplify e-cond) ,(simplify e-then) ,(simplify e-else))]
                    [`(set! ,(? symbol? x) ,(? expr? e)) `(set! ,x ,(simplify e))]
                    [`(let* ,bindings ,e) `(let* ,bindings ,(simplify e))]
                    [`(lambda (,x) ,e0) `(lambda (,x) ,(simplify e0))]
                    [`(λ (,x) ,e0) `(λ (,x) ,(simplify e0))]
                    [x x]))))
  
  (define remove-unnecessary-bindings
    (iter-to-fp
     (λ (e) (match e
              [`(let* ([,vars ,vals]...) ,e0)
               (let ([ind (index-where vals ae?)])
                 (if (equal? ind #f)
                     e
                     (let* ([var (list-ref vars ind)]
                            [val (list-ref vals ind)]
                            [new-vars (remove-at vars ind)]
                            [new-vals (remove-at vals ind)])
                       (if (= (length new-vars) 0)
                           (replace-free e0 var val)
                           `(let* ,(map (λ (var val) `[,var ,val]) new-vars new-vals) ,(replace-free e0 var val))))))]
              [e e]))))

         
  (define (expr->ae e k)
    (match (a-normalize e)
      [(? ae? ae) (k ae)]
      [`(let* ,bindings ,e0)
       (let ([e0-var (fresh-id)])
         `(let* (,@bindings [,e0-var ,e0])
            ,(k e0-var)))]
      [`(let* ,bindings ,(? ae? ae0))
       `(let* ,bindings ,(k ae0))]
      [e-norm (let ([e-var (fresh-id)])
              `(let* ([,e-var ,e-norm]) ,(k e-var)))]))  
  
  (define (a-normalize e)
    (match e
      [`(let* ([,vars ,vals]...) ,e0)
       (if (equal? vars '())
           (a-normalize e0)
           (expr->ae (car vals)
                     (λ (val-ae)
                       `(let* ([,(car vars) ,val-ae]) ,(a-normalize `(let* ,(map (λ (var val) `[,var ,val]) (cdr vars) (cdr vals))
                                                                       ,e0))))))] 
      [`(lambda (,x) ,e) `(lambda (,x) ,(a-normalize e))]
      [(? ae? ae) ae]
      [`(,e0 ,e1) (expr->ae e0 (λ (ae0) (expr->ae e1 (λ (ae1) `(,ae0 ,ae1)))))]

      [`(if ,e-cond ,e-then ,e-else)
       (expr->ae e-cond (λ (ae-cond) `(if ,ae-cond ,(a-normalize e-then) ,(a-normalize e-else))))]
      [`(set! ,x ,e0)
       (expr->ae e0 (λ (e0-var) `(set! ,x ,e0-var)))]
      [(? const? c) c]))
  (simplify (a-normalize e)))

(define example-for-a-normalize
  (let* ([g ((identity identity) identity)])
    g))
    
(define (tag e)
  (define (tag e counter)
    (match e
      [(? symbol? s) `((,s . ,counter) . ,(add1 counter))]
      [`(,(? expr? l) ,(? expr? r))
       (let* ([l-t (tag l (add1 counter))]
              [r-t (tag r (cdr l-t))])
         `(((,(car l-t) ,(car r-t)) . ,counter) . ,(cdr r-t)))]
      [`(lambda (,x) ,(? expr? e))
       (let ([et (tag e (add1 counter))])
         `(((lambda (,x) ,(car et)) . ,counter) . ,(cdr et)))]
      [`(if ,(? expr? e-cond) ,(? expr? e-then) ,(? expr? e-else))
       (let* ([e-cond-t (tag e-cond (add1 counter))]
              [e-then-t (tag e-then (cdr e-cond-t))]
              [e-else-t (tag e-else (cdr e-then-t))])
         `(((if ,(car e-cond-t) ,(car e-then-t) ,(car e-else-t)) . ,counter) . ,(cdr e-else-t)))]
      [`(set! ,(? symbol? x) ,(? expr? e))
       (let ([et (tag e (add1 counter))])
         `(((set! ,x ,(car et)) . ,counter) . ,(cdr et)))]
      [(? const? c) `((,c . ,counter) . ,(add1 counter))]
      [else 'BAD-INPUT]))
  (car (tag e 1)))

(define (untag et)
  (match (car et)
    [(? symbol? x) x]
    [`(,l-t  ,r-t) `(,(untag l-t) ,(untag r-t))]
    [`(lambda (,x) ,e-t) `(lambda (,x) ,(untag e-t))]
    [`(if ,e-cond-t ,e-then-t ,e-else-t) `(if ,(untag e-cond-t) ,(untag e-then-t) ,(untag e-else-t))]
    [`(set! ,x-t ,e-t) `(set! ,(untag x-t) ,(untag e-t))]
    [(? const? c) c]
    [else 'BAD-INPUT]))

(define (tagged-expr? et)
  (define (helper e)
    (match e
      [(cons head tail) (and (helper head) (helper tail))]
      [sym (not (equal? sym 'BAD-INPUT))]))
  (helper (untag et)))

(define (builtin? x) (hash-ref builtins x #f))
(define const? (or/c boolean? number? builtin?))
(define builtins (hash
                  'add1 add1
                  'sub1 sub1
                  'not not
                  'zero? zero?
                  'call/cc 'call/cc))


;; Examples
(define id-id '((lambda (x) x) (lambda (y) y)))
(define example-omega '((lambda (x) (x x)) (lambda (y) (y y))))

;; This should not terminate
(define sugared-example
  '(let* ([f #f]
          [dummy (set! f (lambda (x) (f x)))])
     (f #f)))
(define sugared-example-2 '(let* ([id (lambda (x) x)]) (id (id id))))
(define sugared-example-3 '((lambda (x) (let* ([res #f]) res)) #t))
(define example-4
  (let* ([counter 0]
         [count-down #t]
         [dummy (set! count-down (lambda (x) (if (zero? x) x (let* ([dummy3 (set! counter (add1 counter))]) (count-down (sub1 x))))))]
         [dummy2 (count-down 5)]
         [dummy3 (count-down 6)])
    counter))
(define example-5 (let* ([foo (call/cc (lambda (k) (let* ([dummy (k 6)]) 7)))])
                    foo))
(define example-6
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
         (double 10)))

(define exmaple-7
  (let* ([i 0]
         [lbl1 (call/cc (lambda (k) k))]
         [dummy (set! i (add1 i))]
         [where-will-it-go (call/cc lbl1)]
         [dummy4 (call/cc where-will-it-go)]
         ) 
  i))
