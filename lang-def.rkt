#lang racket

(require parser-tools/yacc
         parser-tools/lex
         (prefix-in : parser-tools/lex-sre))

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

(define/contract (desugar e)
  (sugared-expr? . -> . expr?)
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

(define (desugar-tagged e)
  (define no-label 'NO-LABEL)
  (match e
    [`(,(? (or/c symbol? const?) sym) . ,l) `(,sym . ,l)]
    [(? builtin? builtin) builtin]
    [`((,f ,arg) . ,l) `((,(desugar-tagged f) ,(desugar-tagged arg)) . ,l)]
    [`((lambda (,x) ,e) . ,l) `((lambda (,x) ,(desugar-tagged e)) . ,l)]
    [`((λ (,x) ,e) . ,l) `((lambda (,x) ,(desugar-tagged e)) . ,l)]
    [`((if ,cond-e ,then-e ,else-e) . ,l) `((if ,(desugar-tagged cond-e) ,(desugar-tagged then-e) ,(desugar-tagged else-e)) . ,l)]
    [`((set! ,(? symbol? x) ,e0) . ,l) `((set! ,x ,(desugar-tagged e0)) . ,l)] 
    [`((let* ([,(? symbol? xs) ,xes] ...) ,e0) . ,l)
     (let ([res-no-label (foldr (λ (x xe e) `((((lambda (,x) ,e) . ,no-label) ,(desugar-tagged xe)) . ,no-label) ) (desugar-tagged e0) xs xes)])
       `(,(car res-no-label) . ,l))]
    [else #f]))

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

(define (tagged-ae? e)
  (match e
    [`((lambda (,x) ,e0) . ,_) #t]
    [`(,(? symbol?) . ,_) #t]
    [`(,(? (or/c boolean? number?)) . ,_) #t]
    [else #f]))

(define (a-normalize e)
  (define i 0)
  (define (fresh-id) (set! i (add1 i)) (string->symbol (format "__x~a" i)))
  
  ;; Merges consecutive let*s together
  (define simplify
    (iter-to-fp (λ (e)
                  (match e
                    [`(let* ([,vars1 ,vals1]...) (let* ([,vars2 ,vals2]...) ,e))
                     `(let* ,(map (λ (var val) `[,var ,(simplify val)]) (append vars1 vars2) (append vals1 vals2)) ,(simplify e))]
                    [`(,(? sugared-expr? e0) ,(? sugared-expr? e1)) `(,(simplify e0) ,(simplify e1))]
                    [`(lambda (,x) ,(? sugared-expr? e0)) `(lambda (,x) ,(simplify e0))]
                    [`(if ,(? sugared-expr? e-cond) ,(? sugared-expr? e-then) ,(? sugared-expr? e-else)) `(if ,(simplify e-cond) ,(simplify e-then) ,(simplify e-else))]
                    [`(set! ,(? symbol? x) ,(? sugared-expr? e)) `(set! ,x ,(simplify e))]
                    [`(let* ([,vars ,vals]...) ,e) `(let* ,(map (λ (var val) `[,var ,(simplify val)]) vars vals) ,(simplify e))]
                    [`(λ (,x) ,e0) `(λ (,x) ,(simplify e0))]
                    [x x]))))

  (define (atomic-application? e)
    (match e
      [`(,(? ae?) ,(? ae?)) #t]
      [else #f]))
  (define (expr->ae e k #:atomic-application-as-ae [application-ae #f])
    (match (a-normalize e)
      [(? ae? ae) (k ae)]
      [`(,(? ae? ae0) ,(? ae? ae1)) #:when application-ae (k `(,ae0 ,ae1))] 
      [`(let* ,bindings ,e0) #:when (or (ae? e0) (and application-ae (atomic-application? e0)))
       `(let* ,bindings ,(k e0))]
      [`(let* ,bindings ,e0)
       (let ([e0-var (fresh-id)])
         `(let* (,@bindings [,e0-var ,e0])
            ,(k e0-var)))]
      [e-norm (let ([e-var (fresh-id)])
                `(let* ([,e-var ,e-norm]) ,(k e-var)))]))  
  
  (define (a-normalize e)
    (match e
      [`(let* ([,vars ,vals]...) ,e0)
       (if (equal? vars '())
           (a-normalize e0)
           (expr->ae #:atomic-application-as-ae #t (car vals)
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



(define (a-normalize-tagged e)
  (define i 0)
  (define (fresh-id [prefix "x"]) (set! i (add1 i)) (string->symbol (format "__~a~a" prefix i)))
  
  ;; Merges consecutive let*s together
  (define simplify-tagged
    (iter-to-fp (match-lambda [(cons e l0)
                  (match e
                    [`(let* ([,vars1 ,vals1]...) ((let* ([,vars2 ,vals2]...) ,e) . ,l1))
                     `((let* ,(map (λ (var val) `[,var ,(simplify-tagged val)]) (append vars1 vars2) (append vals1 vals2)) ,(simplify-tagged e)) . ,l0)]
                    [`(,(? tagged-expr? e0) ,(? tagged-expr? e1)) `((,(simplify-tagged e0) ,(simplify-tagged e1)) . ,l0)]
                    [`(lambda (,x) ,(? tagged-expr? e0)) `((lambda (,x) ,(simplify-tagged e0)) . ,l0)]
                    [`(if ,(? tagged-expr? e-cond) ,(? tagged-expr? e-then) ,(? tagged-expr? e-else))
                     `((if ,(simplify-tagged e-cond) ,(simplify-tagged e-then) ,(simplify-tagged e-else)) . ,l0)]
                    [`(set! ,(? symbol? x) ,(? tagged-expr? e)) `((set! ,x ,(simplify-tagged e)) . ,l0)]
                    [`(let* ([,vars ,vals]...) ,e) `((let* ,(map (λ (var val) `[,var ,(simplify-tagged val)]) vars vals) ,(simplify-tagged e)) . ,l0)]
                    [`(λ (,x) ,e0) `((λ (,x) ,(simplify-tagged e0)) . ,l0)]
                    [x `(,x . ,l0)])])))

  (define (tagged-atomic-application? e)
    (match e
      [`((,(? tagged-ae?) ,(? tagged-ae?)) . ,l) #t]
      [else #f]))
  (define (tagged-expr->ae te k #:atomic-application-as-ae [application-ae #f])
    (unless (tagged-expr? te) (error "not a tagged expr: " te))
    (match (a-normalize-tagged te)
      [(? tagged-ae? ae) (k ae)]
      [`((,(? tagged-ae? ae0) ,(? tagged-ae? ae1)) . ,l) #:when application-ae (k `((,ae0 ,ae1) . ,l))] 
      [`((let* ,bindings ,e0) . ,l) #:when (or (tagged-ae? e0) (and application-ae (tagged-atomic-application? e0)))
       `((let* ,bindings ,(k e0)) . ,l)]
      [`((let* ,bindings ,e0) . ,l)
       (let ([e0-var (fresh-id)])
         `((let* (,@bindings [,e0-var ,e0])
            ,(k `(,e0-var . NO-LABEL))) . ,l))]
      [`(,e-norm . ,l) (let ([e-var (fresh-id)])
                `((let* ([,e-var (,e-norm . ,l)]) ,(k `(,e-var . NO-LABEL))) . No-LABEL))]))  
  
  (define (a-normalize-tagged te)
    (match te
      [`((let* ([,vars ,vals]...) ,e0) . ,l)
       (if (equal? vars '())
           (a-normalize-tagged e0)
           (tagged-expr->ae #:atomic-application-as-ae #t (car vals)
                            (λ (val-ae)
                              `((let* ([,(car vars) ,val-ae])
                                 ,(a-normalize-tagged `((let* ,(map (λ (var val) `[,var ,val]) (cdr vars) (cdr vals))
                                                          ,e0) . ,l))) . NO-LABEL))))] 
      [`((lambda (,x) ,e) . ,l) `((lambda (,x) ,(a-normalize-tagged e)) . ,l)]
      [(? tagged-ae? ae) ae]
      [`((,e0 ,e1) . ,l) (tagged-expr->ae e0 (λ (ae0) (tagged-expr->ae e1 (λ (ae1) `((,ae0 ,ae1) . ,l)))))]

      [`((if ,e-cond ,e-then ,e-else) .,l)
       (tagged-expr->ae e-cond (λ (ae-cond) `((if ,ae-cond ,(a-normalize-tagged e-then) ,(a-normalize-tagged e-else)) . ,l)))]
      [`((set! ,x ,e0) . ,l)
       (tagged-expr->ae e0 (λ (e0-var) `((set! ,x ,e0-var) . ,l)))]
      [`(,(? const? c) . ,l) `(,c . ,l)]))
  (simplify-tagged (a-normalize-tagged e)))

(define example-for-a-normalize
  (let* ([g ((identity identity) identity)])
    g))

(define (cpsify e)
  (define i 0)
  (define (fresh-id [prefix "k"]) (set! i (add1 i)) (string->symbol (format "__~a~a" prefix i)))
  (define (cpsify e)
    (match e
      [`(lambda (,x) ,e0)
       (let ([k-id (fresh-id)]
             [k′-id (fresh-id)])
         `(lambda (,k-id) (,k-id (lambda (,k′-id) (lambda (,x) (,(cpsify e0) ,k′-id))))))] 
      [`(,e0 ,e1)
       (let ([k-id (fresh-id)]
             [e0-k (fresh-id "f")]
             [e1-k (fresh-id "x")])
         `(lambda (,k-id) (,(cpsify e0) (lambda (,e0-k) (,(cpsify e1) (lambda (,e1-k) ((,e0-k ,k-id) ,e1-k)))))))]
      [(? builtin? b)
       (let ([k-id (fresh-id)]
             [k′-id (fresh-id)]
             [x-id (fresh-id "x")])
         `(lambda (,k-id) (,k-id (lambda (,k′-id) (lambda (,x-id) (,k′-id (,b ,x-id)))))))]
      [(? (or/c symbol? number? boolean?) x) (let ([k-id (fresh-id)]) `(lambda (,k-id) (,k-id ,x)))]
      [`(if ,e-cond ,e-then ,e-else)
       (let ([k-id (fresh-id)]
             [e-cond-k (fresh-id "cond")])
         `(lambda (,k-id) (,(cpsify e-cond) (lambda (,e-cond-k) (if ,e-cond-k (,(cpsify e-then) ,k-id) (,(cpsify e-else) ,k-id))))) )]
      [`(set! ,x ,e0)
       (let ([k-id (fresh-id)]
             [e0-k (fresh-id "x")])
         `(lambda (,k-id) (,k-id (,(cpsify e0) (lambda (,e0-k) (set! ,x ,e0-k))))) )]))
  (cpsify e))

(define example-for-cpsify
  (((((lambda (x) x) (lambda (y) y)) (lambda (x) (lambda (y) x))) 1) 2))

(define example-for-cpsify-2
  (((lambda (x) (lambda (y) (if x x y))) #f) 42))

(define example-for-cpsify-3
  ((lambda (x) ((lambda (dummy) x) (set! x (add1 x)))) 1))


    
(define (tag e)
  (define (tag e counter)
    (match e
      [(? symbol? s) `((,s . ,counter) . ,(add1 counter))]
      [`(,(? sugared-expr? l) ,(? sugared-expr? r))
       (let* ([l-t (tag l (add1 counter))]
              [r-t (tag r (cdr l-t))])
         `(((,(car l-t) ,(car r-t)) . ,counter) . ,(cdr r-t)))]
      [`(lambda (,x) ,(? sugared-expr? e))
       (let ([et (tag e (add1 counter))])
         `(((lambda (,x) ,(car et)) . ,counter) . ,(cdr et)))]
      [`(if ,(? sugared-expr? e-cond) ,(? sugared-expr? e-then) ,(? sugared-expr? e-else))
       (let* ([e-cond-t (tag e-cond (add1 counter))]
              [e-then-t (tag e-then (cdr e-cond-t))]
              [e-else-t (tag e-else (cdr e-then-t))])
         `(((if ,(car e-cond-t) ,(car e-then-t) ,(car e-else-t)) . ,counter) . ,(cdr e-else-t)))]
      [`(set! ,(? symbol? x) ,(? sugared-expr? e))
       (let ([et (tag e (add1 counter))])
         `(((set! ,x ,(car et)) . ,counter) . ,(cdr et)))]
      [`(let* ([,vars ,vals] ...) ,e0)
       (let* ([vals-tagged (foldl (λ (val list-counter)
                                   (match-let ([(cons new-val-tagged new-counter) (tag val (cdr list-counter))])
                                     (cons (append (car list-counter) (list new-val-tagged)) new-counter)))
                                 (cons '() (add1 counter)) vals)]
              [e0-t (tag e0 (cdr vals-tagged))])
         `(((let* ,(map (λ (var val) `[,var ,val]) vars (car vals-tagged)) ,(car e0-t)) . ,counter) . ,(cdr e0-t)))]
      [(? const? c) `((,c . ,counter) . ,(add1 counter))]
      #;[else 'BAD-INPUT]))
  (car (tag e 1)))

(define (untag et)
  (match (car et)
    [(? symbol? x) x]
    [`(,l-t  ,r-t) `(,(untag l-t) ,(untag r-t))]
    [`(lambda (,x) ,e-t) `(lambda (,x) ,(untag e-t))]
    [`(λ (,x) ,e-t) `(λ (,x) ,(untag e-t))]
    [`(if ,e-cond-t ,e-then-t ,e-else-t) `(if ,(untag e-cond-t) ,(untag e-then-t) ,(untag e-else-t))]
    [`(set! ,x-t ,e-t) `(set! ,x-t ,(untag e-t))]
    [`(let* ([,vars ,vals] ...) ,e0t)
     `(let* ,(map (λ (var val) `(,var ,(untag val))) vars vals) ,(untag e0t))]
    [(? const? c) c]))

(define (tagged-expr? et)
  (with-handlers ([exn? (λ (ex) #f)])
    (begin (untag et) #t)))

(define (builtin? x) (hash-has-key? builtins x))
(define const? (or/c boolean? number? builtin?))

(define builtins (hash
                  'add1 (λ (n) (if (number? n) (add1 n) #f))
                  'sub1 (λ (n) (if (number? n) (sub1 n) #f))
                  'not not
                  'zero? (and/c number? zero?)
                  'call/cc 'call/cc))

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
      [`(,(? sugared-expr? e0) ,(? sugared-expr? e1)) `(,(replace-free e0 free-var replace-val) ,(replace-free e1 free-var replace-val))]
      [`(lambda (,x) ,(? sugared-expr? e0)) (if (equal? x free-var) e `(lambda (,x) ,(replace-free e0 free-var replace-val)))]
      [`(if ,(? sugared-expr? e-cond) ,(? sugared-expr? e-then) ,(? sugared-expr? e-else))
       `(if ,(replace-free e-cond free-var replace-val) ,(replace-free e-then free-var replace-val) ,(replace-free e-else free-var replace-val))]
      [`(set! ,(? symbol? x) ,(? sugared-expr? e0)) `(set! ,x ,(replace-free e0 free-var replace-val))]
      [(? const? c) c]))

(define/contract (free-vars e)
  (tagged-expr? . -> . (listof symbol?))

  (define (free-vars e bound-vars)
    (match e
      [`(,(? const?) . ,l) '()]
      [`(,(? symbol? x) . ,l) (if (set-member? bound-vars x) '() (list x))]
      [`((lambda (,x) ,e) . ,l) (free-vars e (set-add bound-vars x))]
      [`((if ,e-cond ,e-then ,e-else) . ,l) (append (free-vars e-cond bound-vars) (free-vars e-then bound-vars) (free-vars e-else bound-vars))]
      [`((set! ,x ,e0) . ,l) (append (if (set-member? bound-vars x) '() (list x)) (free-vars e0 bound-vars))]
      [`((,e0 ,e1) . ,l) (append (free-vars e0 bound-vars) (free-vars e1 bound-vars))]
      [`((λ (,x) ,e) . ,l) (free-vars e (set-add bound-vars x))]
      [`((let* ([,(? symbol? xs) ,xes]...) ,e-body) . ,l)
       (match-let ([(cons bound-vars free-vars0) (foldl (match-lambda** [(x xe (cons bound-vars res)) (cons (set-add bound-vars x)
                                                                                                            (append res (free-vars xe bound-vars)))])
                                                        (cons bound-vars '())
                                                        xs xes)])
         (append free-vars0 (free-vars e-body bound-vars)))]))
  
  (free-vars e (set)))

;; returns true iff (a free occurence of) x is mutated inside expression e
(define/contract (var-mutated? x e)
  (symbol? tagged-expr? . -> . boolean?)
  (match e
      [`(,(? const?) . ,l) #f]
      [`(,(? symbol? x) . ,l) #f]
      [`((lambda (,x0) ,e0) . ,l) (if (equal? x0 x) #f (var-mutated? x e0))]
      [`((if ,e-cond ,e-then ,e-else) . ,l) (or (var-mutated? x e-cond) (var-mutated? x e-then) (var-mutated? x e-else))]
      [`((set! ,x0 ,e0) . ,l) (if (equal? x0 x) #t (var-mutated? x e0))]
      [`((,e0 ,e1) . ,l) (or (var-mutated? x e0) (var-mutated? x e1))]
      [`((λ (,x0) ,e0) . ,l) (if (equal? x0 x) #f (var-mutated? x e0))]
      [`((let* ([,(? symbol? xs) ,xes]...) ,e-body) . ,l)
       (if (equal? xs '())
           (var-mutated? x e-body)
           (or (var-mutated? x (car xes))
               (and (not (equal? x (car xs))) (var-mutated? x `((let* ,(map (λ (xi xei) `[,xi ,xei]) (cdr xs) (cdr xes)) ,e-body) . ,l)))))
       ]))
;; ----- Parsing --------

(define-tokens value-tokens (SYMBOL))
(define-empty-tokens empty-tokens (OP CP OB CB EOF))
(define sexpl
  (lexer-src-pos
   [(eof) 'EOF]
   [(:or #\tab #\space #\newline) (return-without-pos (sexpl input-port))]
   [(:: (:? (char-set "#")) (:+ (:or alphabetic numeric (char-set "!$%&*/:<=>?^_~@+-.@")))) (token-SYMBOL (read (open-input-string lexeme)))]
   ["(" 'OP]
   [")" 'CP]
   ["[" 'OB]
   ["]" 'CB]))

(define sexp
  (parser
   (tokens value-tokens empty-tokens)
   (start sexp)
   (end EOF)
   (error (lambda (a b c) (void)))
   (src-pos)
   (grammar
    (sexps [() '()]
           [(sexp sexps) (cons $1 $2)])
    (sexp [(OP sexps CP) (cons $2 (cons $1-start-pos $3-end-pos))]
          [(OB sexps CB) (cons $2 (cons $1-start-pos $3-end-pos))]
          [(SYMBOL) (cons $1 (cons $1-start-pos $1-end-pos))]))))

(define (parse str)
  (define port (open-input-string str))
  (port-count-lines! port)
  (sexp (λ () (sexpl port))))

(define (shave-extra-tags e)
  (match e
    [`(((lambda . ,_) (((,x . ,_)) . ,_) ,e) . ,l) `((lambda (,x) ,(shave-extra-tags e)) . ,l)]
    [`(((if . ,_) ,e-cond ,e-then ,e-else) . ,l) `((if ,(shave-extra-tags e-cond) ,(shave-extra-tags e-then) ,(shave-extra-tags e-else)) . ,l)]
    [`(((set! . ,_) (,x . ,_) ,e) . ,l) `((set! ,x ,(shave-extra-tags e)) . ,l)]
    [`((,e1 ,e2) . ,l) `((,(shave-extra-tags e1) ,(shave-extra-tags e2)) . ,l)]
    [`(((let* . ,_) ((([,vars ,vals] . ,binding-ls) ...) . ,_) ,e) . ,l)
     `((let* ,(map (λ (var val) `(,(car var) ,(shave-extra-tags val))) vars vals) ,(shave-extra-tags e)) . ,l)]
    [x x]))

(define/contract (parse-tagged-expr str)
  (string? . -> . tagged-expr?)
  (shave-extra-tags (parse str)))



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
         [dummy4 (call/cc where-will-it-go)]) 
    i))

(define example-8
  (let* ([id (lambda (x) x)]
         [f (lambda (n)
              (let* ([_ (set! n (add1 n))])
                n))]
         [c (id #t)]
         [d (id #f)])
         (if d (f 1) (f 2))))