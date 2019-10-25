#lang racket

(require json)
(require parser-tools/lex)
(require racket/hash)
(require "lang-def.rkt")
(require "abstract-extended-cesk-star-helpers.rkt")

(provide (all-defined-out))

(define (make-ids xs)
  (define id 0)
  (define (gen-id)
    (set! id (add1 id))
    (number->string (sub1 id)))
  (foldl (λ (x hash) (hash-set hash x (gen-id))) (hash) xs))

(define (number->symbol n)
  (string->symbol (number->string n)))

;SCREW RACKET's STUPID FUCKING FLATTEN
;WHAT KIND OF A DERANGED IDIOT WRITES A FLATTEN FUNCTION LIKE THAT?
(define (flatten ll)
  (foldl (λ (l res)
           (append res l))
         '() ll))

(define (ast-json&expr-pos-ids tagged-expr)
  (define expr-ids (make-hash))
  (define id 0)
  (define (gen-id te)
    (set! id (add1 id))
    (hash-set! expr-ids (cdr te) (number->string id))
    (number->string id))

  (define (ast-json tagged-expr)
    (define (add-pos h l)
      (match l
        [(cons (position _ sl sc) (position _ el ec))
         (hash-set* h
                    'start (list (sub1 sl) sc)
                    'end (list (sub1 el) ec))]
        [else h]))
    (define l (cdr tagged-expr))
    (define node-id (string->symbol (gen-id tagged-expr)))
    (define node-json (add-pos (hash 'tok (~a (untag tagged-expr))) l))
    
    (match (car tagged-expr)
      [(? symbol? x) (hash node-id (add-pos (hash 'tok (symbol->string x)) l))]
      [`(,l-t ,r-t) (hash-set (hash-union (ast-json l-t) (ast-json r-t))
                               node-id node-json)]
      [`(lambda (,x) ,e-t) (hash-set (ast-json e-t)
                                     node-id node-json)]
      [`(if ,e-cond-t ,e-then-t ,e-else-t) (hash-set (hash-union (ast-json e-cond-t) (ast-json e-then-t) (ast-json e-else-t))
                                                     node-id node-json)]
      [`(set! ,x-t ,e-t) (hash-set (ast-json e-t)
                                   node-id node-json)]
      [`(let* ([,vars ,vals] ...) ,e0t)
       (hash-union (foldl (λ (val h) (hash-union h (ast-json val))) (hash) vals)
                   (hash node-id node-json)
                   (ast-json e0t))]
      [(? const? c) (hash node-id (add-pos (hash 'tok (~a c)) l))]))
    (let ([ast-json (ast-json tagged-expr)])
      (cons ast-json expr-ids)))
  
(define (jsonify expr-str tagged-expr s0 g σ #:analysis [analysis-type ""])
  (define state-ids (make-ids (hash-keys g)))
  (define env-ids (make-ids (map third (filter (λ (ς) (equal? (car ς) 'E)) (hash-keys g)))))
  (define val-ids (make-ids (flatten (map set->list (hash-values σ)))))
  (define kont-ids (make-ids (filter kont? (flatten (map set->list (hash-values σ))))))
  (match-define (cons ast-json expr-pos-ids) (ast-json&expr-pos-ids tagged-expr))

  (define vals-json
    (foldl (λ (val h)
             (hash-set h (string->symbol (hash-ref val-ids val))
                       (match val
                         [`(clo ((lambda (,x) ,e0) . ,l) ,ρ)
                          (hash 'type "closure"
                                'astString (~a (untag `((lambda (,x) ,e0) . ,l)))
                                'ast (hash-ref expr-pos-ids l 'null))]
                         [`(lit ,(? boolean? b))
                          (hash 'type "bool"
                                'val b
                                'valString (~a b))]
                         [x
                          (hash 'type "?"
                                'valString (~a x))])))
           (hash) (hash-keys val-ids)))
  
  (define store-json
    (foldl (λ (addr h)
             (hash-set h (string->symbol (~a addr))
                       (map (λ (val) (hash-ref val-ids val "????")) (set->list (hash-ref σ addr)))))
           (hash) (hash-keys σ)))

  (define konts-json
    (foldl (λ (kont h)
             (hash-set h (string->symbol (hash-ref kont-ids kont))
                       (hash 'instr "0"
                             'type (kont-type kont)
                             'kont (kont-kont kont))))
           (hash) (hash-keys kont-ids)))
  
  (define states-json
    (foldl (λ (s-id h)
             (let ([id (cdr s-id)]
                   [s (car s-id)])
               (hash-set h (string->symbol id)
                         (let ([state-json (hash
                                            'exprString (~a (untag (second s)))
                                            'form (~a (first s))
                                            ;'kont (state-kont s)
                                            'instr "0")])
                           (if (equal? (car s) 'T)
                               state-json
                               (hash-set state-json 'env (hash-ref env-ids (third s))))))))
           (hash) (hash->list state-ids)))

  (define configs-json
    (foldl (λ (s h)
             (let ([id (hash-ref state-ids s)])
               (hash-set h (string->symbol id)
                         (hash 'states (list id)
                               'id id
                               'form (~a (first s))
                               'astLink (if (equal? (car s) 'E)
                                            (match (hash-ref expr-pos-ids (cdr (second s)) '()) ['() (list)] [pos-id (list pos-id)])
                                            (list))))))
           (hash) (hash-keys g)))

  (define envs-json
    (foldl (λ (env h)
             (hash-set h (string->symbol (hash-ref env-ids env))
                       (map (match-lambda [(cons var addr) (hash 'var (symbol->string var)
                                                                 'varString (symbol->string var)
                                                                 'addr (~a addr)
                                                                 'instr "0")])
                            (hash->list env))))
           (hash) (hash-keys env-ids)))

  (define state-graph-json
    (foldl (λ (s h)
             (hash-set h (string->symbol (hash-ref state-ids s))
                       (foldl (λ (s′ edges-hash)
                                (hash-set edges-hash
                                          (string->symbol (hash-ref state-ids s′))
                                          (hash)))
                              (hash) (set->list (hash-ref g s)))))
           (hash)
           (hash-keys g)))

  (define instr-json
    (hash '|0| (hash 'exprStrings '() 'exprs '())))

    
  (hash
   'status "done"
   'code expr-str
   'name "Arash's AAM tool"
   'analysis analysis-type
   'items (hash
           'instr instr-json
           'vals vals-json
           'store store-json
           'states states-json
           'configs configs-json
           'envs envs-json
           'ast ast-json
           'graphs (hash 'states (hash 'graph state-graph-json
                                       'start (hash-ref state-ids s0))))))
                                  