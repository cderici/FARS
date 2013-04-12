#lang plai



(define constant-symbols '(a b c d e))

(define var-symbols '(x y z g t u v))

(define (constant? sym)
  (and
   (symbol? sym)
   (or
    (member sym constant-symbols)
    (not (member sym var-symbols)))))

(define (variable? sym)
  (and
   (symbol? sym)
   (or
    (member sym var-symbols)
    (not (member sym constant-symbols)))))

(define (listof? pred)
  (lambda (ls)
    (andmap pred ls)))

;; Defining the abstract syntax of the reduced first-order predicate (FOP) logic
;; reduced in the way that there is no quantifier
(define-type FOP
  [con (c constant?)]
  [var (v variable?)]
  [conj (terms (listof FOP?))]
  [disj (terms (listof FOP?))]
  [neg (expr FOP?)]
  [func (f-name symbol?) (args (listof FOP?))]
  [pred (p-name symbol?) (args (listof FOP?))])


;; FOP=? : FOP? FOP? -> boolean
;; tests two FOP statements to be exactly equal
(define (FOP=? f1 f2)
  (type-case FOP f1
    [con (c) (and (con? f2) (symbol=? (con-c f2) c))]
    [var (v) (and (var? f2) (symbol=? (var-v f2) v))]
    [conj (terms) (and (conj? f2)
                       (= (length terms) (length (conj-terms f2)))
                       (andmap (lambda (t1 t2) (FOP=? t1 t2))
                               terms
                               (conj-terms f2)))]
    [disj (terms) (and (disj? f2)
                       (= (length terms) (length (disj-terms f2)))
                       (andmap (lambda (t1 t2) (FOP=? t1 t2))
                               terms
                               (disj-terms f2)))]
    [neg (expr) (and (neg? f2) (FOP=? expr (neg-expr f2)))]
    [func (name args) (and (func? f2)
                           (symbol=? name (func-f-name f2))
                           (= (length args) (length (func-args f2)))
                           (andmap (lambda (a1 a2) (FOP=? a1 a2))
                                   args
                                   (func-args f2)))]
    [pred (name args) (and (pred? f2)
                           (symbol=? name (pred-p-name f2))
                           (= (length args) (length (pred-args f2)))
                           (andmap (lambda (a1 a2) (FOP=? a1 a2))
                                   args
                                   (pred-args f2)))]))

;; var-contain? : var? FOP? -> boolean
;; checks if the given term contains the given variable
(define (var-contain? v term)
  (type-case FOP term
    [con (c) false]
    [var (v-name) (symbol=? (var-v v) v-name)]
    [conj (terms) (ormap (curry var-contain? v) terms)]
    [disj (terms) (ormap (curry var-contain? v) terms)]
    [neg (expr) (var-contain? v expr)]
    [func (name args) (ormap (curry var-contain? v) args)]
    [pred (name args) (ormap (curry var-contain? v) args)]))

;; rewrite-term : var? FOP? FOP? -> FOP?
(define (rewrite-term v new-term term)
  (type-case FOP term
    [con (c) term]
    [var (v-name) (if (symbol=? (var-v v) v-name) new-term term)]
    [conj (terms) (conj (map (curry rewrite-term v new-term)
                             terms))]
    [disj (terms) (disj (map (curry rewrite-term v new-term)
                             terms))]
    [neg (expr) (neg (rewrite-term v new-term expr))]
    [func (name args) (func name (map (curry rewrite-term v new-term) args))]
    [pred (name args) (pred name (map (curry rewrite-term v new-term) args))]))

;; var-names : FOP? (listof) -> (listof symbol?)
(define (var-names clause out)
  (type-case FOP clause
    [con (c) out]
    [var (v-name) (cons v-name out)]
    [conj (terms) (foldr (lambda (term acc) (var-names term acc)) out terms)]
    [disj (terms) (foldr (lambda (term acc) (var-names term acc)) out terms)]
    [neg (expr) (var-names expr out)]
    [func (name args) (foldr (lambda (term acc) (var-names term acc)) out args)]
    [pred (name args) (foldr (lambda (term acc) (var-names term acc)) out args)]))

(define (pred-names clause out)
  (type-case FOP clause
    [con (c) out]
    [var (v) out]
    [conj (terms) (foldr (lambda (term acc) (pred-names term acc)) out terms)]
    [disj (terms) (foldr (lambda (term acc) (pred-names term acc)) out terms)]
    [neg (expr) (pred-names expr out)]
    [func (name args) out] ; no predicate is an argument fo a function
    [pred (name args) (cons name (foldr (lambda (arg acc) (pred-names arg acc)) out args))]))

(define (neg-pred-names clause out)
  (type-case FOP clause
    [con (c) out]
    [var (v) out]
    [conj (terms) (foldr (lambda (term acc) (neg-pred-names term acc)) out terms)]
    [disj (terms) (foldr (lambda (term acc) (neg-pred-names term acc)) out terms)]
    [neg (expr) (neg-pred-names expr (cons (pred-p-name expr) out))]
    [func (name args) out] ; no predicate is an argument fo a function
    [pred (name args) (foldr (lambda (arg acc) (pred-names arg acc)) out args)]))

;; extract-names : (clause->(listof symbol?)) clause -> (listof symbol?)
(define (extract-names proc clause)
  (foldr append null
         (map (lambda (lit)
                (proc lit null)) clause)))

(define (extract-names-from-S proc loc)
  (foldr append null
         (map (lambda (clause)
                (extract-names proc clause))
              loc)))


(define (process-args args seperator out)
  (cond
    ((null? args) (substring out 1 (string-length out)))
    (else
     (process-args (cdr args)
                   seperator
                   (string-append out seperator (unparse (car args)))))))

;; unparse : FOP? -> string
(define (unparse expr)
  (type-case FOP expr
    [con (c) (symbol->string c)]
    [var (v) (symbol->string v)]
    [conj (terms) (process-args terms "AND" "")]
    [disj (terms) (process-args terms "|" "")]
    [neg (expr) (string-append "~" (unparse expr))]
    [func (name args) (string-append (symbol->string name) "(" (process-args args "," "") ")")]
    [pred (name args) (string-append (symbol->string name) "(" (process-args args "," "") ")")]))


(define (unparse-clause clause)
  (map unparse clause))

(define (unparse-S set-of-clauses)
  (map unparse-clause set-of-clauses))

