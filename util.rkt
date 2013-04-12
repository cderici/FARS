#lang plai

(require srfi/13)
(require "language.rkt")


;; clause : FOP

;; "y,f(x,y,z),t" -> '("y" "f(x,y,z)" "t")
; "and(knave(i),rich(i)),x"

;(extract-args "a,b,c")

;(extract-args "f(x(),y,z),t")
;(extract-args "f(x(),z),g(a,b)")
;(extract-args "f(x(,z),g(a,b)")

;; just a wrapper
(define (extract-args str)
  (extract-arguments str null))

(define (comma-after-paren-count0 charlst paren-count current-index)
  (cond
    ((zero? paren-count) current-index)
    ((char=? (car charlst) #\()
     (comma-after-paren-count0 (cdr charlst) 
                               (add1 paren-count)
                               (add1 current-index)))
    ((char=? (car charlst) #\))
     (comma-after-paren-count0 (cdr charlst)
                               (sub1 paren-count)
                               (add1 current-index)))
    (else
     (comma-after-paren-count0 (cdr charlst)
                               paren-count
                               (add1 current-index)))))

(define (extract-arguments str out)
  (let*
      (
       (comma-index (string-index str #\,))
       (str-len (string-length str))
       (l-loc (string-index str #\())
       (l-paren-index (if l-loc l-loc 0))
       (r-loc (string-index str #\)))
       (r-paren-index (if r-loc r-loc 0))
       )
    (cond
      ((string=? str "") (reverse out))
      ((not comma-index) (reverse (cons str out)))
      ((= comma-index 0) (extract-arguments (substring str 1 str-len) out))
      ((< comma-index l-paren-index)
       (extract-arguments (substring str (add1 comma-index) (string-length str))
                          (cons (substring str 0 comma-index) out)))
      (else
       (let*
           ((first-l-paren (member #\( (string->list str)))
            (balanced-comma-index (if first-l-paren
                                      (comma-after-paren-count0
                                       (cdr first-l-paren)
                                       1
                                       l-paren-index)
                                      (string-index str #\,))))
         (extract-arguments (substring str (add1 balanced-comma-index)
                                       str-len)
                            (cons
                             (substring str 0 (+ balanced-comma-index
                                                 (if first-l-paren
                                                     1 0))) out)))))))

;; remove-identicals : (listof FOP?) -> (listof FOP?)
;; removes identical terms
;; {P(a,x),P(a,x)} -> {P(a,x)}
(define (remove-identicals terms)
  (cond
    ((null? terms) null)
    (else
     (cons (car terms)
           (filter (compose not (curry FOP=? (car terms))) 
                   (remove-identicals (cdr terms)))))))

;; disagreement-dive : (listof FOP?) -> (listof FOP?)
;; this is actually a hack
;; we know that the terms in the given lists are not equal.
;; dive handles the cases where f(g(k)) f(u) -> {g(k),u}
(define (disagreement-dive terms)
  (cond
    ((andmap func? terms) (disagreement-set (map func-args terms)))
    ((andmap pred? terms) (disagreement-set (map pred-args terms)))
    (else terms)))

;; disagreement-set : (listof (listof FOP)) -> (listof FOP)
;; extracts the disagreement set from the given argument set of predicates
(define (disagreement-set l-args)
  (let
      (
       (first-set (first l-args))
       )
    (cond
      ((null? first-set) null)
      ((not (andmap (curry FOP=? (car first-set)) (map car l-args)))
       (disagreement-dive (map car l-args)))
      (else
       (disagreement-set (map cdr l-args))))))

;; preliminary-check
;; checks if all pred or all neg+pred with same names and same number of arguments
(define (preliminary-check terms)
  (or
   (and
    (andmap pred? terms)
    ;; check if the names and the number of arguments are the same
    (car (foldr (lambda (x y) (if (and (car y) 
                                       (and (symbol=? (pred-p-name x) (car y))
                                            (= (length (pred-args x)) (cadr y))))
                                  y
                                  (list false (cadr y)))) 
                (list (pred-p-name (car terms))
                      (length (pred-args (car terms))))
                (cdr terms))))
   (and
    (andmap neg? terms)
    (preliminary-check (map neg-expr terms))
    'N)))

;; find-term : var? (listof FOP?) -> FOP?
;; finds the first term in the disagreement-set that not includes the given var
(define (find-term v disag-set)
  (cond
    ((null? disag-set) null)
    ((and (not (var? (car disag-set)))
          (not (var-contain? v (car disag-set)))) (car disag-set))
    (else
     (find-term v (cdr disag-set)))))

;; find-var-term : (listof FOP?) -> (listof var? FOP?)
(define (find-var-term disag-set)
  (if
   (null? disag-set) false ;; Disagreement is empty
   (let*
       ((vars (filter var? disag-set))
        (v (if (null? vars) false (car vars))))
     (if (not v) false ;; there is no variable in disagreement set
         ; now we should find a term that not includes v
         (let
             ((term (find-term v disag-set)))
           (if (null? term) false ; no such t is found, not unifiable
               (list term v)))))))


;; apply-subst : (listof var? FOP?) (listof FOP?) -> (listof FOP?)
;; rewrites the terms in the given clauses, with the given var replaced with the given term
(define (apply-subst v-t loc)
  (cond
    ((null? loc) null)
    ((not (var-contain? (cadr v-t) (car loc)))
     (cons (car loc) (apply-subst v-t (cdr loc))))
    (else
     (cons (rewrite-term (cadr v-t) (car v-t) (car loc))
           (apply-subst v-t (cdr loc))))))

;; apply-mgu : (listof (listof var? FOP?)) (listof clause) -> (listof FOP?)
;; applies all the substitutions to the given clauses one by one
(define (apply-mgu mgu loc)
  (cond
    ((null? mgu) loc)
    (else
     (apply-mgu (cdr mgu) (apply-subst (car mgu) loc)))))

;; unify : (listof clause) (listof (listof var? FOP?)) -> (listof (listof var? FOP?))
;; implements the unification algorithm, finds the mgu of the given clauses
;; subst is a (listof <variable> <term>) such that <term> doesn't include <variable>
(define (unify loc mgu)
  (let ((pre-check (preliminary-check loc)))
    (if
     (not pre-check) false
     (let
         ((disag-set (disagreement-set (if (symbol=? 'N pre-check)
                                           (map (compose pred-args neg-expr) loc)
                                           (map pred-args loc)))))
       (cond
         ; if loc is a singleton, subst is the mgu
         ((null? (cdr loc)) (reverse mgu))
         ((null? disag-set) false)
         (else
          (let
              ((v-t (find-var-term disag-set)))
            (if (not v-t) false ; not unifiable
                (unify (remove-identicals (apply-subst v-t loc))
                       (cons v-t mgu))))))))))

;(define S (list (parse-term "P(a,x,f(g(y)))")
;                (parse-term "P(z,f(z),f(u))")))

;(unify S null) ; will give {a/z , f(a)/x , g(y)/u}

;; find-unifiable-pair-mgu : (listof FOP?) -> (listof FOP? FOP?)
;; finds unifiable pair of terms from the given list and produce 
;; their mgu's
(define (find-unifiable-pair-mgu lot1 lot2)
  (foldr (lambda (lit1 y)
           (if (not (null? y)) y
               (foldr (lambda (lit2 b)
                        (if (not (null? b)) b
                            (if (FOP=? lit1 lit2)
                                (list null (list lit2 lit1))
                                (let
                                    ((uni (unify (list lit1 lit2) null)))
                                  (if (not uni) b
                                      (list uni (list lit2 lit1))))))) null lot1)))
           null lot2))

;; just a helper for factorization
;; we cannot use find-unifiable-pair-mgu because of the 
;; (FOP=? lit1 lit2) hack which is intentional
(define (fup-mgu/factor c1 c2)
  (foldr (lambda (lit1 y)
           (if (not (null? y)) y
               (foldr (lambda (lit2 b)
                        (if (or (FOP=? lit1 lit2)
                                (not (null? b))) 
                            b
                            (let
                                ((uni (unify (list lit1 lit2) null)))
                              (if (not uni) b
                                  (list uni (list lit2 lit1)))))) null c1)))
         null c2))

;; detach-literal : FOP? clause -> clause
(define (detach-literal lit clause)
  (filter (compose not (curry FOP=? lit)) clause))


(define (pred-or-neg-with-name name)
  (lambda (lit)
    (or (and (pred? lit) (symbol=? name (pred-p-name lit)))
        (and (neg? lit) (pred? (neg-expr lit)) (symbol=? name (pred-p-name (neg-expr lit)))))))

(define (pred-with-name name)
  (lambda (lit)
    (and (pred? lit)
         (symbol=? name (pred-p-name lit)))))

(define (neg-with-pred-name name)
  (lambda (lit)
    (and (neg? lit)
         (pred? (neg-expr lit))
         (symbol=? name (pred-p-name (neg-expr lit))))))

;; clause-has-pred-or-neg : clause symbol? -> boolean
;; checks if the given clause contains the predicate or its negation with the given name
(define (contains-pred-or-neg clause pred-name)
  (or (memf (pred-with-name pred-name) clause)
      (memf (neg-with-pred-name pred-name) clause)
      (memf (pred-with-name pred-name) 
            (foldr append null
                   (map (lambda (lit)
                          (if (disj? lit)
                              (disj-terms lit)
                              (list lit))) clause)))
      ))

;; highest-pred-in : clause (listof symbol?)-> symbol?
;; produces the name of the predicate that has the highest order in the given clause
(define (highest-pred-in cls pred-order)
  (cond
    ((null? pred-order) false)
    ((contains-pred-or-neg cls (car pred-order)) (car pred-order))
    (else
     (highest-pred-in cls (cdr pred-order)))))


;; rename-vars : clause clause -> (list clause clause)
;; if the given clauses have variables with the same names, rename 
(define (rename-vars c1 c2)
  (let*
      ((vars-c1 (extract-names var-names c1))
       (vars-c2 (extract-names var-names c2))
       (shared-vars (foldr (lambda (t1 acc)
                             (append (foldr (lambda (t2 acc2)
                                              (if (and (symbol=? t1 t2)
                                                       (not (member t1 acc2)))
                                                  (cons t1 acc2)
                                                  acc2)) 
                                            null vars-c1)
                                     acc))
                           null vars-c2))
       ;; transforming shared vars to an mgu (just an implementation trick)
       ;; manually constructing an mgu look-a-like list of substitutions to rename shared vars
       (shared-vars-as-mgu (map (lambda (vr)
                                  (list (var (gensym)) (var vr))) shared-vars)))
    (list (apply-mgu shared-vars-as-mgu c1)
          c2)))

;; process-same-lits :  clause clause -> (list clause clause)
;; constructs and artificial mgu that will make possible the 
;; EXACTLY SAME (negated) literals to be resolved normally
;; if c1 : P(x)VQ(x) and c2: ~P(x)V~Q(x)
;; normally, renaming will make them P(gsym1)VQ(gsym1) and ~P(x)V~Q(x)
;; process-same-lits will produce 
;;         newc1 : P(a)VQ(a) and c2: ~P(x)V~Q(x)
;; to make the normal resolution process resolve them easily
(define (process-same-lits c1 c2 mgu)
  (let*
      ((generated-mgu (construct-inner-mgu c1 c2 mgu))
       (new-c1 (apply-mgu generated-mgu c1)))
    (list new-c1 c2)))

(define (construct-inner-mgu c1 c2 mgu)
  (cond
    ((null? c1) mgu)
    (else
     (let*
         ((inter-mgu (choose-unifiable-literals c1 c2 null true))
          ; usable means that unification produced empty mgu
          ; they can be unified without doing anything, which means
          ; they are exactly the same (with one being negation of the other)
          (usable? (and inter-mgu (null? (car inter-mgu)))))
       (if usable?
           (let*
               ((lit-from-c1 (cadr inter-mgu))
                ; extracting the var names from the first literal which will be transformed 
                ; with constants
                (vars-to-be-cons (extract-names var-names (list lit-from-c1)))
                ; constructing part of the mgu with found vars in this literal
                (new-mgu (map (lambda (var-name) (list (con (gensym)) (var var-name))) vars-to-be-cons))
                )
             (construct-inner-mgu (detach-literal lit-from-c1 c1) c2 (append new-mgu mgu)))
           (if (not inter-mgu)
               ; if inter-mgu is false, then they are not unifiable at all, return the mgu
               mgu
               ; else there are two literals that can be normally resolvable (with a non-empty mgu)
               ; discard it and carry on searching same lits
               (construct-inner-mgu (detach-literal (cadr inter-mgu) c1) c2 mgu)))))))

;; choose-unifiable-literals : clause clause (listof symbol?) -> (listof FOP? FOP?)
;; chooses two literals L1 and L2 from C1 and C2 (respectively) according to 
;; the given predicate order,
;; such that L1 and ~L2 are unifiable
;; hack-flag tells "do NOT use predicate-order, 
;;                      just give me two unifiable literals"
(define (choose-unifiable-literals c1 c2 pred-order hack-flag)
  (let*
      (
       ;; look for the highest predicate in c1
       (pred-symb (highest-pred-in c1 pred-order))
       ;; pred-symb is false --> not resolvable at all
       (mgu1stTry (if (and (not hack-flag) (not pred-symb))
                      false
                      (find-unifiable-pair-mgu 
                       (if hack-flag c1 (filter (pred-with-name pred-symb) c1))
                       (map (lambda (lit) (if (neg? lit) (neg-expr lit) lit)) (if hack-flag c2 (filter (neg-with-pred-name pred-symb) c2))))))
       (mgu2ndTry (if (not (null? mgu1stTry))
                      mgu1stTry
                      (find-unifiable-pair-mgu
                       (map (lambda (lit) (if (neg? lit) (neg-expr lit) lit)) (if hack-flag c1 (filter (neg-with-pred-name pred-symb) c1)))
                       (if hack-flag c2 (filter (pred-with-name pred-symb) c2)))))
       )
    (cond
      ((and (not hack-flag) (not pred-symb)) false)
      ((and (or hack-flag pred-symb) ; if there is a predicate P in both, and
            (null? mgu1stTry) ; we couldn't find P ~P pair, and
            (null? mgu2ndTry)) ; we couldn't find ~P P pair,
       false) ; then these clauses cannot be resolved
      
      ((and (not (null? mgu1stTry)) mgu1stTry)
       (list (car mgu1stTry)
             (car (cadr mgu1stTry))
             (neg (cadr (cadr mgu1stTry)))))
      ((and (not (null? mgu2ndTry)) mgu2ndTry)
       (list (car mgu2ndTry)
             (neg (car (cadr mgu2ndTry)))
             (cadr (cadr mgu2ndTry))))
      (else 
       false))))

;; count-preds-lit : FOP number -> number
(define (count-preds-lit lit)
  (type-case FOP lit
    [con (c) 0]
    [var (v) 0]
    [neg (expr) (count-preds-lit expr)]
    [conj (terms) (count-preds-clause terms)]
    [disj (terms) (count-preds-clause terms)]
    [func (name args) (count-preds-clause args)]
    [pred (name args) (add1 (count-preds-clause args))]))

(define (count-preds-clause clause)
  (foldr + 0 (map (lambda (lit)
                    (count-preds-lit lit)) clause)))

;; construct-pred-order : (listof clause) -> (listof symbol?)
;; constructs a predicate order from the given list of clauses
(define (construct-pred-order loc)
  (let*
      ((pred-names (extract-names-from-S pred-names loc))
       (pn-unique (foldr (lambda (x y) (if (member x y)
                                           y
                                           (cons x y))) null pred-names))
       (p-counts (foldr (lambda (pname counts)
                          (let
                              ((shelf (cadr (assoc pname counts))))
                            (begin
                              (set-box! shelf (add1 (unbox shelf)))
                              counts))) 
                        (map (lambda (pred) (list pred (box 0))) pn-unique) 
                        pred-names))
       )
    (map car (sort 
              (map (lambda (count-box) 
                     (list (car count-box)
                           (unbox (cadr count-box)))) 
                   p-counts) 
              (lambda (x y)
                (> (cadr x)
                   (cadr y)))))))

;; picker-example : (listof (listof number number clause)) -> (listof number number clause)
;; this example clause picker, picks a clause with the smallest pred count
(define (picker-example loc)
  (if (null? loc) null (argmin cadr loc)))

;; differentiator-example : (listof (listof clauses)) -> (liistof (listof clauses) (listof clauses))
;; extracts the nucleus and satellite by
;; putting all positive clauses into nucleus, and others to satellite
(define (differentiator-example S)
  (let*
      ((output (list null null)))
    (foldr
     (lambda (cls out)
       (if (andmap pred? (caddr cls))
           (list (car out) (cons cls (cadr out)))
           (list (cons cls (car out)) (cadr out))))
     output
     S)))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; EXTRA HELPERS
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;





(define (insert-everywhere element left right out)
  (cond
    ((null? right) (cons (append left (list element)) out))
    (else
     (insert-everywhere element (cons (car right) left) (cdr right)
                        (cons (append left (list element) right) out)))))

(define (generate-all-permutations-of lst)
  (foldr
   (lambda (element out)
     (foldr append null
            (map (lambda (outls)
                   (insert-everywhere element null outls null))
                 out)))
   (list null) lst))




;; construct-proof-sequence : proof-memory (list id id) id -> (listof (list id id (id cluase)))
;; constructs the proof-sequence that generated the top resolvents lead to F
(define (construct-proof-sequence proof-memory end-point last-input-id)
  (cond
    ((and (<= (car end-point) last-input-id)
          (<= (cadr end-point) last-input-id)) null) ; both are clauses from input
    ((<= (car end-point) last-input-id)
     ; only the first one is from input, continuing from the second clause
     (let*
         ((second-lead (assoc (cadr end-point) proof-memory))
          (new-id (car second-lead))
          (cls1 (car (third second-lead)))
          (cls2 (cadr (third second-lead)))
          )
       (cons (list (car cls1)
                   (car cls2)
                   (list new-id (second second-lead)))
             (construct-proof-sequence proof-memory (list (car cls1) (car cls2)) last-input-id))))
    ((<= (cadr end-point) last-input-id)
     ; only the second one is from input, continuing from the first clause
     (let*
         ((first-lead (assoc (car end-point) proof-memory))
          (new-id (car first-lead))
          (cls1 (car (third first-lead)))
          (cls2 (cadr (third first-lead)))
          )
       (cons (list (car cls1)
                   (car cls2)
                   (list new-id (second first-lead)))
             (construct-proof-sequence proof-memory (list (car cls1) (car cls2)) last-input-id))))
    (else
     ; both clauses are resolvents, continuing from both
     (let*
         ((p1 (car end-point))
          (p2 (cadr end-point))
          (first-lead (assoc p1 proof-memory))
          (second-lead (assoc p2 proof-memory))
          (cls1-p1 (car (third first-lead)))
          (cls2-p1 (cadr (third first-lead)))
          (cls1-p2 (car (third second-lead)))
          (cls2-p2 (cadr (third second-lead))))
       (append
        (cons
         (list (car cls1-p1)
               (car cls2-p1)
               (list p1 (second first-lead)))
         (construct-proof-sequence proof-memory (list (car cls1-p1) (car cls2-p1)) last-input-id))
        (cons
         (list (car cls1-p2)
               (car cls2-p2)
               (list p2 (second second-lead)))
         (construct-proof-sequence proof-memory (list (car cls1-p2) (car cls2-p2)) last-input-id)))))))