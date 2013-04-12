#lang plai

(require "parse-io.rkt")
(require "language.rkt")
(require "util.rkt")


(define lion (parse-file "solved/LION.THM"))


;; GLOBAL OPTIONS
(define max-step 10000)
(define max-literal 20)
(define verbose true)

(define starter-verbose true)

;; factorization : clause -> clause
(define (factor cls)
  (let*
      (
       (mgu/lits (fup-mgu/factor cls cls))
       (mgu (if (null? mgu/lits) null (car mgu/lits)))
       )
    (cond
      ((null? mgu) cls)
      (else
       (factor (remove-identicals (apply-mgu mgu cls)))))))

;; resolve : clause clause -> clause
;; implements full resolution by repeated applications of binary resolution
(define init true)

(define (resolve c1 c2 pred-order)
  (begin
    (set! init true)
    (resolve-inner c1 c2 pred-order)))

(define resolve-inner
  (lambda (c1 c2 pred-order)
    (let*
        (
         (resolvent1 (binary-resolve c1 c2 pred-order))
         (resolvent2 (binary-resolve (factor c1) c2 pred-order))
         (resolvent3 (binary-resolve c1 (factor c2) pred-order))
         (resolvent4 (binary-resolve (factor c1) (factor c2) pred-order))
         )
      (cond
        ; if init and all resolvents are false, then stop
        ((and (not init) (not resolvent1) (not resolvent2) (not resolvent3) (not resolvent4))
         (remove-identicals (append c1 c2)))
        (resolvent4
         (if (and (null? (car resolvent4))
                  (null? (cadr resolvent4)))
             null
             (begin
               (set! init false)
               (if verbose (begin (newline) (display "Using factor of both : ")) (void))
               (resolve-inner (car resolvent4) (cadr resolvent4) pred-order))))
        (resolvent3
         (if (and (null? (car resolvent3))
                  (null? (cadr resolvent3))) 
             null
             (begin
               (set! init false)
               (if verbose (begin (newline) (display "Using factor of the second clause : ")) (void))
               (resolve-inner (car resolvent3) (cadr resolvent3) pred-order))))
        (resolvent2
         (if (and (null? (car resolvent2))
                  (null? (cadr resolvent2)))
             null
             (begin
               (set! init false)
               (if verbose (begin (newline) (display "Using factor of the first clause : ")) (void)) 
               (resolve-inner (car resolvent2) (cadr resolvent2) pred-order))))
        (resolvent1
         (if (and (null? (car resolvent1))
                  (null? (cadr resolvent1)))
             null
             (begin
               (set! init false)
               (resolve-inner (car resolvent1) (cadr resolvent1) pred-order))))
        ; else is: every resolvent is false and init is true
        (else false)))))
        
;; binary-resolve : (listof (listof FOP?)) (listof (listof FOP?)) -> (listof (listof FOP?))
;; implements binary resolution on given two clauses
(define (binary-resolve c1-raw c2-raw pred-order)
  (let*
      ((same-lits-arranged (process-same-lits c1-raw c2-raw null))
       (c1-org (car same-lits-arranged))
       (c2-org (cadr same-lits-arranged))
       ; renaming the shared same variables
       (new-clauses (rename-vars c1-org c2-org))
       (c1 (car new-clauses))
       (c2 (cadr new-clauses))
       (mgu+L1~L2 (choose-unifiable-literals c1 c2 pred-order false)))
    (if (not mgu+L1~L2)
        false
        (let*
            ((mgu (car mgu+L1~L2))
             
             (c1-L1 (apply-mgu mgu (detach-literal (cadr mgu+L1~L2) c1)))
             (c2-L2 (apply-mgu mgu (detach-literal (caddr mgu+L1~L2) c2))))
          (list c1-L1 c2-L2)))))


;; initiate : (listof clauses) 
;;         ((listof clauses) -> (listof symbol?))
;;         ((listof clauses) -> (listof (listof clauses) (listof clauses)))
;;         (listof clauses) -> clause
(define (initiate S p-order-constructor clause-differentiator clause-picker)
  (if (null? S)
      (begin 
        (display "Given set is empty!")
        false)
      (let*
          (
           (len (length S))
           ; indexing all clauses with id and predcount
           (indexed-S (map (lambda (num cls) (list num (count-preds-clause cls) cls)) (build-list len (lambda (x) (add1 x))) S))
           (next-index (add1 len))
           ; constructing the predicate order
           (pred-order (p-order-constructor S))
           ; differentiate nucleus and satellite
           (N+S (clause-differentiator indexed-S))
           ; in default settings, nucleus contains mixed and negative clauses
           (nucleus (car N+S))
           ; in default settings, satellite contains only positive clauses
           (satellite (cadr N+S))
           
           (nucleus-units (filter (lambda (index+clause) (= (length (caddr index+clause)) 1)) nucleus))
           (satellite-units (filter (lambda (index+clause) (= (length (caddr index+clause)) 1)) satellite))
           )
        (begin
          (newline)
          (display "Initiating the input : ") (newline)
          (display "<ID> <predCount> <actualClause>") (newline)
          (map (lambda (clause) (begin 
                                  (display (list (car clause) (cadr clause) (unparse-clause (caddr clause)))) (newline))) indexed-S)
          (newline)(newline)
          (display "Initial predicate order: ")(newline)
          (display pred-order)
          (newline)(newline)
          (make-pi nucleus satellite nucleus-units satellite-units clause-picker pred-order next-index)))))

; prover input
(define-struct pi (nucleus satellite nuc-unit sat-unit c-picker p-order next-index))

(define (start prover-input)
  (begin
    (set! main-memory null)
    (set! proof-nucleus-memory null)
    (set! verbose starter-verbose)
    (set! last-input-index 
          (sub1 (pi-next-index prover-input)))
    (prove 
     (pi-nucleus prover-input)
     (pi-satellite prover-input)
     (pi-nuc-unit prover-input)
     (pi-sat-unit prover-input)
     (pi-c-picker prover-input)
     (pi-p-order prover-input)
     (pi-next-index prover-input)
     0)))

(define (easy-init set)
  (initiate set
            construct-pred-order
            differentiator-example
            picker-example))

(define (prove-file file-name)
  (start (easy-init (parse-file file-name))))


;; just for printing proofs
(define last-input-index 0)

;; main-memory (listof number number)
;; stores the indices of the pair of clauses that tried before
;; '(nucleus-index satellite-index)
(define main-memory null)

(define proof-nucleus-memory null)

;; stores the successful resolutions
;; '(new-resolvent-id new-resolvent (nuc-clause sat-clause))
(define proof-memory null)

;; print-proof proof-memory end-point last-input-clause-id -> void
; (print-proof proof-memory (list id id) id)


(define (prove nucleus satellite nuc-units sat-units clause-picker pred-order next-index step)
  (if (and max-step (>= step max-step))
      (begin (newline) (display "Stopping for max-step") (newline) false)
      (if (or
           (null? nucleus)
           (null? satellite))
          (begin (newline) (display "Stopping for nucleus or satellite is empty") (newline) false)
          (let*
              (
               ; select the smallast clause in filtered nucleus
               ; considering previous failed tries
               (nuc-min-clause (clause-picker (filter (lambda (nuc-clause)
                                                        (not (member (car nuc-clause) proof-nucleus-memory))) 
                                                      nucleus))) 
               ; nuc-min-clause is not just a clause but (listof ID predcount clause)
               )
            (if 
             (null? nuc-min-clause)
             ;; there are no nucleus-satellite pairs to go on
             (begin (newline) (display "Stopping : No useful clause in nucleus") (newline) false)
             (let*
                 (
                  (nc-preds (extract-names pred-names (caddr nuc-min-clause)))
                  (nc-neg-preds (extract-names neg-pred-names (caddr nuc-min-clause)))
                  
                  ; select also the smallest one in filtered satellite
                  ; where only clauses contain predicates in nc-preds or nc-neg-preds are filtered
                  
                  ; preparing filtering functions
                  (pred-sieve (map (lambda (pred-symb) (neg-with-pred-name pred-symb)) nc-preds))
                  (neg-pred-sieve (map (lambda (pred-symb) (pred-with-name pred-symb)) nc-neg-preds))
                  
                  (sat-subspace-only-negs (sieve-clause-set neg-pred-sieve satellite (car nuc-min-clause)))
                  
                  (sat-subspace-preds (if (not (null? sat-subspace-only-negs))
                                          null
                                          (sieve-clause-set pred-sieve satellite (car nuc-min-clause))))
                  
                  ; now we can select the min clause among the suitable ones in satellite
                  (sat-min-clause (clause-picker (if (null? sat-subspace-only-negs) sat-subspace-preds sat-subspace-only-negs)))
                  )
               (cond
                 ((null? sat-min-clause) ; then the chosen nucleus clause is not a good one
                  (begin
                    ; record this nucleus as a failed try and go on
                    (set! proof-nucleus-memory (cons (car nuc-min-clause) proof-nucleus-memory))
                    (prove nucleus satellite nuc-units sat-units clause-picker pred-order next-index (add1 step))))
                 (else
                  ; at this point, we've chosen two -seem to be- resolvable clauses
                  ; we still don't know if these are actually resolvable
                  (let*
                      (; record and try to resolve these chosen clauses
                       (possible-resolvent (begin
                                             (set! main-memory
                                                   (cons (list (car nuc-min-clause) (car sat-min-clause)) main-memory))
                                             (if verbose
                                                 (display (string-append "\nTrying a clash with: " 
                                                                         (number->string (car nuc-min-clause)) " and "
                                                                         (number->string (car sat-min-clause)) " : "))
                                                 (void))
                                             ;                                           (display "Proof memory : ") (display main-memory) (newline)
                                             (resolve (caddr nuc-min-clause) (caddr sat-min-clause) pred-order)))
                       )
                    (cond
                      ((null? possible-resolvent) (begin
                                                    (newline)(newline)
                                                    (display "proof-found! F is derived.")
                                                    (newline)
                                                    (print-proof proof-memory (car main-memory) last-input-index))
                                                    'proof-found!) ; we have a winner
                      ((not possible-resolvent) ; this pair failed, we already recorded them, can safely go on searching
                       (begin
                         (if verbose
                             (begin (display " failed.") (newline))
                             (void))
                         (prove nucleus satellite nuc-units sat-units clause-picker pred-order next-index (add1 step))))
                      (else
                       ; we finally have a resolvent
                       (let*
                           ((predcount (count-preds-clause possible-resolvent))
                            (resolvent (begin
                                         (if verbose
                                             (begin
                                               (display " ->> ")
                                               (display (list next-index predcount (unparse-clause possible-resolvent))) (newline))
                                             (void))
                                         (set! proof-memory (cons (list ; recording
                                                                   next-index ; the new resolvent id
                                                                   possible-resolvent ;and the resolvent with
                                                                   (list nuc-min-clause sat-min-clause)) ; which clauses generated this
                                                                  proof-memory))
                                         (set! proof-nucleus-memory null)
                                         
                                         (list next-index (count-preds-clause possible-resolvent) possible-resolvent))))
                         ; we now need to find out what to do with this resolvent
                         (cond
                           ; if max-literal is set, we discard the resolvent
                           ; note that we already recorded the pair to main-memory before
                           ((and max-literal (>= (length (caddr resolvent)) max-literal))
                            (prove nucleus satellite nuc-units sat-units clause-picker pred-order next-index (add1 step)))
                           ((andmap pred? (caddr resolvent))
                            (if (= (length (caddr resolvent)) 1) ; it is a unit clause
                                (or
                                 (unit-conflict-check resolvent nuc-units pred-order)
                                 (prove nucleus (cons resolvent satellite) nuc-units (cons resolvent sat-units) clause-picker pred-order (add1 next-index) (add1 step)))
                                (prove nucleus (cons resolvent satellite) nuc-units sat-units clause-picker pred-order (add1 next-index) (add1 step))))
                           (else
                            (if (= (length (caddr resolvent)) 1) ; unit clause
                                (or
                                 (unit-conflict-check resolvent sat-units pred-order)
                                 (prove (cons resolvent nucleus) satellite (cons resolvent nuc-units) sat-units clause-picker pred-order (add1 next-index) (add1 step)))
                                (prove (cons resolvent nucleus) satellite nuc-units sat-units clause-picker pred-order (add1 next-index) (add1 step)))))))))))))))))


;; sieve-clause-set : (listof (literal->boolean)) (listof clause) -> (listof clause)
;; sieve will eliminate the irrelevant clauses according to the given list of 
;; eliminator functions, these functions together decide whether the given clause is 
;; suitable or not, by looking at their literals
;; NOTE THAT: the clauses in the given clause set is in the format (list ID predCount clause)
(define (sieve-clause-set siever-functions clause-set chosen-nuc-clause-ID)
  (let*
      (
       (already-tried-pairs-with-this-nuc-clause 
        (filter (lambda (mem-pair) (= (car mem-pair) chosen-nuc-clause-ID)) main-memory))
       ; determine the satellite clauses tried against this nuc-clause-ID
       (tried-satellites (map cadr already-tried-pairs-with-this-nuc-clause))
       )
    (filter 
     (lambda (clause)
       (and
        (not (member (car clause) tried-satellites))
        (ormap (lambda (lit)
                 (ormap (lambda (func) (func lit))
                        siever-functions))
               (caddr clause)))) ; this is for the given format of a clause
     clause-set)))

;; unit-conflict-check : unit-clause (listof unit-clauses) (listof symbol) -> proof-found!/false
(define (unit-conflict-check clause unit-clauses pred-order)
  (cond
    ((null? unit-clauses) false)
    (else
     (let*
         ((resolvent (resolve (caddr clause) (caddr (car unit-clauses)) pred-order)))
       (cond
         ((null? resolvent) (begin
                              (newline)(newline)
                              (display "proof-found! unit conflict.")
                              (newline)
                              (print-proof proof-memory (list (car clause) (car (car unit-clauses))) 
                                           last-input-index)
                              'proof-found!))
         ((not resolvent) (unit-conflict-check clause (cdr unit-clauses) pred-order))
         (else
          (begin
            (display "!!! Dummy case, Something seriously wrong with the unit clauses !!!")
            (unit-conflict-check clause (cdr unit-clauses) pred-order))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define (start-with-order order prover-input)
  (begin
    (set! main-memory null)
    (set! proof-memory null)
    (set! proof-nucleus-memory null)
    (set! verbose starter-verbose)
    (set! last-input-index 
          (sub1 (pi-next-index prover-input)))
    (prove 
     (pi-nucleus prover-input)
     (pi-satellite prover-input)
     (pi-nuc-unit prover-input)
     (pi-sat-unit prover-input)
     (pi-c-picker prover-input)
     order
     (pi-next-index prover-input)
     0)))


(define (start-for-all-preds pinput)
  (begin
    (set! verbose starter-verbose)
    (set! main-memory null)
    (set! proof-memory null)
    (set! proof-nucleus-memory null)
    (prove-for-all-pred-orders pinput (generate-all-permutations-of (pi-p-order pinput)))))

(define (prove-for-all-pred-orders pinput order-list)
  (if 
   (null? order-list)
   false
   (let*
       ((proof (begin (newline) (display "Trying order : ") 
                      (display (car order-list)) (newline) (start-with-order (car order-list) pinput))))
     (cond
       ((and (symbol? proof) (symbol=? 'proof-found! proof))
        'QED)
       (else
        (begin (newline) 
               (display "Failed.. ") 
               (set! main-memory null)
               (set! proof-memory null)
               (set! proof-nucleus-memory null)
               (display "Memories are reset.. Going on...") (newline)
               (prove-for-all-pred-orders pinput (cdr order-list))))))))

(define (prove-file-preds file-name)
  (start-for-all-preds (easy-init (parse-file file-name))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;; print-proof : set-of-clauses proof-memory
;; crawles through the proof memory and prints the proof in a human readable 
;; format
(define (print-proof proof-memory end-points last-input-id)
  (print-real-proof (reverse (construct-proof-sequence proof-memory end-points last-input-id)) end-points))



;; print-real-proof : (listof (list id id (id cluase))) -> void
;; real printing
(define (print-real-proof proof-sequence end-points)
  (cond
    ((null? proof-sequence) (begin
                              (newline)
                              (display 
                               (string-append 
                                "From " 
                                (number->string (car end-points))
                                " and "
                                (number->string (cadr end-points))
                                " ---> F"))
                              (newline)
                              'end))
    (else
     (let*
         ((next-seq (car proof-sequence))
          (id1 (car next-seq))
          (id2 (cadr next-seq))
          (resolv-id (caaddr next-seq))
          (resolv-cls (cadr (third next-seq))))
     (begin
       (newline)
       (display (string-append "From " (number->string id1) " and " (number->string id2) ", generate -> " (number->string resolv-id) " - "
                               (foldr (lambda (a b) (if (= 0 (string-length b))
                                                        a
                                                        (string-append a " | " b))) "" (unparse-clause resolv-cls))))
       (newline)
       (print-real-proof (cdr proof-sequence) end-points))))))