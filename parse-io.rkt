#lang plai

(require "language.rkt")
(require "util.rkt")
(require 2htdp/batch-io)
(require htdp/testing)
(require srfi/13)


(define comment ";")
(define negline "negated_conclusion")
(define or-sym "|")
(define or-char #\|)


(define (pre-process input)
  (filter (lambda (line)
            (not (or
                  ;; deleting empty lines
                  (null? line)
                  ;; deleting comment lines
                  (string=? (substring (car line) 0 1) comment)
                  ;; deleting "negated_conclusion" line
                  (string=? (car line) negline)
                  )))
          input))

;; remove-or-symbols : (listof string?) -> (listof string?)
(define (remove-or-symbols clause)
  (filter (λ (literal)
            (not (string=? or-sym literal))) clause))


;; parse-term : string -> FOP
;; --- assumptions ---
;; - function-like symbols with no arguments are constants -> b() or Agatha()
;; - there's no nested predicates 
;; p-f is a boolean -> true means func
;; at the top level, p-f is false (most outer is predicate), inners are true(func)
(define (parse-term lit)
  (parse-term-inner false lit))

(define (parse-term-inner p-f lit)
  (cond
    ((char=? (string-ref lit 0) #\~) 
     (neg (parse-term-inner p-f (substring lit 1 (string-length lit)))))
    ((and (= 1 (string-length lit)) (variable? (string->symbol lit)))
     (var (string->symbol lit)))
    ((and (= 1 (string-length lit)) (constant? (string->symbol lit)))
     (con (string->symbol lit)))
    (else
     (let*
         ((first-split (string-split lit "("))
          ;; extracting name of the predicate
          (name (car first-split))
          ;; trimming the outside parens name(args) -> args
          (args-total (substring lit (add1 (string-length name)) (sub1 (string-length lit))))
          ;; collecting individual arguments
          (arg-list (extract-args args-total))
          (name-sym (string->symbol name)))
       (cond
         ((empty? arg-list) ;; it's a constant
          (con name-sym))
         (p-f
          ;; it's a function
          (func (string->symbol name)
                (map (curry parse-term-inner true) arg-list)))
         (else
          ;; it's a predicate
          (pred (string->symbol name)
                (map (curry parse-term-inner true) arg-list))))))))

;; --- tests ---
(check-expect (parse-term "~LA(z,x,y)") (neg (pred 'LA (list (var 'z) (var 'x) (var 'y)))))
(check-expect (parse-term "~Richer(x,y)") (neg (pred 'Richer (list (var 'x) (var 'y)))))
(check-expect (parse-term "Killed(Charles(),Agatha())") (pred 'Killed (list (con 'Charles) (con 'Agatha))))
(check-expect (parse-term "LA(lion(),today(),ystday(today()))") (pred 'LA (list (con 'lion) (con 'today) (func 'ystday (list (con 'today))))))
(check-expect (parse-term "~Q(y,f(x,y))") (neg (pred 'Q (list (var 'y) (func 'f (list (var 'x) (var 'y)))))))
(check-expect (parse-term "MO(ystday(x))") (pred 'MO (list (func 'ystday (list (var 'x))))))
(check-expect (parse-term "Mem(x,lydays(lion()))") (pred 'Mem (list (var 'x) (func 'lydays (list (con 'lion))))))
;;; a special case:
;(check-expect (parse-term "A") (pred 'A empty))


;; parse-clause: (listof string?) -> FOP
(define (parse-clause clause)
  (cond
    ;; unit clause?
    [(null? (cdr clause)) 
     (if
      ;; originally written in file like: P(x)|Q(x) --> without spaces around |
      (member or-char (string->list (car clause)))
      (parse-clause (string-split (car clause) or-sym))
      (list (parse-term (car clause))))]
    [else
     ;; producing all disjunctions as list of FOPs
     (map parse-term (remove-or-symbols clause))
     ]))


;; parse-file : string? -> (listof clauses)
;; takes a filename and parses it to FOP expressions
(define (parse-file filename)
  (with-handlers
      ((exn:fail?
        (λ (err) (error 'parse (string-append "--- invalid input ---\n" (exn-message err))))))
    (map parse-clause (pre-process (read-words/line filename)))))

; cpu time: 4 real time: 1 gc time: 0
;(parse-file "EQUAL.THM")

(generate-report)