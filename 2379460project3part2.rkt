
#lang plai
;;; EECS 662 - Miniproject 3
;;;
;;; Author: Jeff Cailteux
;;; Date: 4/10/13
;;;
;;; Description:
;;; CFWAER - The abstract data type for representing CFWAER ASTs
;;; parse-cfwaer - Parser translating concrete CFWAER syntax into CFWAER AST
;;; fac5 - Concrete syntax for the example from class
;;;
;;; Based on utilities provided by Perry Alexander

;;; Define an AST type for CFWAER constructs.
(define-type CFWAER
  (num (n number?))
  (add (lhs CFWAER?) (rhs CFWAER?))
  (sub (lhs CFWAER?) (rhs CFWAER?))
  (mul (lhs CFWAER?) (rhs CFWAER?))
  (div (lhs CFWAER?) (rhs CFWAER?))
  (id (name symbol?))
  (with (name symbol?) (named-expr CFWAER?) (body CFWAER?))
  (rec (name symbol?) (named-expr CFWAER?) (body CFWAER?))
  (if0 (cond CFWAER?) (tarm CFWAER?) (farm CFWAER?))
  (fun (arg-name symbol?) (body CFWAER?))
  (app (fun-expr CFWAER?)(arg CFWAER?)))

;;; CFWAER Value type
(define-type CFWAER-Value
  (numV (n number?))
  (closureV (arg symbol?)
            (body CFWAER?)
            (ds Env?)))

;;Boxed Value
(define (boxed-CFWAER-Value? v)
  (and (box? v)
       (CFWAER-Value? (unbox v))))

;;; Deferred substitution type, with recursion
(define-type Env
  (mtSub)
  (aSub (name symbol?) (value CFWAER-Value?) (ds Env?))
  (aRecSub (name symbol?) (value boxed-CFWAER-Value?) (env Env?))
  )

;;; ds lookup
(define lookup
  (lambda (name ds)
    (type-case Env ds
      (mtSub () (error 'lookup "variable not found"))
      (aSub (n v d)
            (if (symbol=? n name)
                v
                (lookup name d)))
      (aRecSub (n b d)
               (if (symbol=? n name)
                   (unbox b)
                   (lookup n d)))
      ))) 

;;; Define a parser for CFWAER constructs.  This parser does no error checking at all. Simply converts
;;; concrete syntax to AST.
(define parse-cfwaer
  (lambda (expr)
    (cond ((symbol? expr) (id expr))
          ((number? expr) (num expr))
          ((list? expr)
           (case (car expr)
             ((-) (sub (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
             ((+) (add (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
             ((*) (mul (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
             ((/) (div (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))))
             ((with) (with (car (cadr expr)) 
                            (parse-cfwaer (cadr (cadr expr))) 
                            (parse-cfwaer (caddr expr))))
             ((rec) (rec (car (cadr expr)) 
                            (parse-cfwaer (cadr (cadr expr))) 
                            (parse-cfwaer (caddr expr))))
             ((if0) (if0 (parse-cfwaer (cadr expr)) (parse-cfwaer (caddr expr))
                         (parse-cfwaer (cadddr expr))))
             ((fun) (fun (caadr expr) (parse-cfwaer (caddr expr))))
             (else (app (parse-cfwaer (car expr)) (parse-cfwaer (cadr expr))))))
          (else 'parse-cfwaer "Unexpected token"))))

;;; Cyclically bind and interp
(define (bindinterp id expr ds)
  (local((define value-holder (box (numV 1729)))
         (define new-ds (aRecSub id value-holder ds))
         (define named-expr (interp-cfwaer expr new-ds)))
    (begin
      (set-box! value-holder named-expr)
      new-ds)))


;;; Interpreting function
(define interp-cfwaer
  (lambda (expr ds)
    (type-case CFWAER expr
      (num (n) (numV n))
      (id (s) (lookup s ds))
      (sub (lhs rhs) (numV (- (numV-n (interp-cfwaer lhs ds)) (numV-n (interp-cfwaer rhs ds)))))
      (add (lhs rhs) (numV (+ (numV-n (interp-cfwaer lhs ds)) (numV-n (interp-cfwaer rhs ds)))))
      (mul (lhs rhs) (numV (* (numV-n (interp-cfwaer lhs ds)) (numV-n (interp-cfwaer rhs ds)))))
      (div (lhs rhs) (numV (/ (numV-n (interp-cfwaer lhs ds)) (numV-n (interp-cfwaer rhs ds)))))
      (if0 (c t e) (cond ((= (numV-n (interp-cfwaer c ds)) 0)
                          (interp-cfwaer t ds))
                         (else (interp-cfwaer e ds))))
      (fun (name body) (closureV name body ds))
      (with (id expr body) 
            (local
              ((define fun-val (interp-cfwaer (fun id body) ds)))
              (interp-cfwaer (closureV-body fun-val)
                            (aSub (closureV-arg fun-val)
                                  (interp-cfwaer expr ds)
                                  (closureV-ds fun-val)))))
      ;need to change rec
      (rec (id expr body)
        (interp-cfwaer body
                (bindinterp id expr ds)))
      (app (func arg)
           (local
             ((define fun-val (interp-cfwaer func ds)))
             (interp-cfwaer (closureV-body fun-val)
                          (aSub (closureV-arg fun-val)
                                (interp-cfwaer arg ds)
                                (closureV-ds fun-val))))))))



;;; Eval function
(define eval-cfwaer
  (lambda (expr)
    (interp-cfwaer (parse-cfwaer expr) (mtSub))))




;;; Factorial example from class.  Try (parse-cfwaer fac5) to see the parser produce an AST
;;; for the example.
(define fac5
  `{rec {fac {fun {n} {if0 n 1 {* n {fac {+ n -1}}}}}}{fac 5}}
  )

;;Testing
;(test (eval-cfwaer fac5) (numV 120))
;(test (eval-cfwaer '(+ 1 2)) (numV 3))
