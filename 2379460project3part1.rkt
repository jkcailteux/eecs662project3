; Jeff Cailteux
; KUID: 2379460
; Project 3 Part 1
; EECS 662
; CFAE and CFWAE

#lang plai

;;; CFAE Value type
(define-type CFAE-Value
  (numV (n number?))
  (closureV (arg symbol?)
            (body CFAE?)
            (ds DefrdSub?)))


;;; Deferred substitution type
(define-type DefrdSub
  (mtSub)
  (aSub (name symbol?) (value CFAE-Value?) (ds DefrdSub?)))


;;; ds lookup
(define lookup
  (lambda (name ds)
    (type-case DefrdSub ds
      (mtSub () (error 'lookup "variable not found"))
      (aSub (n v d)
            (if (symbol=? n name)
                v
                (lookup name d))))))


;;; CFAE type
(define-type CFAE
  (num (n number?))
  (id (name symbol?))
  (add (lhs CFAE?) (rhs CFAE?))
  (sub (lhs CFAE?) (rhs CFAE?))
  (mul (lhs CFAE?) (rhs CFAE?))
  (div (lhs CFAE?) (rhs CFAE?))
  (fun (fun-name symbol?) (body CFAE?))
  (app (func CFAE?)(arg CFAE?))
  (if0 (c CFAE?) (t CFAE?) (e CFAE?)))


;;; Interpreting function
(define interp-cfae
  (lambda (expr ds)
    (type-case CFAE expr
      (num (n) (numV n))
      (id (s) (lookup s ds))
      (sub (lhs rhs) (numV (- (numV-n (interp-cfae lhs ds)) (numV-n (interp-cfae rhs ds)))))
      (add (lhs rhs) (numV (+ (numV-n (interp-cfae lhs ds)) (numV-n (interp-cfae rhs ds)))))
      (mul (lhs rhs) (numV (* (numV-n (interp-cfae lhs ds)) (numV-n (interp-cfae rhs ds)))))
      (div (lhs rhs) (numV (/ (numV-n (interp-cfae lhs ds)) (numV-n (interp-cfae rhs ds)))))
      (if0 (c t e) (cond ((= (numV-n (interp-cfae c ds)) 0)
                          (interp-cfae t ds))
                         (else (interp-cfae e ds))))
      (fun (name body) (closureV name body ds))
      (app (func arg)
           (local
             ((define fun-val (interp-cfae func ds)))
             (interp-cfae (closureV-body fun-val)
                          (aSub (closureV-arg fun-val)
                                (interp-cfae arg ds)
                                (closureV-ds fun-val))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; Part II ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; CFWAE type
(define-type CFWAE
  (numw (n number?))
  (idw (name symbol?))
  (addw (lhs CFWAE?) (rhs CFWAE?))
  (subw (lhs CFWAE?) (rhs CFWAE?))
  (mulw (lhs CFWAE?) (rhs CFWAE?))
  (divw (lhs CFWAE?) (rhs CFWAE?))
  (funw (fun-name symbol?) (body CFWAE?))
  (appw (func CFWAE?)(arg CFWAE?))
  (if0w (c CFWAE?) (t CFWAE?) (e CFWAE?))
  (withw (id symbol?) (named-expr CFWAE?) (body CFWAE?)))


;;; Parsing function
(define parse-cfwae
  (lambda (expr)
    (cond ((symbol? expr) (idw expr))
          ((number? expr) (numw expr))
          ((list? expr)
           (case (car expr)
             ((-) (cond ((fun? (parse-cfwae (cadr expr))) 
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        ((fun? (parse-cfwae (caddr expr)))
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        (else (subw (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))))
             ((+) (cond ((fun? (parse-cfwae (cadr expr))) 
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        ((fun? (parse-cfwae (caddr expr)))
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        (else (addw (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))))
             ((*) (cond ((fun? (parse-cfwae (cadr expr))) 
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        ((fun? (parse-cfwae (caddr expr)))
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        (else (mulw (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))))
             ((/) (cond ((fun? (parse-cfwae (cadr expr))) 
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        ((fun? (parse-cfwae (caddr expr)))
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        (else (divw (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))))
             ((if0) (if0w (parse-cfwae (cadr expr))
                          (parse-cfwae (caddr expr))
                          (parse-cfwae (cadddr expr))))
             ((with) (withw (caadr expr)
                           (parse-cfwae (cadadr expr))
                           (parse-cfwae (caddr expr))))
             ((fun) (if (number? (cadr expr))
                        (error  parse-cfwae "cannot call a number like a function")
                        (funw (cadr expr) (parse-cfwae (caddr expr)))))
             (else (appw (parse-cfwae (car expr)) (parse-cfwae (cadr expr))))))
          (else parse-cfwae "Unexpected token"))))



;;; Elaborator function
(define elab-cfwae
  (lambda (expr)
    (type-case CFWAE expr
      (numw (n) (num n))
      (idw (s) (id s))
      (subw (lhs rhs) (sub (elab-cfwae lhs) (elab-cfwae rhs)))
      (addw (lhs rhs) (add (elab-cfwae lhs) (elab-cfwae rhs)))
      (mulw (lhs rhs) (mul (elab-cfwae lhs) (elab-cfwae rhs)))
      (divw (lhs rhs) (div (elab-cfwae lhs) (elab-cfwae rhs)))
      (funw (fun-name body) (fun fun-name (elab-cfwae body)))
      (appw (func arg) (app (elab-cfwae func) (elab-cfwae arg)))
      (if0w (c t e) (if0 (elab-cfwae c) (elab-cfwae t) (elab-cfwae e)))
      (withw (name named-expr body) (app (fun name (elab-cfwae body)) (elab-cfwae named-expr)))
      )))


;;; Helper function for elaborating cond0
(define elab-cond0w
  (lambda (ce ed)
    (cond ((empty? ce) ed)
          (else (if0 (elab-cfwae (caar ce))
                     (elab-cfwae (cadar ce))
                     (elab-cond0w (cdr ce) ed))))))

;;; Prelude (pi, g, area, inc)
(define prelude
  (aSub 'pi (numV 3.14159)
        (aSub 'g (numV 9.8)
              (aSub 'area (closureV 'r (mul (num 3.14159) (mul (id 'r) (id 'r))) (mtSub))
                    (aSub 'inc (closureV 'i (add (id 'i) (num 1)) (mtSub)) (mtSub))))))


;;; Eval function
(define eval-cfwae
  (lambda (cfae)
    (interp-cfae (elab-cfwae (parse-cfwae cfae)) prelude)))


;;; Test Cases
(test (eval-cfwae '{+ 1 2}) (numV 3))
(test (eval-cfwae '{+ 2 {* 2 3}}) (numV 8))
(test (eval-cfwae '{{fun x x} 3}) (numV 3))
(test (eval-cfwae '{{fun x {+ x 1}} 1}) (numV 2))
(test (eval-cfwae '{if0 0 1 2}) (numV 1))
(test (eval-cfwae '{if0 {{fun x {- x 2}} 3} {{fun x {* 2 x}} 10} {{fun x {/ x 2}} 8}}) (numV 4))
(test (eval-cfwae '{{if0 0 {fun x {+ x 1}} {fun x {+ x 2}}} 0}) (numV 1))
(test (eval-cfwae '{with {x 10} {+ x 5}}) (numV 15))
(test (eval-cfwae '{with {f {fun x {+ x 1}}} {f 2}}) (numV 3))
(test (eval-cfwae '{inc pi}) (numV 4.14159))
(test (eval-cfwae '{with {x 2} {with {inc {fun x {+ x 2}}} {inc x}}}) (numV 4))
(test (eval-cfwae '{area 2}) (numV 12.56636))
(test (eval-cfwae '{{{fun x {fun y {+ x y}}} 3} 1}) (numV 4))
(test (eval-cfwae '{with {f {fun x {fun y {+ x y}}}} {{f 3} 1}}) (numV 4))