; Jeff Cailteux
; KUID: 2379460
; Project 3 Part 1
; EECS 662
; CFWAE

#lang plai

;;; CFWAE type
(define-type CFWAE
  (num (n number?))
  (id (name symbol?))
  (add (lhs CFWAE?) (rhs CFWAE?))
  (sub (lhs CFWAE?) (rhs CFWAE?))
  (mul (lhs CFWAE?) (rhs CFWAE?))
  (div (lhs CFWAE?) (rhs CFWAE?))
  (fun (fun-name symbol?) (body CFWAE?))
  (app (func CFWAE?)(arg CFWAE?))
  (if0 (c CFWAE?) (t CFWAE?) (e CFWAE?))
  (with (id symbol?) (named-expr CFWAE?) (body CFWAE?)))


;;; CFWAE Value type - requirement #1
(define-type CFWAE-Value
  (numV (n number?))
  (closureV (arg symbol?)
            (body CFWAE?)
            (ds DefrdSub?)))


;;; Deferred substitution type
(define-type DefrdSub
  (mtSub)
  (aSub (name symbol?) (value CFWAE-Value?) (ds DefrdSub?)))


;;; ds lookup
(define lookup
  (lambda (name ds)
    (type-case DefrdSub ds
      (mtSub () (error 'lookup "variable not found"))
      (aSub (n v d)
            (if (symbol=? n name)
                v
                (lookup name d))))))




;;; Parsing function - requirement #2
(define parse-cfwae
  (lambda (expr)
    (cond ((symbol? expr) (id expr))
          ((number? expr) (num expr))
          ((list? expr)
           (case (car expr)
             ((-) (cond ((fun? (parse-cfwae (cadr expr))) 
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        ((fun? (parse-cfwae (caddr expr)))
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        (else (sub (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))))
             ((+) (cond ((fun? (parse-cfwae (cadr expr))) 
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        ((fun? (parse-cfwae (caddr expr)))
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        (else (add (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))))
             ((*) (cond ((fun? (parse-cfwae (cadr expr))) 
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        ((fun? (parse-cfwae (caddr expr)))
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        (else (mul (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))))
             ((/) (cond ((fun? (parse-cfwae (cadr expr))) 
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        ((fun? (parse-cfwae (caddr expr)))
                         error  parse-cfwae "arithmetic operation cannot be performed on a function")
                        (else (div (parse-cfwae (cadr expr)) (parse-cfwae (caddr expr))))))
             ((if0) (if0 (parse-cfwae (cadr expr))
                          (parse-cfwae (caddr expr))
                          (parse-cfwae (cadddr expr))))
             ((with) (with (caadr expr)
                           (parse-cfwae (cadadr expr))
                           (parse-cfwae (caddr expr))))
             ((fun) (if (number? (cadr expr))
                        (error  parse-cfwae "cannot call a number like a function")
                        (fun (cadr expr) (parse-cfwae (caddr expr)))))
             (else (app (parse-cfwae (car expr)) (parse-cfwae (cadr expr))))))
          (else parse-cfwae "Unexpected token"))))


;;; Prelude (pi, g, area, inc)
(define prelude
  (aSub 'pi (numV 3.14159)
        (aSub 'g (numV 9.8)
              (aSub 'area (closureV 'r (mul (num 3.14159) (mul (id 'r) (id 'r))) (mtSub))
                    (aSub 'inc (closureV 'i (add (id 'i) (num 1)) (mtSub)) (mtSub))))))

;;; Interpreting function - requirement #3
(define interp-cfwae
  (lambda (expr ds)
    (type-case CFWAE expr
      (num (n) (numV n))
      (id (s) (lookup s ds))
      (sub (lhs rhs) (numV (- (numV-n (interp-cfwae lhs ds)) (numV-n (interp-cfwae rhs ds)))))
      (add (lhs rhs) (numV (+ (numV-n (interp-cfwae lhs ds)) (numV-n (interp-cfwae rhs ds)))))
      (mul (lhs rhs) (numV (* (numV-n (interp-cfwae lhs ds)) (numV-n (interp-cfwae rhs ds)))))
      (div (lhs rhs) (numV (/ (numV-n (interp-cfwae lhs ds)) (numV-n (interp-cfwae rhs ds)))))
      (if0 (c t e) (cond ((= (numV-n (interp-cfwae c ds)) 0)
                          (interp-cfwae t ds))
                         (else (interp-cfwae e ds))))
      (fun (name body) (closureV name body ds))
      (with (id expr body) 
            (local
              ((define fun-val (interp-cfwae (fun id body) ds)))
              (interp-cfwae (closureV-body fun-val)
                            (aSub (closureV-arg fun-val)
                                  (interp-cfwae expr ds)
                                  (closureV-ds fun-val)))))
      (app (func arg)
           (local
             ((define fun-val (interp-cfwae func ds)))
             (interp-cfwae (closureV-body fun-val)
                          (aSub (closureV-arg fun-val)
                                (interp-cfwae arg ds)
                                (closureV-ds fun-val))))))))


;;; Eval function  - requirement #4
(define eval-cfwae
  (lambda (expr)
    (interp-cfwae (parse-cfwae expr) prelude)))


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