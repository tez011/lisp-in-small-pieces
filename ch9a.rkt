#lang racket/base
(require test-engine/racket-tests)
; An unhygienic macro expander from https://theincredibleholk.org/blog/2013/02/12/patterns-with-ellipses/

(define (match* p e sk fk)
  (cond
    ((and (pair? p) (pair? (cdr p)) (eq? '... (cadr p)))
     (let loop ((e e)
                (b '()))
       (if (null? e)
           (match* (cddr p) e (lambda (b+) (sk (cons (cons '... (reverse b)) b+))) fk)
           (match* (car p) (car e)
             (lambda (b+) (loop (cdr e) (cons b+ b))) ; builds each ellipsis item, but in reverse (for speed), reversed when iteration finishes
             (lambda () (match* (cddr p) e (lambda (b+) (sk (cons (cons '... b) b+))) fk))))))
    ((and (pair? p) (pair? e))
     (match* (car p) (car e)
       (lambda (b) (match* (cdr p) (cdr e) (lambda (b+) (sk (append b b+))) fk))
       fk))
    ((or (eq? p '_))
     (sk '()))
    ((symbol? p)
     (sk (list (cons p e))))
    ((and (null? p) (null? e))
     (sk '()))
    (else (fk))))

(define (mem* x ls)
  (cond
    ((and (pair? ls) (pair? (cdr ls)) (eq? (cadr ls) '...))
     #f)
    ((pair? ls)
     (or (mem* x (car ls)) (mem* x (cdr ls))))
    (else (eq? x ls))))
(define (extract-... p bindings)
  (if (null? bindings)
      '()
      (let ((rest (extract-... p (cdr bindings)))
            (b (car bindings)))
        (if (and (eq? (car b) '...) (not (null? (cdr b))))
            (let ((names (map car (cadr b))))
              (if (ormap (lambda (x) (mem* x p)) names)
                  (cons (cdr b) rest)
                  rest))
            rest))))
(define (instantiate* p bindings)
  (cond
    ((and (pair? p) (pair? (cdr p)) (eq? '... (cadr p)))
     (let ((bindings... (extract-... (car p) bindings)))
       (if (null? bindings...)
           (instantiate* (cddr p) bindings)
           (append
            (apply map (cons (lambda b*
                               (instantiate* (car p)
                                             (append (apply append b*)
                                                     bindings)))
                             bindings...))
            (instantiate* (cddr p) bindings)))))
    ((pair? p)
     (cons (instantiate* (car p) bindings)
           (instantiate* (cdr p) bindings)))
    ((assq p bindings) => cdr)
    (else p)))

(check-expect (match* '(let-id ((x e) ...) b) '(let ((x 5) (y 6)) (+ x y)) (lambda (b) b) (lambda () #f)) '((let-id . let) (... ((x . x) (e . 5)) ((x . y) (e . 6))) (b . (+ x y))))
(check-expect (match* '(_ e1 e2) '(or2 1 2) (lambda (b) b) (lambda () #f)) '((e1 . 1) (e2 . 2)))
(check-expect (match* '(_ e1 e2 . e3) '(thing 1 2 3 4 5 6) (lambda (b) b) (lambda () #f)) '((e1 . 1) (e2 . 2) (e3 . (3 4 5 6))))
(check-expect (match* '(let ((name val) ...) body1 body2 ...) '(let ((x 5) (y 6)) (set! a 4) (+ x y))
                (lambda (b) (instantiate* '((lambda (name ...) body1 body2 ...) val ...) b))
                (lambda () #f))
              '((lambda (x y) (set! a 4) (+ x y)) 5 6))

; Unhygienic case
(check-expect
 (let ((t 5)) ; evaluate an expression, using...
   (or #f t)) ; the expansion of this builtin macro using Racket's own system
 5)           ; expecting a result consistent with hygienic macro expansion
(check-expect
 (let ((mexp (match* '(_ e1 e2) '(or #f t)                               ; the macro match
               (lambda (b) (instantiate* '(let ((t e1)) (if t t e2)) b)) ; the macro expansion
               (lambda () #f))))         
   (let ((fexp `(let ((t 5)) ,mexp)))                                    ; create an expression using the macro expansion
     (eval fexp (make-base-namespace))))                                 ; evaluate that expression
 #f)                                                                     ; expecting a result consistent with unhygienic macro expansion

(test)