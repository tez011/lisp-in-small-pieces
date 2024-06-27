; The slow interpreter.
; All data are closures.

; The environment.
(define wrong #f)
(call-with-current-continuation (lambda (k)
                                  (set! wrong (lambda args (display ">>>> ERROR") (newline) (k args)))))

; Known types. All values are closures that respond to messages.
(define the-empty-list
  (lambda (msg)
    (case msg
      ((as-typename) 'null)
      ((as-conditional) (lambda (x y) x))))) ; true
(define (create-boolean value)
  (lambda (msg)
    (case msg
      ((as-typename) 'boolean)
      ((as-conditional) (if value (lambda (x y) x) (lambda (x y) y))))))
(define (create-number value)
  (lambda (msg)
    (case msg
      ((as-typename) 'number)
      ((as-conditional) (lambda (x y) x))
      ((as-number) value))))
(define (create-string value)
  (lambda (msg)
    (case msg
      ((as-typename) 'string)
      ((as-conditional) (lambda (x y) x))
      ((as-chars) value))))
(define (create-symbol name)
  (lambda (msg)
    (case msg
      ((as-typename) 'symbol)
      ((as-conditional) (lambda (x y) x))
      ((as-name) name))))
(define (create-function tag behavior)
  (lambda (msg)
    (case msg
      ((as-typename) 'function)
      ((as-conditional) (lambda (x y) x))
      ((as-tag) tag)
      ((as-behavior) behavior))))
(define (create-pair a d) ; these are not values, these are addresses!
  (lambda (msg)
    (case msg
      ((as-typename) 'pair)
      ((as-conditional) (lambda (x y) x))
      ((set-car) (lambda (s v) (update s a v)))
      ((set-cdr) (lambda (s v) (update s d v)))
      ((get-car) a)
      ((get-cdr) d))))
(define (create-immutable-pair a d)
  (lambda (msg)
    (case msg
      ((as-typename) 'pair)
      ((as-conditional) (lambda (x y) x))
      ((set-car) (wrong "immutable pair"))
      ((set-cdr) (wrong "immutable pair"))
      ((get-car) a)
      ((get-cdr) d))))

; Storage
(define (allocate n s q)
  (if (> n 0)
      (let ((a (new-location s))) ; return the index of an unused cell
        (allocate (- n 1)
                  (expand-store a s) ; ensure that the future store 'knows' that cell is occupied
                  (lambda (a* ss) (q (cons a a*) ss))))
      (q '() s)))
; those can be accomplished with
(define (new-location s)
  (+ 1 (s 0))) ; 0 is a sentinel key pointing to the size of the store. so, to expand...
(define (expand-store new-address s)
  (update s 0 new-address))
; since r : variable -> address and s : address -> value, update should work on both.
; returns a closure with one argument. if that argument matches 'a', 'v' is returned. otherwise, try something else.
(define (update s a v)
  (lambda (aa)
    (if (eqv? a aa) v (s aa))))
(define (update* s a* v*)
  (if (pair? a*)
      (update* (update s (car a*) (car v*)) (cdr a*) (cdr v*))
      s))
  
(define (allocate-pair a d s q)
  (allocate 2 s ; it's easier this way; Queinnec suggests one index into separate car[] and cdr[] and against cdr = car+1.
            (lambda (a* ss)
              (q (create-pair (car a*) (cadr a*))
                 (update (update ss (car a*) a) (cadr a*) d))))) ; two updates required: one for the car, one for the cdr
(define (allocate-immutable-pair a d s q) ; it's the same
  (allocate 2 s (lambda (a* ss)
                  (q (create-immutable-pair (car a*) (cadr a*))
                     (update (update ss (car a*) a) (cadr a*) d)))))
(define (allocate-list v* s q)
  (define (consify v* q)
    (if (pair? v*)
        (consify (cdr v*) (lambda (v ss)
                            (allocate-pair (car v*) v ss q)))
        (q the-empty-list s)))
  (consify v* q))

(define s.init (expand-store 0 (lambda (a) (wrong "No such address" a))))
(define s.global s.init)

; Environment
(define (r.init id) (wrong "No binding for" id))
(define r.global r.init)

(define-syntax definition
  (syntax-rules ()
    ((definition name value)
     (allocate 1 s.global
               (lambda (a ss)
                 (set! r.global (update r.global 'name (car a))) ; associate name with the address
                 (set! s.global (update ss (car a) value))))))) ; associate address with value
(define-syntax defprimitive
  (syntax-rules ()
    ((defprimitive name value arity)
     (definition name
       (allocate 1 s.global
                 (lambda (a ss)
                   (set! s.global (expand-store (car a) ss))
                   (create-function (car a)
                                    (lambda (v* s k)
                                      (if (= arity (length v*))
                                          (value v* s k) ; invoke
                                          (wrong "incorrect arity" 'name))))))))))
(definition true (create-boolean #t))
(definition false (create-boolean #f))
(definition nil the-empty-list)
(defprimitive < ; name
  (lambda (v* s k)
    (if (and (eqv? ((car v*) 'as-typename) 'number) ; do type-checking
             (eqv? ((cadr v*) 'as-typename) 'number))
        (k (create-boolean              ; 3. convert the Scheme boolean to a LiSP4 boolean
            (< ((car v*) 'as-number)    ; 2. do the comparison
               ((cadr v*) 'as-number))) ; 1. convert the LiSP4 number to a Scheme number
           s)
        (wrong "< requires numbers")))
  2)
(defprimitive +
  (lambda (v* s k)
    (if (and (eqv? ((car v*) 'as-typename) 'number)
             (eqv? ((cadr v*) 'as-typename) 'number))
        (k (create-number (+ ((car v*) 'as-number) ((cadr v*) 'as-number))) s)
        (wrong "+ requires numbers"))) 2)
(defprimitive cons
  (lambda (v* s k)
    (allocate-pair (car v*) (cadr v*) s k)) 2)
(defprimitive car
  (lambda (v* s k)
    (if (eqv? ((car v*) 'as-typename) 'pair)
        (k
         (s ((car v*) 'get-car)) ; address -> value
         s)
        (wrong "not a pair" (car v*)))) 1)
(defprimitive cdr
  (lambda (v* s k)
    (if (eqv? ((car v*) 'as-typename) 'pair)
        (k (s ((car v*) 'get-cdr)) s)
        (wrong "not a pair" (car v*)))) 1)
(defprimitive set-car!
  (lambda (v* s k)
    (if (eqv? ((car v*) 'as-typename) 'pair)
        (let ((pair (car v*)))
          (k pair ((pair 'set-car) s (cadr v*))))
        (wrong "not a pair" (car v*)))) 2)
(defprimitive set-cdr!
  (lambda (v* s k)
    (if (eqv? ((car v*) 'as-typename) 'pair)
        (let ((pair (car v*)))
          (k pair ((pair 'set-cdr) s (cadr v*))))
        (wrong "not a pair" (car v*)))) 2)
(defprimitive pair?
  (lambda (v* s k)
    (k (create-boolean (eqv? ((car v*) 'as-typename) 'pair)) s)) 1)

(defprimitive eqv?
  (lambda (v* s k)
    (k (create-boolean
        (if (eqv? ((car v*) 'as-typename) ((cadr v*) 'as-typename))
            (case ((car v*) 'as-typename)
              ((null) #t)
              ((boolean) (((car v*) 'as-conditional)
                          (((cadr v*) 'as-conditional) #t #f)   ; if first is true...
                          (((cadr v*) 'as-conditional) #f #t))) ; if first is false...
              ((symbol) (eqv? ((car v*) 'as-name) ((cadr v*) 'as-name)))
              ((number) (= ((car v*) 'as-number) ((cadr v*) 'as-number)))
              ((pair) (and (= ((car v*) 'get-car) ((cadr v*) 'get-car)) ; comparing addresses, NOT values
                           (= ((car v*) 'get-cdr) ((cadr v*) 'get-cdr))))
              ((function) (= ((car v*) 'as-tag) ((cadr v*) 'as-tag)))
              (else #f))
            #f)) s))
  2)

(definition call/cc
  (create-function
   -1 ; arbitrary and won't conflict with other assignments
   (lambda (v* s k)
     (if (= 1 (length v*))
         (if (eqv? ((car v*) 'as-typename) 'function)
             (allocate 1 s
                       (lambda (a ss)
                         (((car v*) 'as-behavior) ; invoke the function passed to call/cc
                          (list (create-function (car a) (lambda (vv* sss kk)
                                                            (if (= 1 (length vv*))
                                                                (k (car vv*) sss)
                                                                (wrong "incorrect arity"))))) ; passing it the current continuation, k
                          ss k))) ; using the store after allocation and the current continuation (which will be dropped)
             (wrong "nonfunctional argument to call/cc"))
         (wrong "incorrect arity for call/cc")))))

(define (evaluate e r s k)
  (if (pair? e)
      (case (car e)
        ((quote) (evaluate-quote (cadr e) r s k))
        ((if) (evaluate-if (cadr e) (caddr e) (cadddr e) r s k))
        ((begin) (evaluate-begin (cdr e) r s k))
        ((set!) (evaluate-set! (cadr e) (caddr e) r s k))
        ((lambda) (evaluate-lambda (cadr e) (cddr e) r s k))
        (else (evaluate-application (car e) (cdr e) r s k)))
      (if (symbol? e) (evaluate-variable e r s k)
          (evaluate-quote e r s k))))

; ((v 'as-conditional) et ef) evaluates to 'et' if v, else 'ef'.
; the continuation is invoked with the contents of the store after evaluation of the condition,
; therefore, side-effects are allowed in the condition and will persist.
(define (evaluate-if ec et ef r s k)
  (evaluate ec r s
            (lambda (v ss)
              (evaluate ((v 'as-conditional) et ef) r ss k))))

; the whole point of begin is side effects, so.
(define (evaluate-begin ee r s k)
  (if (pair? (cdr ee))
      (evaluate (car ee) r s
                (lambda (void ss)
                  (evaluate-begin (cdr ee) r ss k)))
      (evaluate (car ee) r s k)))

; name -> address -> value. invoke the continuation with the value and the same, unchanged store.
(define (evaluate-variable n r s k)
  (k (s (r n)) s))

; invoke the continuation, arbitrarily supplying the result of the evaluation, with a new store containing the update.
(define (evaluate-set! n e r s k)
  (evaluate e r s
            (lambda (v ss)
              (k v (update ss (r n) v)))))

(define (evaluate-application e ep r s k)
  (define (evaluate-arguments ep r s k) ; left to right
    (if (pair? ep)
        (evaluate (car ep) r s
                  (lambda (v ss)
                    (evaluate-arguments (cdr ep) r ss
                                        (lambda (vv sss) ; the rest of the values, and the final state
                                          (k (cons v vv) sss)))))
        (k '() s)))
  (evaluate e r s
            (lambda (f ss) ; e evaluates to a function
              (evaluate-arguments ep r ss
                                  (lambda (vv sss)
                                    (if (eqv? (f 'as-typename) 'function)
                                        ((f 'as-behavior) vv sss k)
                                        (wrong "Not a function" e)))))))

(define (evaluate-lambda ep eb r s k)
  (allocate 1 s
            (lambda (a ss) ; a list of addresses with length [1], and the new store
              (k (create-function
                  (car a)
                  (lambda (v* s k) ; values of parameters
                    (if (= (length ep) (length v*))
                        (allocate (length ep) s
                                  (lambda (a* ss) ; a list of addresses with same length as ep, and the new store
                                    (evaluate-begin eb
                                                    (update* r ep a*)
                                                    (update* ss a* v*)
                                                    k)))
                        (wrong "incorrect arity"))))
                 ss))))
(define (evaluate-quote e r s k)
  (transcode e s k))

(define (transcode c s q)
  (cond ((null? c) (q the-empty-list s))
        ((pair? c) (transcode (car c) s (lambda (a ss)
                                          (transcode (cdr c) ss (lambda (d sss)
                                                                   (allocate-immutable-pair a d sss q))))))
        ((boolean? c) (q (create-boolean c) s))
        ((symbol? c) (q (create-symbol c) s))
        ((string? c) (q (create-string c) s))
        ((number? c) (q (create-number c) s))))

(define (transcode-back v s)
  (case (v 'as-typename)
    ((null) '())
    ((boolean) ((v 'as-conditional) #t #f))
    ((number) (v 'as-number))
    ((symbol) (v 'as-name))
    ((string) (v 'as-chars))
    ((pair) (cons (transcode-back (s (v 'get-car)) s)
                  (transcode-back (s (v 'get-cdr)) s)))
    ((function) 'function)
    (else (wrong "unknown type" (v 'as-typename)))))
    
(define (LiSP4)
  (define (toplevel s)
    (evaluate (read)     ; read
              r.global   ; evaluate in the global environment
              s          ; use the current store
              (lambda (v ss)
                (display (transcode-back v ss))
                (newline)
                (toplevel ss)))) ; invoke the interpreter with the new store after evaluation
  (toplevel s.global))

(LiSP4)