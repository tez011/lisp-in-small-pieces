#lang racket/base
(require racket/set)
(require racket/list)
; This needs to be ported to the host-language to operate on s-expressions

(struct syntax (e scopes srcloc)
  #:property prop:custom-write (lambda (s port mode)
                                 (fprintf port "#<syntax:~s>" (syntax->datum s))))
(define empty-stx (syntax #f (set) #f))
(define (identifier? s)
  (and (syntax? s) (symbol? (syntax-e s))))
(define (syntax->datum s)
  (let loop ((s/e (syntax-e s)))
    (cond ((syntax? s/e) (loop (syntax-e s/e)))
          ((pair? s/e) (cons (loop (car s/e))
                             (loop (cdr s/e))))
          (else s/e))))
(define (datum->syntax stx-c v (stx-l #f))
  (let ((wrap (lambda (e)
                (syntax e
                        (if stx-c (syntax-scopes stx-c) (set))
                        (and stx-l (syntax-srcloc stx-l))))))
    (cond ((syntax? v) v)
          ((list? v) (wrap (map (lambda (vv) (datum->syntax stx-c vv stx-l)) v))) ; We need this to ensure that the terminal null doesn't get syntaxified.
          ((pair? v) (wrap (cons (datum->syntax stx-c (car v) stx-l)
                                 (datum->syntax stx-c (cdr v) stx-l))))
          (else (wrap v)))))

;; A lightweight pattern matcher along the lines of `syntax-rules`.
;; The result of matching is a function that takes a symbol and
;; returns its match. I don't pretend to understand this, we'll likely roll our own.
(define (match-syntax orig-s pattern
                      #:error [error error])
  (define (match s pattern)
    (cond
     [(symbol? pattern)
      (when (regexp-match? #rx"^id(:|$)" (symbol->string pattern))
        (unless (identifier? s)
          (error "not an identifier:" s)))
      (list (list pattern s))]
     [(syntax? s) (match (syntax-e s) pattern)]
     [(and (list? pattern)
           (= (length pattern) 2)
           (or (eq? '... (cadr pattern))
               (eq? '...+ (cadr pattern))))
      (define flat-s (to-syntax-list s))
      (cond
       [(null? flat-s)
        (when (eq? '...+ (cadr pattern))
          (error "bad syntax:" orig-s))
        (make-empty-vars pattern)]
       [(list? flat-s)
        (define a-lists
          (for/list ([s (in-list flat-s)])
            (match s (car pattern))))
        (apply map
               (lambda slice
                 (list (caar slice)
                       (map cadr slice)))
               a-lists)]
       [else (error "bad syntax:" orig-s)])]
     [(pair? pattern)
      (cond
       [(pair? s)
        (append (match (car s) (car pattern))
                (match (cdr s) (cdr pattern)))]
       [else (error "bad syntax:" orig-s)])]
     [(null? pattern)
      (cond
       [(null? s) null]
       [else (error "bad syntax:" orig-s)])]
     [(and (or (keyword? pattern)
               (boolean? pattern))
           (eq? pattern s))
      null]
     [else
      (error "bad pattern")]))
  (define a-list (match orig-s pattern))
  (lambda (sym)
    (define a (assq sym a-list))
    (if a
        (cadr a)
        (error "no such pattern variable:" sym))))

(define (make-empty-vars pattern)
  (cond
   [(symbol? pattern)
    (list (list pattern null))]
   [(and (list? pattern)
         (= (length pattern) 2)
         (or (eq? '... (cadr pattern))
             (eq? '...+ (cadr pattern))))
    (map (lambda (m)
           (cons (car m) (list (cadr m))))
         (make-empty-vars (car pattern)))]
   [(pair? pattern)
    (append (make-empty-vars(car pattern))
            (make-empty-vars(cdr pattern)))]
   [else
    null]))

(define (try-match-syntax orig-s pattern)
  (let/ec esc
    (match-syntax orig-s pattern
                  #:error (lambda args (esc #f)))))

(define (to-syntax-list s)
  (cond
   [(pair? s) (cons (car s) (to-syntax-list (cdr s)))]
   [(syntax? s) (to-syntax-list (syntax-e s))]
   [else s]))

; End the matcher

(struct scope (id bindings)
  #:property prop:custom-write (lambda (sc port mode)
                                 (fprintf port "#<scope:~a>" (scope-id sc))))
(define new-scope-id! (let ((n 0))
                        (lambda ()
                          (set! n (add1 n))
                          n)))
(define (new-scope)
  (scope (new-scope-id!) (make-hash)))
(define (scope>? sc1 sc2)
  (> (scope-id sc1) (scope-id sc2)))
(define (change-scope s/e sc op)
  (cond ((syntax? s/e) (syntax (change-scope (syntax-e s/e) sc op)
                               (op (syntax-scopes s/e) sc)
                               (syntax-srcloc s/e)))
        ((pair? s/e) (cons (change-scope (car s/e) sc op)
                           (change-scope (cdr s/e) sc op)))
        (else s/e)))
(define (add-scope s sc) (change-scope s sc set-add))
(define (del-scope s sc) (change-scope s sc set-remove))
(define (del-scopes s scs) (for/fold ((s s)) ((sc (in-list scs)))
                             (del-scope s sc)))
(define (xor-scope s sc) (change-scope s sc (lambda (s e)
                                              (if (set-member? s e)
                                                  (set-remove s e)
                                                  (set-add s e)))))

(define (add-binding-in-scopes! scopes sym binding)
  (when (set-empty? scopes)
    (error "cannot bind in empty scope set"))
  (let* ((max-sc (for/fold ((max-sc (set-first scopes))) ((sc (in-set scopes)))
                   (if (scope>? sc max-sc) sc max-sc)))
         (bindings (scope-bindings max-sc))
         (sym-bindings (or (hash-ref bindings sym #f)
                           (let ((h (make-hash)))
                             (hash-set! bindings sym h)
                             h))))
    (hash-set! sym-bindings scopes binding)))
(define (add-binding! id binding)
  (add-binding-in-scopes! (syntax-scopes id) (syntax-e id) binding))
(define (find-matching-bindings s scopes)
  (for*/list ((sc (in-set scopes)) ; nested loops
              (bindings (in-value (hash-ref (scope-bindings sc) (syntax-e s) #f)))
              #:when bindings ; skip if #f, now it's a hashtable
              ((b-scopes binding) (in-hash bindings))
              #:when (subset? b-scopes scopes)) ; skip if not subset
    (cons b-scopes binding)))
(define (resolve s)
  (unless (identifier? s)
    (raise-argument-error 'resolve "identifier?" s))
  (let* ((scopes (syntax-scopes s))
         (candidates (find-matching-bindings s scopes)))
    (and (pair? candidates)
         (let ((max-candidate (argmax (lambda (c) (set-count (car c))) candidates)))
           (if (andmap (lambda (c) (subset? (car c) (car max-candidate))) candidates)
               (cdr max-candidate)
               (error "ambiguous:" s scopes))))))

(struct core-binding (sym))
(struct core-form (expander) #:transparent)
(struct local-binding (key))
(define (bound-identifier=? a b)
  (and (eq? (syntax-e a)
            (syntax-e b))
       (equal? (syntax-scopes a)
               (syntax-scopes b))))
(define (free-identifier=? a b)
  (let ((ab (resolve a))
        (bb (resolve b)))
    (cond ((core-binding? ab)
           (and (core-binding? bb)
                (eq? (core-binding-sym ab)
                     (core-binding-sym bb))))
          ((local-binding? ab)
           (and (local-binding? bb)
                (eq? (local-binding-key ab)
                     (local-binding-key bb)))))))
(define (add-local-binding! id)
  (let ((key (gensym (syntax-e id))))
    (add-binding! id (local-binding key))
    key))

(define (env-extend env key val)
  (hash-set env key val))
(define missing (gensym 'missing))
(define (missing? t) (eq? t missing))
(define variable (gensym 'variable))
(define (variable? t) (eq? t variable))
(define (transformer? t) (procedure? t))

(define core-scope (new-scope))
(define core-stx (add-scope empty-stx core-scope))
(define core-forms (make-hash))
(define core-primitives (make-hash))
(define (add-core-form! sym proc)
  (add-binding! (datum->syntax core-stx sym) (core-binding sym))
  (hash-set! core-forms sym proc))
(define (add-core-primitive! sym val)
  (add-binding! (datum->syntax core-stx sym) (core-binding sym))
  (hash-set! core-primitives sym val))
(define (core-form-sym s)
  (let ((m (try-match-syntax s '(id . _)))) ; try-match a syntax that is a cons pair, and return the car
    (and m
         (let ((b (resolve (m 'id))))
           (and (core-binding? b) (core-binding-sym b))))))
(define (binding-lookup b env id)
  (cond ((core-binding? b)
         (let ((c (hash-ref core-forms (core-binding-sym b) #f)))
           (if c (core-form c) variable)))
        ((local-binding? b)
         (let ((t (hash-ref env (local-binding-key b) missing)))
           (if (eq? t missing)
               (error "identifier used out of context:" id)
               t)))
        (else (error "internal error: unknown binding for lookup:" b))))

(struct expand-context (use-site-scopes
                        env
                        only-immediate?
                        post-expansion-scope))
(define (make-expand-context)
  (expand-context #f #hash() #f #f))
(define (expand-in-context s ctx)
  (cond ((identifier? s)
         (expand-identifier s ctx))
        ((and (pair? (syntax-e s))
              (identifier? (car (syntax-e s))))
         (expand-identifier-application s ctx))
        ((or (pair? (syntax-e s))
             (null? (syntax-e s)))
         (expand-implicit '#%app s ctx))
        (else
         (expand-implicit '#%datum s ctx))))
(define (expand-identifier s ctx)
  (let ((binding (resolve s)))
    (if binding
        (dispatch (binding-lookup binding (expand-context-env ctx) s) s ctx)
        (expand-implicit '#%top s ctx))))
(define (expand-identifier-application s ctx)
  (let* ((id (car (syntax-e s)))
         (binding (resolve id)))
    (if binding
        (let ((t (binding-lookup binding (expand-context-env ctx) id)))
          (if (variable? t)
              (expand-implicit '#%app s ctx)
              (dispatch t s ctx)))
        (expand-implicit '#%app s ctx))))
(define (expand-implicit sym s ctx)
  (let* ((id (datum->syntax s sym))
         (b (resolve id))
         (t (and b (binding-lookup b (expand-context-env ctx) id))))
    (cond ((core-form? t)
           (if (expand-context-only-immediate? ctx)
               s
               (dispatch t (datum->syntax s (cons sym s) s) ctx)))
          ((transformer? t)
           (dispatch t (datum->syntax s (cons sym s) s) ctx))
          (else (error (format "no transformer binding for ~a:" sym) s)))))
(define (dispatch t s ctx)
  (cond ((core-form? t)
         (if (expand-context-only-immediate? ctx)
             s
             ((core-form-expander t) s ctx)))
        ((transformer? t)
         (expand-in-context (apply-transformer t s ctx) ctx))
        ((variable? t) ; some run-time value
         s)
        (else ; some other compile-time value
         (error "illegal use of syntax:" t))))
(define (apply-transformer t s ctx)
  (let* ((intro-scope (new-scope))
         (intro-s (add-scope s intro-scope))
         (use-s (maybe-add-use-site-scope intro-s ctx))
         (transformed-s (t use-s)))
    (if (syntax? transformed-s)
        (maybe-add-post-expansion-scope (xor-scope transformed-s intro-scope) ctx)
        (error "transformed produced non-syntax:" transformed-s))))
(define (maybe-add-use-site-scope s ctx)
  (if (expand-context-use-site-scopes ctx)
      (let ((sc (new-scope))
            (b (expand-context-use-site-scopes ctx)))
        (set-box! b (cons sc (unbox b))) ; this is so that we can mutate the field in the expand-context
        (add-scope s sc))
      s))
(define (maybe-add-post-expansion-scope s ctx)
  (if (expand-context-post-expansion-scope ctx)
      (add-scope s (expand-context-post-expansion-scope ctx))
      s))
(define (expand-body bodys sc s ctx)
  (let ((outside-sc (new-scope))
        (inside-sc (new-scope)))
    (let loop ((body-ctx (expand-context (box null)
                                         (expand-context-env ctx)
                                         #t
                                         inside-sc))
               (bodys (map (lambda (body)
                             (add-scope (add-scope (add-scope body sc) outside-sc) inside-sc)) bodys))
               (done-bodys null)
               (val-binds null)
               (dups #hash()))
      (if (null? bodys)
          (finish-expanding-body body-ctx done-bodys val-binds s)
          (let ((exp-body (expand-in-context (car bodys) body-ctx)))
            (case (core-form-sym exp-body)
              ((begin)
               (let ((m (match-syntax exp-body '(begin e ...)))) ; (to-syntax-list (cdr (syntax-e s))), I guess
                 (loop body-ctx
                       (append (m 'e) (cdr bodys))
                       done-bodys val-binds dups)))
              ((define-values)
               (let* ((m (match-syntax exp-body '(define-values (id ...) rhs)))
                      (ids (remove-use-site-scopes (m 'id) body-ctx))
                      (new-dups (check-no-duplicate-ids ids exp-body dups))
                      (keys (map add-local-binding! ids))
                      (extended-env (foldl (lambda (key env) (env-extend env key variable))
                                           (expand-context-env body-ctx) keys)))
                 (loop (struct-copy expand-context body-ctx
                                    (env extended-env))
                       (cdr bodys)
                       null
                       (cons (list ids (m 'rhs))
                             (append
                              (map (lambda (done-body) (no-binds done-body s)) done-bodys)
                              val-binds))
                       new-dups)))
              ((define-syntaxes)
               (let* ((m (match-syntax exp-body '(define-syntaxes (id ...) rhs)))
                      (ids (remove-use-site-scopes (m 'id) body-ctx))
                      (new-dups (check-no-duplicate-ids ids exp-body dups))
                      (keys (map add-local-binding! ids))
                      (vals (eval-for-syntaxes-binding (m 'rhs) ids ctx))
                      (extended-env (foldl (lambda (key val env) (env-extend env key val))
                                           (expand-context-env body-ctx) keys vals)))
                 (loop (struct-copy expand-context body-ctx
                                    (env extended-env))
                       (cdr bodys)
                       done-bodys val-binds new-dups)))
              (else
               (loop body-ctx
                     (cdr bodys)
                     (cons exp-body done-bodys)
                     val-binds
                     dups))))))))
(define (finish-expanding-body body-ctx done-bodys val-binds s)
  (when (null? done-bodys)
    (error "no body forms:" s))
  (let* ((finish-ctx (expand-context #f
                                     (expand-context-env body-ctx)
                                     #f #f))
         (finish-bodys (lambda ()
                         (if (null? (cdr done-bodys))
                             (expand-in-context (car done-bodys) finish-ctx)
                             (datum->syntax #f
                                            `(,(datum->syntax core-stx 'begin)
                                              ,@(map (lambda (body) (expand-in-context body finish-ctx)) (reverse done-bodys)))
                                            s)))))
    (if (null? val-binds)
        (finish-bodys)
        (datum->syntax #f
                       `(,(datum->syntax core-stx 'letrec-values)
                         ,(map (lambda (bind) `(,(datum->syntax #f (car bind)) ,(expand-in-context (cadr bind) finish-ctx))) (reverse val-binds))
                         ,(finish-bodys))
                       s))))
(define (no-binds expr s)
  (list null
        (datum->syntax #f
                       `(,(datum->syntax core-stx 'begin)
                         ,expr
                         (,(datum->syntax core-stx '#%app)
                          ,(datum->syntax core-stx 'values)))
                       s)))
(define (remove-use-site-scopes s ctx)
  (del-scopes s (unbox (expand-context-use-site-scopes ctx))))
(define (check-no-duplicate-ids ids s (ht #hash()))
  (let loop ((v ids) (ht ht))
    (cond ((identifier? v)
           (let ((l (hash-ref ht (syntax-e v) null)))
             (for ((id (in-list l)))
               (when (bound-identifier=? id v)
                 (error "duplicate binding:" v)))
             (hash-set ht (syntax-e v) (cons v l))))
          ((pair? v)
           (loop (cdr v) (loop (car v) ht)))
          (else ht))))

(define (compile s)
  (cond ((pair? (syntax-e s))
         (let ((core-sym (core-form-sym s)))
           (case core-sym
             ((#f) (error "not a core form:" s))
             ((lambda)
              (let ((m (match-syntax s '(lambda formals body))))
                `(lambda ,@(compile-lambda (m 'formals) (m 'body)))))
             ((case-lambda)
              (let ((m (match-syntax s '(case-lambda (formals body) ...))))
                `(case-lambda ,@(map compile-lambda (m 'formals) (m 'body)))))
             ((#%app)
              (let ((m (match-syntax s '(#%app . rest))))
                (map compile (m 'rest))))
             ((if)
              (let ((m (match-syntax s '(if tst thn els))))
                `(if
                  ,(compile (m 'tst))
                  ,(compile (m 'thn))
                  ,(compile (m 'els)))))
             ((begin begin0)
              (let ((m (match-syntax s '(begin e ...+))))
                `(,core-sym ,@(map compile (m 'e)))))
             ((set!)
              (let ((m (match-syntax s '(set! id rhs))))
                `(set! ,(compile (m 'id))
                       ,(compile (m 'rhs)))))
             ((let-values letrec-values)
              (compile-let core-sym s))
             ((quote)
              (let ((m (match-syntax s '(quote datum))))
                `(quote ,(syntax->datum (m 'datum)))))
             ((quote-syntax)
              (let ((m (match-syntax s '(quote-syntax datum))))
                `(quote ,(m 'datum))))
             (else (error "unrecognized core form:" core-sym)))))
        ((identifier? s)
         (let ((b (resolve s)))
           (cond ((core-binding? b)
                  (hash-ref core-primitives (core-binding-sym b) #f))
                 ((local-binding? b)
                  (if (local-binding-key b)
                      (key->symbol (local-binding-key b))
                      (error "missing a binding after expansion:" s)))
                 (else (error "not a reference to a local binding:" s)))))
        (else (error "bad syntax after expansion:" s))))
(define (compile-lambda formals body)
  (let ((gen-formals (let loop ((formals formals))
                       (cond ((identifier? formals) (local->symbol formals))
                             ((syntax? formals) (loop (syntax-e formals)))
                             ((pair? formals) (cons (loop (car formals))
                                                    (loop (cdr formals))))
                             (else null)))))
    `(,gen-formals ,(compile body))))
(define (compile-let core-sym s)
  (let* ((rec? (eq? core-sym 'letrec-values))
         (m (match-syntax s '(let-values (((id ...) rhs) ...) body)))
         (sc (new-scope))
         (symss (map (lambda (ids) (map local->symbol ids)) (m 'id))))
    `(,core-sym
      ,(map (lambda (syms rhs) `(,syms ,(compile rhs))) symss (m 'rhs))
      ,(compile (m 'body)))))
(define (local->symbol id)
  (let ((b (resolve id)))
    (if (local-binding? b)
        (key->symbol (local-binding-key b))
        (error "bad binding:" id))))
(define (key->symbol key) key)

(define (expand-transformer s ctx)
  (expand-in-context s (expand-context (expand-context-use-site-scopes ctx)
                                       #hash() #f #f)))
(define (expand+eval-for-syntaxes-binding rhs ids ctx)
  (let ((exp-rhs (expand-transformer rhs ctx)))
    (values exp-rhs
            (eval-for-bindings ids exp-rhs))))
(define (eval-for-syntaxes-binding rhs ids ctx)
  (define-values (exp-rhs vals) (expand+eval-for-syntaxes-binding rhs ids ctx))
  vals)
(define (eval-for-bindings ids s)
  (let* ((compiled (compile s))
         (vals (call-with-values (lambda () (expand-time-eval `(#%expression ,compiled))) list)))
    (if (= (length ids) (length vals))
        vals
        (error "wrong number of results: ids(" (length ids) ") != vals(" (length vals) ") from" s))))
(define (expand-time-eval compiled)
  (eval compiled (make-base-namespace)))
(define (rebuild orig-s nw)
  (datum->syntax orig-s nw orig-s))

;; because a lot of this is incidental?
;; Common expansion for `lambda` and `case-lambda`
(define (make-lambda-expander s formals bodys ctx)
  (define sc (new-scope))
  ;; Parse and check formal arguments:
  (define ids (parse-and-flatten-formals formals sc))
  (check-no-duplicate-ids ids s)
  ;; Bind each argument and generate a corresponding key for the
  ;; expand-time environment:
  (define keys (for/list ([id (in-list ids)])
                 (add-local-binding! id)))
  (define body-env (for*/fold ([env (expand-context-env ctx)]) ([key (in-list keys)])
                     (env-extend env key variable)))
  ;; Expand the function body:
  (define body-ctx (struct-copy expand-context ctx
                                [env body-env]))
  (define exp-body (expand-body bodys sc s body-ctx))
  ;; Return formals (with new scope) and expanded body:
  (values (add-scope formals sc)
          exp-body))

(add-core-form!
 'lambda
 (lambda (s ctx)
   (define m (match-syntax s '(lambda formals body ...+)))
   (define-values (formals body)
     (make-lambda-expander s (m 'formals) (m 'body) ctx))
   (rebuild
    s
    `(,(m 'lambda) ,formals ,body))))

(add-core-form!
 'case-lambda
 (lambda (s ctx)
   (define m (match-syntax s '(case-lambda [formals body ...+] ...)))
   (define cm (match-syntax s '(case-lambda clause ...)))
   (rebuild
    s
    `(,(m 'case-lambda)
      ,@(for/list ([formals (in-list (m 'formals))]
                   [bodys (in-list (m 'body))]
                   [clause (in-list (cm 'clause))])
          (define-values (exp-formals exp-body)
            (make-lambda-expander s formals bodys ctx))
          (rebuild clause `[,exp-formals ,exp-body]))))))

(define (parse-and-flatten-formals all-formals sc)
  (let loop ([formals all-formals])
    (cond
     [(identifier? formals) (list (add-scope formals sc))]
     [(syntax? formals)
      (define p (syntax-e formals))
      (cond
       [(pair? p) (loop p)]
       [(null? p) null]
       [else (error "not an identifier:" p)])]
     [(pair? formals)
      (unless (identifier? (car formals))
        (error "not an identifier:" (car formals)))
      (cons (add-scope (car formals) sc)
            (loop (cdr formals)))]
     [(null? formals)
      null]
     [else
      (error "bad argument sequence:" all-formals)])))

;; ----------------------------------------

;; Common expansion for `let[rec]-[syntaxes+]values`
(define (make-let-values-form syntaxes? rec?)
  (lambda (s ctx)
    (define m (if syntaxes?
                  (match-syntax s '(letrec-syntaxes+values
                                    ([(trans-id ...) trans-rhs] ...)
                                    ([(val-id ...) val-rhs] ...)
                                    body ...+))
                  (match-syntax s '(let-values ([(val-id ...) val-rhs] ...)
                                    body ...+))))
   (define sc (new-scope))
   ;; Add the new scope to each binding identifier:
   (define trans-idss (for/list ([ids (in-list (if syntaxes? (m 'trans-id) null))])
                        (for/list ([id (in-list ids)])
                          (add-scope id sc))))
   (define val-idss (for/list ([ids (in-list (m 'val-id))])
                      (for/list ([id (in-list ids)])
                        (add-scope id sc))))
   (check-no-duplicate-ids (list trans-idss val-idss) s)
   ;; Bind each left-hand identifier and generate a corresponding key
   ;; fo the expand-time environment:
   (define trans-keyss (for/list ([ids (in-list trans-idss)])
                         (for/list ([id (in-list ids)])
                           (add-local-binding! id))))
   (define val-keyss (for/list ([ids (in-list val-idss)])
                       (for/list ([id (in-list ids)])
                         (add-local-binding! id))))
   ;; Evaluate compile-time expressions (if any):
   (define trans-valss (for/list ([rhs (in-list (if syntaxes? (m 'trans-rhs) null))]
                                  [ids (in-list trans-idss)])
                         (eval-for-syntaxes-binding (add-scope rhs sc) ids ctx)))
   ;; Fill expansion-time environment:
   (define rec-val-env
     (for*/fold ([env (expand-context-env ctx)]) ([keys (in-list val-keyss)]
                                                  [key (in-list keys)])
       (env-extend env key variable)))
   (define rec-env (for/fold ([env rec-val-env]) ([keys (in-list trans-keyss)]
                                                  [vals (in-list trans-valss)])
                     (for/fold ([env env]) ([key (in-list keys)]
                                            [val (in-list vals)])
                       (env-extend env key val))))
   ;; Expand right-hand sides and bodyL
   (define rec-ctx (struct-copy expand-context ctx
                                [env rec-env]))
   (define letrec-values-id
     (if syntaxes?
         (datum->syntax core-stx 'letrec-values)
         (m 'let-values)))
   (rebuild
    s
    `(,letrec-values-id ,(for/list ([ids (in-list val-idss)]
                                    [rhs (in-list (m 'val-rhs))])
                           `[,ids ,(if rec?
                                       (expand-in-context (add-scope rhs sc) rec-ctx)
                                       (expand-in-context rhs ctx))])
      ,(expand-body (m 'body) sc s rec-ctx)))))

(add-core-form!
 'let-values
 (make-let-values-form #f #f))

(add-core-form!
 'letrec-values
 (make-let-values-form #f #t))

(add-core-form!
 'letrec-syntaxes+values
 (make-let-values-form #t #t))

;; ----------------------------------------

(add-core-form!
 '#%datum
 (lambda (s ctx)
   (define m (match-syntax s '(#%datum . datum)))
   (when (keyword? (syntax-e (m 'datum)))
     (error "keyword misused as an expression:" (m 'datum)))
   (rebuild
    s
    (list (datum->syntax core-stx 'quote)
          (m 'datum)))))

(add-core-form!
 '#%app
 (lambda (s ctx)
   (define m (match-syntax s '(#%app rator rand ...)))
   (rebuild
    s
    (list* (m '#%app)
           (expand-in-context (m 'rator) ctx)
           (for/list ([rand (in-list (m 'rand))])
             (expand-in-context rand ctx))))))

(add-core-form!
 'quote
 (lambda (s ctx)
   (match-syntax s '(quote datum))
   s))

(add-core-form!
 'quote-syntax
 (lambda (s ctx)
   (match-syntax s '(quote-syntax datum))
   s))

(add-core-form!
 'if
 (lambda (s ctx)
   (define m (match-syntax s '(if tst thn els)))
   (rebuild
    s
    (list (m 'if)
          (expand-in-context (m 'tst) ctx)
          (expand-in-context (m 'thn) ctx)
          (expand-in-context (m 'els) ctx)))))

(add-core-form!
 'with-continuation-mark
 (lambda (s ctx)
   (define m (match-syntax s '(with-continuation-mark key val body)))
   (rebuild
    s
    (list (m 'with-continuation-mark)
          (expand-in-context (m 'key) ctx)
          (expand-in-context (m 'val) ctx)
          (expand-in-context (m 'body) ctx)))))

(define (make-begin)
 (lambda (s ctx)
   (define m (match-syntax s '(begin e ...+)))
   (rebuild
    s
    (cons (m 'begin)
          (for/list ([e (in-list (m 'e))])
            (expand-in-context e ctx))))))

(add-core-form!
 'begin
 (make-begin))

(add-core-form!
 'begin0
 (make-begin))

(add-core-form!
 'set!
 (lambda (s ctx)
   (define m (match-syntax s '(set! id rhs)))
   (define binding (resolve (m 'id)))
   (unless binding
     (error "no binding for assignment:" s))
   (define t (binding-lookup binding (expand-context-env ctx) s))
   (unless (variable? t)
     (error "cannot assign to syntax:" s))
   (rebuild
    s
    (list (m 'set!)
          (m 'id)
          (expand-in-context (m 'rhs) ctx)))))

(add-core-form!
 'define-values
 (lambda (s ctx)
   (error "not allowed in an expression position:" s)))

(add-core-form!
 'define-syntaxes
 (lambda (s ctx)
   (error "not allowed in an expression position:" s)))

(add-core-primitive! 'syntax-e syntax-e)
(add-core-primitive! 'datum->syntax datum->syntax)
(add-core-primitive! 'cons cons)
(add-core-primitive! 'list list)
(add-core-primitive! 'car car)
(add-core-primitive! 'cdr cdr)
(add-core-primitive! 'null? null?)
(add-core-primitive! 'values values)

(define (syntax-introduce s)
  (add-scope s core-scope))
(struct compiled-expression (s-expr)
  #:property prop:custom-write (lambda (c port mode)
                                 (fprintf port "#<compiled-expression:~s>" (compiled-expression-s-expr c))))
(define (compile-expression s)
  (compiled-expression (compile s)))
(define (expand s)
  (expand-in-context s (make-expand-context)))

;; ----------------------------------------

(define (expand-expression e)
  (expand (syntax-introduce (datum->syntax #f e))))
(define (compile+eval-expression e)
  (define c
    (compile (expand-expression e)))
  (values c
          (run-time-eval c)))
(define (run-time-eval compiled)
  (eval compiled (make-base-namespace)))

(define (eval-expression e #:check [check-val #f])
  (define-values (c v) (compile+eval-expression e))
  (when check-val
    (unless (equal? v check-val)
      (error "check failed")))
  v)

(compile+eval-expression
 '(case-lambda
   [(x) (set! x 5)]
   [(x y) (begin0 y x)]
   [() (if 1 2 3)]))

(compile+eval-expression
 '(lambda (x) (define-values (y) x) y))


(compile+eval-expression
 '(lambda (x)
   (define-syntaxes (y) (lambda (stx) (quote-syntax 7)))
   y))

(compile+eval-expression
 '(let-values ([(z) 9])
   (letrec-syntaxes+values
    ([(m) (lambda (stx) (car (cdr (syntax-e stx))))])
    ([(x) 5] [(y) (lambda (z) z)])
    (let-values ([(z) 10])
      (begin z (if (m 10) 1 2))))))

"expansion not captured"
(eval-expression
 #:check 'x-1
 '(let-values ([(x) 'x-1])
   (letrec-syntaxes+values
    ([(m) (lambda (stx) (quote-syntax x))])
    ()
    (let-values ([(x) 'x-3])
      (m)))))

"non-capturing expansion"
(eval-expression
 #:check 'x-3
 '(let-values ([(x) 'x-1])
   (letrec-syntaxes+values
    ([(m) (lambda (stx)
            (datum->syntax
             #f
             (list (quote-syntax let-values)
                   (list (list (list (quote-syntax x))
                               (quote-syntax 'x-2)))
                   (car (cdr (syntax-e stx))))))])
    ()
    (let-values ([(x) 'x-3])
      (m x)))))

"distinct generated variables"
(eval-expression
 #:check '(2 1)
 '(letrec-syntaxes+values
   ([(gen) (lambda (stx)
             (let-values ([(vals) (syntax-e (car (cdr (syntax-e stx))))]
                          [(binds) (syntax-e (car (cdr (cdr (syntax-e stx)))))]
                          [(refs) (syntax-e (car (cdr (cdr (cdr (syntax-e stx))))))])
               (datum->syntax
                #f
                (if (null? vals)
                    (list (quote-syntax bind) binds refs)
                    (list (quote-syntax gen)
                          (cdr vals)
                          (cons (list (list (quote-syntax x))
                                      (car vals))
                                binds)
                          (cons (quote-syntax x)
                                refs))))))]
    [(bind) (lambda (stx)
              (let-values ([(binds) (car (cdr (syntax-e stx)))]
                           [(refs) (car (cdr (cdr (syntax-e stx))))])
                (datum->syntax
                 (quote-syntax here)
                 (list (quote-syntax let-values)
                       binds
                       (cons (quote-syntax list)
                             refs)))))])
   ()
   (gen (1 2) () ())))

"use-site scopes (so not ambiguous)"
(eval-expression
 #:check 'ok
 '((let-values ()
     (define-syntaxes (identity)
       (lambda (stx)
         (let-values ([(misc-id) (car (cdr (syntax-e stx)))])
           (datum->syntax
            (quote-syntax here)
            (list 'lambda '(x)
                  (list 'let-values (list
                                     (list (list misc-id) ''other))
                        'x))))))
     (identity x))
   'ok))

"use-site scope remove from binding position"
(eval-expression
 #:check 'still-ok
 '(let-values ()
   (define-syntaxes (define-identity)
     (lambda (stx)
       (let-values ([(id) (car (cdr (syntax-e stx)))])
         (datum->syntax
          (quote-syntax here)
          (list 'define-values (list id) '(lambda (x) x))))))
   (define-identity f)
   (f 'still-ok)))

"non-transformer binding misuse"
(with-handlers ([exn:fail? (lambda (exn)
                             (unless (regexp-match? #rx"illegal use of syntax"
                                                    (exn-message exn))
                               (error "wrong error"))
                             'illegal-use)])
  (expand-expression '(letrec-syntaxes+values
                       ([(v) 1])
                       ()
                       v))
  (error "shouldn't get here"))