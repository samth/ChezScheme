;;; Prototype scalar replacement on Lsrc, before cpcheck.
;;; Licensed under Apache-2.0, like the surrounding Chez compiler.
;;; Fresh nonescaping Scheme-object records and pairs; actual uses must be read-only.
;;; CHEZ_SRA_HELPERS=inline or specialize enables the two experimental helper policies.
;;; Quoted records retain the stricter immutable, non-inherited eligibility rule.
;;; Pairs may be mutable in the language, but all uses must be read-only here.
(begin
(define enable-scalar-replacement
 ($make-thread-parameter (equal? (getenv "CHEZ_SCALAR_REPLACEMENT") "1")
  (lambda (x) (and x #t))))
(define $cpsra
 (let ()
  (import (nanopass))
  (include "base-lang.ss")
  (define-threaded split-fuel)
  (define-threaded candidate-descriptor)
  (define-threaded local-count)
  (define-threaded loop-count)
  (define-threaded local-mode)
  (define-threaded local-active?)
  (define-threaded local-fuel)
  (define-threaded local-trials)
  (define-threaded local-commits)
  (define-threaded local-candidates)
  (define rtd-flds (csv7:record-field-accessor #!base-rtd 'flds))
  (define rtd-mpm (csv7:record-field-accessor #!base-rtd 'mpm))
  (define (shape? rtd)
   (and (not (record-type-parent rtd))
    (let ([fs (rtd-flds rtd)])
     (if (fixnum? fs)
      (and (fx< 0 fs) (fx<= fs 8) (eqv? 0 (rtd-mpm rtd)))
      (and (fx< 0 (length fs)) (fx<= (length fs) 8)
       (andmap (lambda (x1) (and (not (fld-mutable? x1))
                          (eq? (filter-foreign-type (fld-type x1)) 'scheme-object))) fs))))))
  (define (field-offset rtd index)
   (let ([fs (rtd-flds rtd)])
    (if (fixnum? fs)
     (fx+ (constant record-data-disp) (fxsll index (constant log2-ptr-bytes)))
     (fld-byte (list-ref fs index)))))
  (define (field-count rtd)
   (if (eq? rtd 'pair) 2
    (let ([fs (rtd-flds rtd)]) (if (fixnum? fs) fs (length fs)))))

  (define (fresh-shape? rtd)
   (let ([fs (rtd-flds rtd)])
    (if (fixnum? fs) (<= 1 fs 8)
     (and (<= 1 (length fs) 8)
          (andmap (lambda (f) (eq? (filter-foreign-type (fld-type f)) 'scheme-object)) fs)))))
  (define (ancestor? a b) (and b (or (eq? a b) (ancestor? a (record-type-parent b)))))

  ;; Two experimental, allocation-driven ways to cross known helper calls.
  (define-threaded cost-mode)
  (define-threaded size-cache)
  (define-threaded validity-cache)
  (define (sra-size ir)
   (if (member cost-mode '("cache" "bounded"))
    (or (eq-hashtable-ref size-cache ir #f)
        (let ([n (count-Lsrc ir)]) (eq-hashtable-set! size-cache ir n) n))
    (count-Lsrc ir)))
  (define-threaded helper-mode)
  (define-threaded helper-definitions)
  (define-threaded helper-scopes)
  (define-threaded helper-origin)
  (define-threaded helper-clones)
  (define-threaded helper-stack)
  (define-threaded helper-fuel)
  (define-threaded helper-inline-count)
  (define-threaded helper-total-inline)
  (define-threaded helper-total-clones)
  (define-threaded helper-roots)
  (define-threaded helper-attempts)
  (define-threaded helper-failures)
  (define-threaded helper-eliminated)
  (define (helper-note key)
   (eq-hashtable-set! helper-failures key (+ 1 (eq-hashtable-ref helper-failures key 0))))
  (define (helper-reject key fail) (helper-note key) (fail #f))
  (define (helper-valid? proc)
   (if (not cost-mode) (not (mentions? proc helper-eliminated))
    (or (null? helper-eliminated)
     (if (member cost-mode '("cache" "bounded"))
      (let ([v (eq-hashtable-ref validity-cache proc #f)])
       (if (and v (eq? (car v) helper-eliminated)) (cdr v)
        (let ([valid? (not (mentions? proc helper-eliminated))])
         (eq-hashtable-set! validity-cache proc (cons helper-eliminated valid?)) valid?)))
      (not (mentions? proc helper-eliminated))))))
  (define (known-helper x)
   (and (not (prelex-assigned x))
    (let ([proc (eq-hashtable-ref helper-definitions x #f)])
     (and proc (helper-valid? proc) proc))))
  (define (register-helpers x* e*)
   (for-each (lambda (x e)
    (nanopass-case (Lsrc Expr) e
     [(case-lambda ,preinfo (clause (,x* ...) ,interface ,body))
      (when (and (= interface (length x*)) (not (prelex-assigned x)))
       (eq-hashtable-set! helper-definitions x e))]
     [else (void)])) x* e*))
  (define (collect-helpers ir)
   (define scope '())
   (define (enter x* thunk)
    (let ([s (cons (list #f) scope)])
     (for-each (lambda (x) (eq-hashtable-set! helper-scopes x s)) x*)
     (fluid-let ([scope s]) (thunk))))
   (define-pass scan : Lsrc (ir) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
     [(letrec ([,x* ,e*] ...) ,body)
      (register-helpers x* e*)
      (enter x* (lambda () (for-each Expr e*) (Expr body))) ir]
     [(letrec* ([,x* ,e*] ...) ,body)
      (register-helpers x* e*)
      (enter x* (lambda () (for-each Expr e*) (Expr body))) ir]
     [(call ,preinfo1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,body)) ,e* ...)
      (when (= interface (length e*)) (register-helpers x* e*))
      (for-each Expr e*) (enter x* (lambda () (Expr body))) ir])
    (CaseLambdaClause : CaseLambdaClause (ir) -> CaseLambdaClause ()
     [(clause (,x* ...) ,interface ,body)
      (enter x* (lambda () (Expr body))) ir]))
   (scan ir))
  ;; Every copied binder gets a fresh prelex. Free lexical references stay free.
  ;; Copy all flags; the successful whole pass recomputes reference flags.
  (define (fresh-helper-body ir)
   (define renames '())
   (define (rename x) (cond [(assq x renames) => cdr] [else x]))
   (define (enter x* thunk)
    (let ([y* (map (lambda (x) (make-prelex (prelex-name x) (prelex-flags x)
                                  (prelex-source x) #f)) x*)])
     (fluid-let ([renames (append (map cons x* y*) renames)]) (thunk y*))))
   (define-pass copy : Lsrc (ir) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
     [(ref ,maybe-src ,x) `(ref ,maybe-src ,(rename x))]
     [(set! ,maybe-src ,x ,[e]) `(set! ,maybe-src ,(rename x) ,e)]
     [(letrec ([,x* ,e*] ...) ,body)
      (enter x* (lambda (x2*) `(letrec ([,x2* ,(map Expr e*)] ...) ,(Expr body))))]
     [(letrec* ([,x* ,e*] ...) ,body)
      (enter x* (lambda (x2*) `(letrec* ([,x2* ,(map Expr e*)] ...) ,(Expr body))))])
    (CaseLambdaClause : CaseLambdaClause (ir) -> CaseLambdaClause ()
     [(clause (,x* ...) ,interface ,body)
      (enter x* (lambda (x2*) `(clause (,x2* ...) ,interface ,(Expr body))))]))
   (copy ir))
  (define (helper-position args p rtd)
   (let loop ([as args] [i 0])
    (and (pair? as)
     (if (nanopass-case (Lsrc Expr) (car as)
          [(ref ,maybe-src ,x) (eq? p x)] [else #f])
      i (loop (cdr as) (+ i 1))))))
  ;; Cache entries: #(original-function position clone-variable rhs-or-#f).
  ;; A placeholder is installed before visiting a body, permitting SCCs.
  (define (find-helper-clone f position)
   (find (lambda (v) (and (eq? f (vector-ref v 0)) (= position (vector-ref v 1)))) helper-clones))
  (define (helper-visible? f)
   (let ([scope (eq-hashtable-ref helper-scopes f #f)])
    (and scope (memq (car scope) helper-origin))))
  (define (helper-call f args p rtd fields visit fail)
   (let* ([position (and cost-mode (helper-position args p rtd))]
          [proc (and (or (not cost-mode) position) (known-helper f))]
          [position (and proc (if cost-mode position (helper-position args p rtd)))])
    (and position
     (begin
      (set! helper-attempts (+ 1 helper-attempts))
      (nanopass-case (Lsrc Expr) proc
       [(case-lambda ,preinfo (clause (,x* ...) ,interface ,body))
        (unless (= interface (length args)) (helper-reject 'arity fail))
        (when (prelex-assigned (list-ref x* position)) (helper-reject 'assigned-argument fail))
        (if (eq? helper-mode 'inline)
         (begin
          (when (or (> (sra-size body) 256) (memq f helper-stack))
           (helper-reject 'inline-size-or-cycle fail))
          (set! helper-fuel (- helper-fuel (sra-size body)))
          (when (< helper-fuel 0) (helper-reject 'budget fail))
          (nanopass-case (Lsrc Expr) (fresh-helper-body proc)
           [(case-lambda ,preinfo (clause (,x2* ...) ,interface ,body))
            (let* ([q (list-ref x2* position)]
                   [new-body (fluid-let ([helper-stack (cons f helper-stack)])
                               ;; The helper may also capture the outer candidate.
                               ;; Process those free uses in the caller's context.
                               (visit (rewrite-region body q rtd fields #f #f '() fail) #t))]
                   [keep-x* (append (list-head x2* position) (list-tail x2* (+ position 1)))]
                   [keep-args (append (list-head args position) (list-tail args (+ position 1)))])
             (set! helper-inline-count (+ helper-inline-count 1))
             (with-output-language (Lsrc Expr)
              `(call ,(make-preinfo-call)
                (case-lambda ,preinfo (clause (,keep-x* ...) ,(length keep-x*) ,new-body))
                ,(map (lambda (e) (visit e #f)) keep-args) ...)))]))
         (begin
          ;; Clones are emitted at the allocation's lexical scope. Only helpers
          ;; already in scope there can be cloned at that scope.
          (unless (helper-visible? f) (helper-reject 'clone-scope fail))
          (let ([entry (or (find-helper-clone f position)
                       (begin
                        (when (or (>= (length helper-clones) 32) (> (sra-size body) 4096))
                         (helper-reject 'clone-size fail))
                        (set! helper-fuel (- helper-fuel (sra-size body)))
                        (when (< helper-fuel 0) (helper-reject 'budget fail))
                        (let ([v (vector f position (make-sra-prelex 'sra-helper) #f)])
                         (set! helper-clones (cons v helper-clones))
                         (nanopass-case (Lsrc Expr) (fresh-helper-body proc)
                          [(case-lambda ,preinfo (clause (,x2* ...) ,interface ,body))
                           (let* ([q (list-ref x2* position)]
                                  [fs (map (lambda (i) (make-sra-prelex 'sra-parameter)) (iota (field-count rtd)))]
                                  [new-x* (append (list-head x2* position) fs (list-tail x2* (+ position 1)))]
                                  [new-body (rewrite-region body q rtd fs #f #f '() fail)])
                            (vector-set! v 3
                             (with-output-language (Lsrc Expr)
                              `(case-lambda ,preinfo (clause (,new-x* ...) ,(length new-x*) ,new-body)))))])
                         v)))])
           (with-output-language (Lsrc Expr)
            `(call ,(make-preinfo-call) ,(ref (vector-ref entry 2))
              ,(append (map (lambda (e) (visit e #f)) (list-head args position))
                       (map ref fields)
                       (map (lambda (e) (visit e #f)) (list-tail args (+ position 1)))) ...)))))])))))
  (define (attempt-helpers x e thunk)
   (if (eq? helper-mode 'off) (thunk)
    (fluid-let ([helper-origin (eq-hashtable-ref helper-scopes x '())]
                [helper-clones '()] [helper-stack '()] [helper-fuel 30000]
                [helper-inline-count 0])
     (let ([answer (thunk)])
      (and answer
       (begin
        (set! helper-eliminated (cons x helper-eliminated))
        (when (or (> helper-inline-count 0) (pair? helper-clones))
         (set! helper-roots (+ 1 helper-roots))
         (when (getenv "CHEZ_SRA_REPORT")
      (fprintf (console-error-port) "SRA-HELPERS roots=~s inline=~s clones=~s attempts=~s failures=~s\n"
       helper-roots helper-total-inline helper-total-clones helper-attempts
       (map (lambda (k) (list k (eq-hashtable-ref helper-failures k 0)))
            (vector->list (hashtable-keys helper-failures)))))
     (when (getenv "CHEZ_SRA_REPORT")
          (fprintf (console-error-port) "SRA-HELPER-SUCCESS ~s ~s inline=~s clones=~s\n"
           (prelex-name x) (initial-shape e) helper-inline-count
           (map (lambda (v) (prelex-name (vector-ref v 0))) helper-clones))))
        (set! helper-total-inline (+ helper-total-inline helper-inline-count))
        (set! helper-total-clones (+ helper-total-clones (length helper-clones)))
        (if (null? helper-clones) answer
         (with-output-language (Lsrc Expr)
          `(letrec ([,(map (lambda (v) (vector-ref v 2)) helper-clones)
                     ,(map (lambda (v) (vector-ref v 3)) helper-clones)] ...) ,answer)))))))))

  ;; Binding/reference helpers follow cpcse; its loop shape is reused below.
  (define (ref x)
   ;; Failed candidates must not mutate metadata on the original program.
   ;; Recompute flags once, after a successful whole-pass transformation.
   (with-output-language (Lsrc Expr) `(ref #f ,x)))
  (define (bind x rhs body)
   (with-output-language (Lsrc Expr)
    `(call ,(make-preinfo-call)
      (case-lambda ,(make-preinfo-lambda) (clause (,x) 1 ,body)) ,rhs)))
  (define (bind-all e* k)
   (if (null? e*) (k '())
    (let ([x (make-sra-prelex 'sra-value)])
     (bind x (car e*) (bind-all (cdr e*) (lambda (x*) (k (cons x x*))))))))
  (define (initial-shape e)
   (nanopass-case (Lsrc Expr) e
    [(call ,preinfo1 ,pr ,e1 ,e2)
     (guard (eq? (primref-name pr) 'cons)) 'pair]
    [(record ,rtd ,rtd-expr ,e* ...) (and (fresh-shape? rtd) rtd)]
    [(quote ,d) (and (record? d) (let ([rtd (record-rtd d)]) (and (shape? rtd) rtd)))]
    [(seq ,e1 ,e2) (initial-shape e2)]
    [(if ,e0 ,e1 ,e2) (let ([rtd (initial-shape e1)]) (and rtd (eq? rtd (initial-shape e2)) rtd))]
    [(call ,preinfo1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,body)) ,e* ...)
     (and (= interface (length e*)) (initial-shape body))]
    [else #f]))
  ;; A known layout alone does not prove a dynamic record predicate. Retain
  ;; the exact, stable descriptor identity from entry and every constructor.
  (define (descriptor-key e)
   (nanopass-case (Lsrc Expr) e
    [(quote ,d) (cons 'quote d)]
    [(ref ,maybe-src ,x) (and (not (prelex-assigned x)) (cons 'ref x))]
    [else #f]))
  (define (same-descriptor? a b)
   (and a b (eq? (car a) (car b)) (eq? (cdr a) (cdr b))))
  (define (initial-descriptor e)
   (nanopass-case (Lsrc Expr) e
    [(record ,rtd ,rtd-expr ,e* ...) (descriptor-key rtd-expr)]
    [(quote ,d) (and (record? d) (cons 'quote (record-rtd d)))]
    [(seq ,e1 ,e2) (initial-descriptor e2)]
    [(if ,e0 ,e1 ,e2)
     (let ([a (initial-descriptor e1)])
      (and (same-descriptor? a (initial-descriptor e2)) a))]
    [(call ,preinfo1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,body)) ,e* ...)
     (and (= interface (length e*)) (initial-descriptor body))]
    [else #f]))
  (define (mentions? e x*)
   (call/cc (lambda (found)
    (define-pass scan : Lsrc (ir) -> Lsrc ()
     (Expr : Expr (ir) -> Expr ()
      [(ref ,maybe-src ,x) (when (memq x x*) (found #t)) ir]
      [(set! ,maybe-src ,x ,[e]) (when (memq x x*) (found #t)) ir]))
    (scan e) #f)))
  (define (split-value e rtd visit fail k)
   (set! split-fuel (- split-fuel 1))
   (when (< split-fuel 0) (fail #f))
   (with-output-language (Lsrc Expr)
    (nanopass-case (Lsrc Expr) e
     [(call ,preinfo1 ,pr ,e1 ,e2)
      (guard (eq? (primref-name pr) 'cons))
      (unless (eq? rtd 'pair) (fail #f))
      ;; Keep both initializers, including effects/errors in an unused slot.
      (bind-all (list (visit e1 #f) (visit e2 #f)) k)]
     [(record ,rtd1 ,rtd-expr1 ,e* ...)
      (unless (and (eq? rtd1 rtd) (= (length e*) (field-count rtd))) (fail #f))
      (when (and candidate-descriptor
                 (not (same-descriptor? candidate-descriptor (descriptor-key rtd-expr1))))
       (fail #f))
      ;; Preserve evaluation of the descriptor and every initializer, even unused ones.
      `(seq ,(visit rtd-expr1 #f)
        ,(bind-all (map (lambda (e) (visit e #f)) e*) k))]
     [(quote ,d)
      (unless (and (record? d) (shape? rtd) (eq? (record-rtd d) rtd)) (fail #f))
      (when (and candidate-descriptor
                 (not (same-descriptor? candidate-descriptor (cons 'quote (record-rtd d)))))
       (fail #f))
      (bind-all (map (lambda (index) `(quote ,((record-accessor rtd index) d)))
                    (iota (field-count rtd))) k)]
     [(if ,e0 ,e1 ,e2)
      ;; Share the continuation: duplicating k could duplicate existing prelex
      ;; binders (including a loop definition) across the two branches.
      (let ([join (make-sra-prelex 'sra-join)]
            [fields (map (lambda (index) (make-sra-prelex 'sra-merge))
                         (iota (field-count rtd)))])
       (define (send fields)
        `(call ,(make-preinfo-call) ,(ref join) ,(map ref fields) ...))
       (bind join
        `(case-lambda ,(make-preinfo-lambda)
          (clause (,fields ...) ,(length fields) ,(k fields)))
        `(if ,(visit e0 #f) ,(split-value e1 rtd visit fail send)
                          ,(split-value e2 rtd visit fail send))))]
     [(seq ,e1 ,e2) `(seq ,(visit e1 #f) ,(split-value e2 rtd visit fail k))]
     [(call ,preinfo1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,body)) ,e* ...)
      (unless (= interface (length e*)) (fail #f))
      `(call ,preinfo1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,(split-value body rtd visit fail k)))
             ,(map (lambda (e) (visit e #f)) e*) ...)]
     [else (fail #f)])))
  ;; Abort an entire candidate when any use observes the object instead of its fields.
  (define (rewrite-region body p rtd fields x1 position formals fail)
   (define (field index)
    (unless (and (fixnum? index) (fx<= 0 index) (fx< index (length fields))) (fail #f))
    (ref (list-ref fields index)))
   (define (call-loop e*)
    (unless (= (length e*) (length formals)) (fail #f))
    (let loop ([before '()] [as e*] [index 0])
     (if (= index position)
      (split-value (car as) rtd visit fail
       (lambda (fs)
        (bind-all (map (lambda (e) (visit e #f)) (cdr as))
         (lambda (after)
          (with-output-language (Lsrc Expr)
           `(call ,(make-preinfo-call) ,(ref x1) ,(map ref (append (reverse before) fs after)) ...))))))
      (let ([x (make-sra-prelex 'sra-arg)])
       (bind x (visit (car as) #f) (loop (cons x before) (cdr as) (+ index 1)))))))
   (define-pass visit : Lsrc (ir tail?) -> Lsrc ()
    (Expr : Expr (ir tail?) -> Expr ()
     [(call ,preinfo1 ,pr (ref ,maybe-src ,x))
      (guard (and (eq? rtd 'pair) (eq? x p)
                  (memq (primref-name pr) '(car cdr pair? null?))))
      (case (primref-name pr)
       [(car) (field 0)]
       [(cdr) (field 1)]
       [(pair?) `(quote #t)]
       [(null?) `(quote #f)])]
     [(call ,preinfo1 ,pr (ref ,maybe-src ,x) ,e)
      (guard (and (eq? x p) (eq? (primref-name pr) 'record?)))
      (unless (same-descriptor? candidate-descriptor (descriptor-key e)) (fail #f))
      `(quote #t)]
     [(record-ref ,rtd1 ,type ,index (ref ,maybe-src ,x))
      (guard (eq? x p))
      (unless (and (not (eq? rtd 'pair)) (ancestor? rtd1 rtd)) (fail #f))
      (field index)]
     [(call ,preinfo1 ,pr (quote ,d1) (ref ,maybe-src ,x) (quote ,d2))
      (guard (and (eq? x p) (eq? (primref-name pr) '$object-ref)))
      (unless (and (not (eq? rtd 'pair)) (eq? d1 'scheme-object)) (fail #f))
      (let loop ([index 0])
       (cond [(= index (field-count rtd)) (fail #f)]
             [(eqv? d2 (field-offset rtd index)) (field index)]
             [else (loop (+ index 1))]))]
     [(call ,preinfo1 ,pr (ref ,maybe-src ,x) (quote ,d))
      (guard (and (eq? x p) (eq? (primref-name pr) '$record-ref)))
      (when (eq? rtd 'pair) (fail #f))
      (field d)]
     [(call ,preinfo1 (ref ,maybe-src ,x) ,e* ...)
      (guard (and x1 (eq? x x1)))
      (unless tail? (fail #f))
      (call-loop e*)]
     [(ref ,maybe-src ,x) (when (or (eq? x p) (and x1 (eq? x x1))) (fail #f)) ir]
     [(set! ,maybe-src ,x ,e)
      (when (or (eq? x p) (and x1 (eq? x x1))) (fail #f))
      `(set! ,maybe-src ,x ,(Expr e #f))]
     [(if ,e0 ,e1 ,e2)
      (let ([test (Expr e0 #f)])
       (nanopass-case (Lsrc Expr) test
        [(quote ,d) (Expr (if d e1 e2) tail?)]
        [else `(if ,test ,(Expr e1 tail?) ,(Expr e2 tail?))]))]
     [(seq ,e1 ,e2) `(seq ,(Expr e1 #f) ,(Expr e2 tail?))]
     [(call ,preinfo1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,body)) ,e* ...)
      (guard (= interface (length e*)))
      `(call ,preinfo1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,(Expr body tail?)))
             ,(map (lambda (e) (Expr e #f)) e*) ...)]
     [(case-lambda ,preinfo2 ,cl* ...)
      (when (and x1 (mentions? ir (list x1))) (fail #f))
      `(case-lambda ,preinfo2
        ,(map (lambda (cl)
          (nanopass-case (Lsrc CaseLambdaClause) cl
           [(clause (,x* ...) ,interface ,body)
            (with-output-language (Lsrc CaseLambdaClause)
             `(clause (,x* ...) ,interface ,(Expr body #t)))])) cl*) ...)]
     [(call ,preinfo1 (ref ,maybe-src ,x) ,e* ...)
      (guard (not (eq? helper-mode 'off)))
      (or (helper-call x e* p rtd fields visit fail)
          `(call ,preinfo1 ,(Expr (ref x) #f) ,(map (lambda (e) (Expr e #f)) e*) ...))]
     [(call ,preinfo1 ,e ,e* ...) `(call ,preinfo1 ,(Expr e #f) ,(map (lambda (e) (Expr e #f)) e*) ...)]
     [(letrec ([,x* ,e*] ...) ,body)
      `(letrec ([,x* ,(map (lambda (e) (Expr e #f)) e*)] ...) ,(Expr body tail?))]
     [(letrec* ([,x* ,e*] ...) ,body)
      `(letrec* ([,x* ,(map (lambda (e) (Expr e #f)) e*)] ...) ,(Expr body tail?))])
    (Expr ir tail?))
   (visit body #t))
  ;; Count only enough nodes to answer the eligibility question. The old guard
  ;; traversed the entire body even when the first 4096 nodes already reject it.
  ;; Count the same Expr + CaseLambdaClause nodes as count-Lsrc.
  (define (body-small/raw? ir)
   (if (not (equal? cost-mode "bounded")) (< (sra-size ir) 4096)
    (call/cc
     (lambda (too-large)
      (define remaining 4096)
      (define (tick n)
       (set! remaining (fx- remaining n))
       (when (fx<= remaining 0) (too-large #f)))
      (define (walk ir)
       (tick 1)
       (nanopass-case (Lsrc Expr) ir
        [(if ,e0 ,e1 ,e2) (walk e0) (walk e1) (walk e2)]
        [(seq ,e0 ,e1) (walk e0) (walk e1)]
        [(set! ,maybe-src ,x ,e) (walk e)]
        [(case-lambda ,preinfo ,cl* ...)
         (for-each (lambda (cl) (tick 1)
          (nanopass-case (Lsrc CaseLambdaClause) cl
           [(clause (,x* ...) ,interface ,body) (walk body)])) cl*)]
        [(letrec ([,x* ,e*] ...) ,body) (for-each walk e*) (walk body)]
        [(letrec* ([,x* ,e*] ...) ,body) (for-each walk e*) (walk body)]
        [(call ,preinfo ,e0 ,e* ...) (walk e0) (for-each walk e*)]
        [(record-type ,rtd ,e) (walk e)]
        [(record-cd ,rcd ,rtd-expr ,e) (walk rtd-expr) (walk e)]
        [(immutable-list (,e* ...) ,e) (for-each walk e*) (walk e)]
        [(immutable-vector (,e* ...) ,e) (for-each walk e*) (walk e)]
        [(record ,rtd ,rtd-expr ,e* ...) (walk rtd-expr) (for-each walk e*)]
        [(record-ref ,rtd ,type ,index ,e) (walk e)]
        [(record-set! ,rtd ,type ,index ,e1 ,e2) (walk e1) (walk e2)]
        [(cte-optimization-loc ,box ,e ,exts) (walk e)]
        [(foreign (,conv* ...) ,name ,e (,arg-type* ...) ,result-type) (walk e)]
        [(fcallable (,conv* ...) ,e (,arg-type* ...) ,result-type) (walk e)]
        [(cpvalid-defer ,e) (walk e)]
        [else (void)]))
      (walk ir) #t))))

  (define (body-small? ir)
   (let ([answer (body-small/raw? ir)])
    (when (getenv "CHEZ_SRA_BOUND_VERIFY")
     (unless (eq? answer (< (count-Lsrc ir) 4096))
      ($oops 'cpsra "bounded eligibility count mismatch")))
    answer))
  (define (try-local/raw x e body)
   (and (not (prelex-assigned x))
    (let ([rtd (initial-shape e)])
     (and rtd
      (call/cc (lambda (fail)
       (split-value e rtd (lambda (e tail?) e) fail
        (lambda (fields) (rewrite-region body x rtd fields #f #f '() fail)))))))))
  (define (try-local x e body)
   (when (initial-shape e) (set! local-candidates (+ local-candidates 1)))
   (let ([answer (and (initial-shape e) (body-small? body)
                  (fluid-let ([split-fuel 64] [candidate-descriptor (initial-descriptor e)])
                   (attempt-helpers x e (lambda () (try-local/raw x e body)))))])
    (when answer (set! local-count (+ local-count 1))) answer))
  (define (try-loop/raw x1 preinfo2 x* interface body preinfo1 maybe-src e*)
   (and (not (prelex-assigned x1)) (= interface (length x*)) (= interface (length e*))
    (not (ormap (lambda (e) (mentions? e (list x1))) e*))
    (let loop ([ps x*] [as e*] [pos 0])
     (and (pair? ps)
      (or
       (and (not (prelex-assigned (car ps)))
        (fluid-let ([candidate-descriptor (initial-descriptor (car as))])
         (let ([rtd (initial-shape (car as))])
         (and rtd
          (call/cc (lambda (fail)
           (let* ([fields (map (lambda (index) (make-sra-prelex 'sra-field)) (iota (field-count rtd)))]
                  [body (rewrite-region body (car ps) rtd fields x1 pos x* fail)]
                  [new-xs (append (list-head x* pos) fields (list-tail x* (+ pos 1)))])
            (let bind-entry ([as e*] [before '()] [index 0])
             (if (= index pos)
              (split-value (car as) rtd (lambda (e tail?) e) fail
               (lambda (initial)
                (bind-all (cdr as)
                 (lambda (after)
                  (with-output-language (Lsrc Expr)
                   `(letrec ([,x1 (case-lambda ,preinfo2 (clause (,new-xs ...) ,(length new-xs) ,body))])
                     (call ,preinfo1 ,(ref x1) ,(map ref (append (reverse before) initial after)) ...)))))))
              (let ([x (make-sra-prelex 'sra-entry)])
               (bind x (car as) (bind-entry (cdr as) (cons x before) (+ index 1)))))))))))))
       (loop (cdr ps) (cdr as) (+ pos 1)))))))
  (define (try-loop x1 preinfo2 x* interface body preinfo1 maybe-src e*)
   (let ([answer (and (eq? helper-mode 'off) (ormap initial-shape e*) (body-small? body)
                  (fluid-let ([split-fuel 64])
                   (try-loop/raw x1 preinfo2 x* interface body preinfo1 maybe-src e*)))])
    (when answer (set! loop-count (+ loop-count 1))) answer))
  ;; Optimize a lambda body in an isolated environment. Synthetic formals stand
  ;; for all free variables, including assigned ones. Clone before recomputing
  ;; flags, so rejected trials cannot mutate the surrounding compiler state.
  (define (isolated-cp0 body)
   (define bound (make-eq-hashtable))
   (define free (make-eq-hashtable))
   (define free-order '())
   (define unsupported? #f)
   (define (note-free! x)
    (unless (or (eq-hashtable-ref bound x #f) (eq-hashtable-ref free x #f))
     (eq-hashtable-set! free x #t)
     (set! free-order (cons x free-order))))
   (define-pass bindings : Lsrc (ir) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
     [(cte-optimization-loc ,box ,e ,exts) (set! unsupported? #t) ir]
     [(letrec ([,x* ,[e*]] ...) ,[body])
      (for-each (lambda (x) (eq-hashtable-set! bound x #t)) x*) ir]
     [(letrec* ([,x* ,[e*]] ...) ,[body])
      (for-each (lambda (x) (eq-hashtable-set! bound x #t)) x*) ir])
    (CaseLambdaClause : CaseLambdaClause (ir) -> CaseLambdaClause ()
     [(clause (,x* ...) ,interface ,[body])
      (for-each (lambda (x) (eq-hashtable-set! bound x #t)) x*) ir]))
   (define-pass uses : Lsrc (ir) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
     [(ref ,maybe-src ,x)
      (note-free! x) ir]
     [(set! ,maybe-src ,x ,[e])
      (note-free! x) ir]))
   (bindings body) (uses body)
   (and (not unsupported?)
   (let* ([xs (reverse free-order)]
          [wrapper (with-output-language (Lsrc Expr)
                    `(case-lambda ,(make-preinfo-lambda)
                      (clause (,xs ...) ,(length xs) ,body)))]
          [wrapper (mark-refs (clear-bound (fresh-helper-body wrapper)))]
          [out ($pass-time 'cpsra-local-cp0 (lambda () (let* ([x ($cp0 wrapper)] [x (if (and (equal? region-mode "types") (enable-type-recovery)) ($cptypes x) x)]) ($cpletrec x))))])
    (nanopass-case (Lsrc Expr) out
     [(case-lambda ,preinfo (clause (,x2* ...) ,interface ,body))
      (unless (and (= interface (length xs)) (= (length x2*) (length xs)))
       ($oops 'cpsra "local CP0 changed wrapper arity"))
      (let ([mapping (map cons x2* xs)])
       (define (rename x) (cond [(assq x mapping) => cdr] [else x]))
       (define-pass restore : Lsrc (ir) -> Lsrc ()
        (Expr : Expr (ir) -> Expr ()
         [(ref ,maybe-src ,x) `(ref ,maybe-src ,(rename x))]
         [(set! ,maybe-src ,x ,[e]) `(set! ,maybe-src ,(rename x) ,e)]))
       (restore body))]
     [else ($oops 'cpsra "local CP0 lost wrapper lambda")])))
  )
  (define (allocation-count body)
   (define n 0)
   (define-pass scan : Lsrc (ir) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
     [(record ,rtd ,[rtd-expr] ,[e*] ...) (set! n (+ n 1)) ir]
     [(call ,preinfo ,pr ,[e*] ...)
      (guard (eq? (primref-name pr) 'cons))
      (set! n (+ n 1)) ir]))
   (scan body) n)
  (define (refine-body body changed? candidates?)
   (if (or local-active? (not local-mode)
           (not (or changed? (and (eq? local-mode 'retry) candidates?))))
    body
    (let loop ([body body] [rounds 2] [changed? changed?])
     (let ([size (sra-size body)])
      (if (or (= rounds 0) (> size (if (equal? (getenv "CHEZ_SRA_LOCAL_MAX") "8192") 8192 2048)) (> size local-fuel)) body
       (begin
        (set! local-fuel (- local-fuel size))
        (set! local-trials (+ local-trials 1))
        (let* ([before (+ local-count loop-count)]
               [trial (isolated-cp0 body)]
               [trial (and trial (fluid-let ([local-active? #t])
                        (collect-helpers trial)
                        (transform trial)))]
               [more? (or (> (+ local-count loop-count) before)
                          (and trial (< (allocation-count trial) (allocation-count body))))])
         (if (and trial (or changed? more?))
          (begin
           (set! local-commits (+ local-commits 1))
           (if more? (loop trial (- rounds 1) #t) trial))
          body))))))))

  ;; Worklist regions include their binding forms and loop entry/backedge scope.
  ;; Scalar binders introduced by successful SRA are the change signal. Failed
  ;; trial binders never occur in the output, so they cannot enqueue a region.
  (define-threaded region-mode)
  (define-threaded region-marks)
  (define-threaded region-trials)
  (define-threaded region-commits)
  (define-threaded region-nodes)
  (define-threaded region-root-commits)
  (define (make-sra-prelex name)
   (let ([x (make-prelex* name)])
    (when region-mode (eq-hashtable-set! region-marks x #t)) x))
  (define (region-children ir)
   (nanopass-case (Lsrc Expr) ir
    [(if ,e0 ,e1 ,e2) (list e0 e1 e2)]
    [(seq ,e0 ,e1) (list e0 e1)]
    [(set! ,maybe-src ,x ,e) (list e)]
    [(case-lambda ,preinfo ,cl* ...)
     (map (lambda (cl) (nanopass-case (Lsrc CaseLambdaClause) cl
            [(clause (,x* ...) ,interface ,body) body])) cl*)]
    [(letrec ([,x* ,e*] ...) ,body) (cons body e*)]
    [(letrec* ([,x* ,e*] ...) ,body) (cons body e*)]
    [(call ,preinfo ,e0 ,e* ...) (cons e0 e*)]
    [(record-type ,rtd ,e) (list e)]
    [(record-cd ,rcd ,rtd-expr ,e) (list rtd-expr e)]
    [(immutable-list (,e* ...) ,e) (cons e e*)]
    [(immutable-vector (,e* ...) ,e) (cons e e*)]
    [(record ,rtd ,rtd-expr ,e* ...) (cons rtd-expr e*)]
    [(record-ref ,rtd ,type ,index ,e) (list e)]
    [(record-set! ,rtd ,type ,index ,e1 ,e2) (list e1 e2)]
    [(cte-optimization-loc ,box ,e ,exts) (list e)]
    [(foreign (,conv* ...) ,name ,e (,arg-type* ...) ,result-type) (list e)]
    [(fcallable (,conv* ...) ,e (,arg-type* ...) ,result-type) (list e)]
    [(cpvalid-defer ,e) (list e)]
    [else '()]))
  (define (cleanup-regions input)
   (define cache (make-eq-hashtable))
   ;; One linear index per sweep; n counts Expr nodes, not source characters.
   (define (info ir)
    (or (eq-hashtable-ref cache ir #f)
     (let* ([cs (map info (region-children ir))]
            [changed (or (ormap (lambda (v) (vector-ref v 1)) cs)
                         (nanopass-case (Lsrc Expr) ir
                          [(ref ,maybe-src ,x) (eq-hashtable-ref region-marks x #f)]
                          [else #f]))]
            [unsupported (or (ormap (lambda (v) (vector-ref v 2)) cs)
                             (nanopass-case (Lsrc Expr) ir
                              [(cte-optimization-loc ,box ,e ,exts) #t] [else #f]))]
            [v (vector (+ 1 (apply + (map (lambda (v) (vector-ref v 0)) cs))) changed unsupported)])
      (eq-hashtable-set! cache ir v) v)))
   (define (scope? ir)
    (nanopass-case (Lsrc Expr) ir
     [(letrec ([,x* ,e*] ...) ,body) #t]
     [(letrec* ([,x* ,e*] ...) ,body) #t]
     [(call ,preinfo (case-lambda ,preinfo2 ,cl* ...) ,e* ...) #t]
     [(call ,preinfo (letrec ([,x* ,e*] ...) ,body) ,e1* ...) #t]
     [(case-lambda ,preinfo ,cl* ...) #t]
     [else #f]))
   (define (sra trial)
    (fluid-let ([local-active? #t] [helper-mode 'off]
                [helper-definitions (make-eq-hashtable)]
                [helper-scopes (make-eq-hashtable)])
     (let ([out (transform trial)])
      (if (member (getenv "CHEZ_SRA_HELPERS") '("inline" "specialize"))
       (begin (collect-helpers out)
        (fluid-let ([helper-mode (string->symbol (getenv "CHEZ_SRA_HELPERS"))])
         (transform out))) out))))
   (define (try ir root?)
    (define (round ir remaining first?)
     (let* ([v (info ir)] [n (vector-ref v 0)])
      (and (> remaining 0) (or (not first?) (vector-ref v 1)) (not (vector-ref v 2))
           (<= n (if (equal? (getenv "CHEZ_SRA_REGION_LIMIT") "2048") 2048 8192))
           (<= (+ region-nodes n) 32768)
       (begin
        (set! region-trials (+ region-trials 1))
        (set! region-nodes (+ region-nodes n))
        (let* ([before (+ local-count loop-count)]
               [trial (isolated-cp0 ir)]
               [trial (and trial (sra trial))])
         (and trial (<= (sra-size trial) (+ 256 (* 3 n)))
          (begin
           (set! region-commits (+ region-commits 1))
           (when root? (set! region-root-commits (+ region-root-commits 1)))
           (when (getenv "CHEZ_REGION_REPORT")
            (fprintf (console-error-port)
             "SRA-REGION-COMMIT root=~s input=~s output=~s new-sra=~s allocations=~s/~s\n"
             root? n (sra-size trial) (- (+ local-count loop-count) before)
             (allocation-count ir) (allocation-count trial)))
           (or (and (or (> (+ local-count loop-count) before)
                        (< (allocation-count trial) (allocation-count ir)))
                    (round trial (- remaining 1) #f))
               trial))))))))
    (round ir (if (equal? region-mode "scope2") 2 1) #t))
   (define (visit ir root?)
    (or (and (or root? (scope? ir)) (try ir root?)) (descend ir)))
   (define-pass descend : Lsrc (ir) -> Lsrc ()
    (Expr : Expr (ir) -> Expr ()
     [(cte-optimization-loc ,box ,e ,exts) ir]
     [(if ,e0 ,e1 ,e2) `(if ,(visit e0 #f) ,(visit e1 #f) ,(visit e2 #f))]
     [(seq ,e0 ,e1) `(seq ,(visit e0 #f) ,(visit e1 #f))]
     [(set! ,maybe-src ,x ,e) `(set! ,maybe-src ,x ,(visit e #f))]
     [(case-lambda ,preinfo ,cl* ...)
      `(case-lambda ,preinfo ,(map (lambda (cl)
         (nanopass-case (Lsrc CaseLambdaClause) cl
          [(clause (,x* ...) ,interface ,body)
           (with-output-language (Lsrc CaseLambdaClause)
            `(clause (,x* ...) ,interface ,(visit body #f)))])) cl*) ...)]
     [(letrec ([,x* ,e*] ...) ,body)
      `(letrec ([,x* ,(map (lambda (e) (visit e #f)) e*)] ...) ,(visit body #f))]
     [(letrec* ([,x* ,e*] ...) ,body)
      `(letrec* ([,x* ,(map (lambda (e) (visit e #f)) e*)] ...) ,(visit body #f))]
     [(call ,preinfo ,e0 ,e* ...)
      `(call ,preinfo ,(visit e0 #f) ,(map (lambda (e) (visit e #f)) e*) ...)]
     [(record-type ,rtd ,e) `(record-type ,rtd ,(visit e #f))]
     [(record-cd ,rcd ,rtd-expr ,e) `(record-cd ,rcd ,(visit rtd-expr #f) ,(visit e #f))]
     [(immutable-list (,e* ...) ,e) `(immutable-list (,(map (lambda (e) (visit e #f)) e*) ...) ,(visit e #f))]
     [(immutable-vector (,e* ...) ,e) `(immutable-vector (,(map (lambda (e) (visit e #f)) e*) ...) ,(visit e #f))]
     [(record ,rtd ,rtd-expr ,e* ...) `(record ,rtd ,(visit rtd-expr #f) ,(map (lambda (e) (visit e #f)) e*) ...)]
     [(record-ref ,rtd ,type ,index ,e) `(record-ref ,rtd ,type ,index ,(visit e #f))]
     [(record-set! ,rtd ,type ,index ,e1 ,e2) `(record-set! ,rtd ,type ,index ,(visit e1 #f) ,(visit e2 #f))]
     [(foreign (,conv* ...) ,name ,e (,arg-type* ...) ,result-type)
      `(foreign (,conv* ...) ,name ,(visit e #f) (,arg-type* ...) ,result-type)]
     [(fcallable (,conv* ...) ,e (,arg-type* ...) ,result-type)
      `(fcallable (,conv* ...) ,(visit e #f) (,arg-type* ...) ,result-type)]
     [(cpvalid-defer ,e) `(cpvalid-defer ,(visit e #f))]))
   (visit input #t))

  (define-pass transform : Lsrc (ir) -> Lsrc ()
   (Expr : Expr (ir) -> Expr ()
    [(case-lambda ,preinfo ,cl* ...)
     `(case-lambda ,preinfo
       ,(map (lambda (cl)
          (nanopass-case (Lsrc CaseLambdaClause) cl
           [(clause (,x* ...) ,interface ,body)
            (let* ([before (+ local-count loop-count)]
                   [candidates local-candidates]
                   [body (Expr body)]
                   [body (refine-body body (> (+ local-count loop-count) before)
                                           (> local-candidates candidates))])
             (with-output-language (Lsrc CaseLambdaClause)
              `(clause (,x* ...) ,interface ,body)))])) cl*) ...)]
    [(letrec ([,x1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,[body]))])
       (call ,preinfo1 (ref ,maybe-src ,x2) ,[e*] ...))
     (guard (eq? x1 x2))
     (or (try-loop x1 preinfo2 x* interface body preinfo1 maybe-src e*)
         `(letrec ([,x1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,body))])
            (call ,preinfo1 (ref ,maybe-src ,x2) ,e* ...)))]
    [(call ,preinfo1 (letrec ([,x1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,[body]))])
                 (ref ,maybe-src ,x2)) ,[e*] ...)
     (guard (eq? x1 x2))
     (or (try-loop x1 preinfo2 x* interface body preinfo1 maybe-src e*)
         `(call ,preinfo1 (letrec ([,x1 (case-lambda ,preinfo2 (clause (,x* ...) ,interface ,body))])
                       (ref ,maybe-src ,x2)) ,e* ...))]
    [(call ,preinfo1 (case-lambda ,preinfo2 (clause (,x) ,interface ,[body])) ,[e])
     (guard (= interface 1))
     (or (try-local x e body)
         `(call ,preinfo1 (case-lambda ,preinfo2 (clause (,x) 1 ,body)) ,e))]))
  ;; Recompute reference counts instead of pessimistically marking all variables.
  (define (clear-ref! x)
   (set-prelex-referenced! x #f) (set-prelex-multiply-referenced! x #f))
  (define-pass clear-bound : Lsrc (ir) -> Lsrc ()
   (Expr : Expr (ir) -> Expr ()
    [(letrec ([,x* ,e*] ...) ,body)
     (for-each clear-ref! x*)
     `(letrec ([,x* ,(map Expr e*)] ...) ,(Expr body))]
    [(letrec* ([,x* ,e*] ...) ,body)
     (for-each clear-ref! x*)
     `(letrec* ([,x* ,(map Expr e*)] ...) ,(Expr body))])
   (CaseLambdaClause : CaseLambdaClause (ir) -> CaseLambdaClause ()
    [(clause (,x* ...) ,interface ,body)
     (for-each clear-ref! x*) `(clause (,x* ...) ,interface ,(Expr body))]))
  (define-pass mark-refs : Lsrc (ir) -> Lsrc ()
   (Expr : Expr (ir) -> Expr ()
    [(ref ,maybe-src ,x) (when (prelex-referenced x) (set-prelex-multiply-referenced! x #t))
     (set-prelex-referenced! x #t) ir]))
  (lambda (x)
   (if (enable-scalar-replacement)
    (fluid-let ([cost-mode (let ([v (getenv "CHEZ_SRA_COST")]) (and (member v '("guard" "cache" "bounded")) v))]
                [size-cache (make-eq-hashtable)] [validity-cache (make-eq-hashtable)]
                [region-mode (let ([s (getenv "CHEZ_SRA_REGION_CP0")]) (and (member s '("scope" "scope2" "types")) s))]
                [region-marks (make-eq-hashtable)] [region-trials 0] [region-commits 0]
                [region-nodes 0] [region-root-commits 0]
                [local-mode (let ([v (getenv "CHEZ_SRA_LOCAL_CP0")])
                             (and (member v '("cleanup" "retry")) (string->symbol v)))]
                [local-active? #f] [local-fuel 32768]
                [local-trials 0] [local-commits 0] [local-candidates 0]
                [local-count 0] [loop-count 0] [helper-mode 'off]
                [helper-definitions (make-eq-hashtable)] [helper-scopes (make-eq-hashtable)]
                [helper-total-inline 0] [helper-total-clones 0] [helper-roots 0]
                [helper-attempts 0] [helper-failures (make-eq-hashtable)] [helper-eliminated '()])
     (let* ([out (transform x)]
            [out (let ([mode (getenv "CHEZ_SRA_HELPERS")])
                   (if (member mode '("inline" "specialize"))
                    (begin (collect-helpers out)
                     (fluid-let ([helper-mode (string->symbol mode)]) (transform out)))
                    out))]
            [out (if (and region-mode (> (+ local-count loop-count) 0)) (cleanup-regions out) out)]
            [out (if (and (= region-commits 0) (= local-count 0) (= loop-count 0) (= local-commits 0))
                     x (mark-refs (clear-bound out)))])
     (when (getenv "CHEZ_SRA_REPORT")
      (fprintf (console-error-port) "SRA-HELPERS roots=~s inline=~s clones=~s attempts=~s failures=~s\n"
       helper-roots helper-total-inline helper-total-clones helper-attempts
       (map (lambda (k) (list k (eq-hashtable-ref helper-failures k 0)))
            (vector->list (hashtable-keys helper-failures)))))
     (when (getenv "CHEZ_SRA_REPORT")
      (fprintf (console-error-port) "SRA local=~s loops=~s\n" local-count loop-count))
     (when (getenv "CHEZ_REGION_REPORT")
      (fprintf (console-error-port) "SRA-REGIONS trials=~s commits=~s nodes=~s roots=~s input=~s\n"
       region-trials region-commits region-nodes region-root-commits (sra-size x)))
     (when (getenv "CHEZ_AGGREGATE_REPORT")
      (fprintf (console-error-port) "SRA-LOCAL trials=~s commits=~s nodes=~s\n"
       local-trials local-commits (- 32768 local-fuel)))
     (when (getenv "CHEZ_SRA_DUMP")
      (pretty-print (list 'before (unparse-Lsrc x)) (console-error-port))
      (pretty-print (list 'after (unparse-Lsrc out)) (console-error-port)))
     out))
    x)))))
