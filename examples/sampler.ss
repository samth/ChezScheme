;;; sampler.ss
;;; Using the built-in stack sampler (c/sampler.inc) from Scheme.
;;;
;;; (sample-thunk thunk [hz]) runs thunk while sampling its CPU time and
;;; returns its values; afterward (sampler-stacks) holds the samples as a
;;; list of (stack . count), each stack a list of frame names, outermost
;;; first.
;;;
;;; (sampler-profile-html thunk [prefix]) runs thunk under the sampler and
;;; writes the same colored source listing as profile-dump-html, but with
;;; time instead of execution counts: each procedure is colored by the
;;; share of samples in which it was on the stack. Load code with
;;; generate-inspector-information (the default) so that procedures carry
;;; their source.
;;;
;;; Linux on x86_64 and arm64.

(define sampler-start (foreign-procedure "(cs)sampler_start" (int) int))
(define sampler-stop (foreign-procedure "(cs)sampler_stop" () void))
(define sampler-take (foreign-procedure "(cs)sampler_take" () scheme-object))
(define sampler-config (foreign-procedure "(cs)sampler_config" (int int) void))

(define sampler-stacks (make-parameter '()))

(define (split-string s c)
  (let loop ([i 0] [start 0] [acc '()])
    (cond
      [(= i (string-length s)) (reverse (cons (substring s start i) acc))]
      [(char=? (string-ref s i) c) (loop (+ i 1) (+ i 1) (cons (substring s start i) acc))]
      [else (loop (+ i 1) start acc)])))

(define (parse-folded bv)
  (let ([text (utf8->string bv)])
    (let loop ([lines (split-string text #\newline)] [acc '()])
      (cond
        [(null? lines) (reverse acc)]
        [(string=? (car lines) "") (loop (cdr lines) acc)]
        [else
         (let* ([line (car lines)]
                [sp (let find ([i (- (string-length line) 1)])
                      (if (char=? (string-ref line i) #\space) i (find (- i 1))))])
           (loop (cdr lines)
                 (cons (cons (split-string (substring line 0 sp) #\;)
                             (string->number (substring line (+ sp 1) (string-length line))))
                       acc)))]))))

(define sample-thunk
  (case-lambda
    [(thunk) (sample-thunk thunk 999)]
    [(thunk hz)
     (sampler-take)                     ; discard earlier samples
     (when (< (sampler-start hz) 0) (errorf 'sample-thunk "the sampler is not available"))
     (call-with-values
       (lambda () (dynamic-wind void thunk sampler-stop))
       (lambda results
         (sampler-stacks (parse-folded (sampler-take)))
         (apply values results)))]))

;; "name@/path/file.ss#bfp-efp_[j]" -> (path bfp efp), or #f
(define (frame-source f)
  (let* ([n (string-length f)]
         [f (if (and (> n 4) (string=? (substring f (- n 4) n) "_[j]")) (substring f 0 (- n 4)) f)]
         [n (string-length f)])
    (let find-at ([i (- n 1)])
      (cond
        [(< i 0) #f]
        [(char=? (string-ref f i) #\@)
         (let* ([loc (substring f (+ i 1) n)]
                [parts (split-string loc #\#)])
           (and (= (length parts) 2)
                (let ([se (split-string (cadr parts) #\-)])
                  (and (= (length se) 2)
                       (let ([b (string->number (car se))] [e (string->number (cadr se))])
                         (and b e (list (car parts) b e)))))))]
        [else (find-at (- i 1))]))))

(define sampler-profile-html
  (case-lambda
    [(thunk) (sampler-profile-html thunk "")]
    [(thunk prefix)
     (sampler-config 1 2)               ; full source positions in names
     (call-with-values
       (lambda () (dynamic-wind void (lambda () (sample-thunk thunk)) (lambda () (sampler-config 1 1))))
       (lambda results
         (let ([inclusive (make-hashtable equal-hash equal?)]
               [sfds (make-hashtable string-hash string=?)])
           (for-each
             (lambda (s)
               (let ([seen (make-hashtable equal-hash equal?)])
                 (for-each
                   (lambda (f)
                     (let ([src (frame-source f)])
                       (when (and src (not (hashtable-ref seen src #f)))
                         (hashtable-set! seen src #t)
                         (hashtable-update! inclusive src (lambda (c) (+ c (cdr s))) 0))))
                   (car s))))
             (sampler-stacks))
           (let ([dump
                  (let-values ([(keys vals) (hashtable-entries inclusive)])
                    (let loop ([i 0] [acc '()])
                      (if (= i (vector-length keys))
                          acc
                          (let* ([k (vector-ref keys i)]
                                 [path (car k)]
                                 [sfd (or (hashtable-ref sfds path #f)
                                          (and (file-exists? path)
                                               (let ([sfd (call-with-port (open-file-input-port path)
                                                            (lambda (ip) (make-source-file-descriptor path ip)))])
                                                 (hashtable-set! sfds path sfd)
                                                 sfd)))])
                            (loop (+ i 1)
                                  (if sfd
                                      (cons (cons (make-source-object sfd (cadr k) (caddr k)) (vector-ref vals i)) acc)
                                      acc))))))])
             (profile-dump-html prefix dump)))
         (apply values results)))]))
