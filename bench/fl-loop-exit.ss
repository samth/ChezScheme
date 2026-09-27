;; Flonum loops whose exit returns the loop variable itself.
;;
;;   scheme -q bench/fl-loop-exit.ss
;;
;; Each kernel comes in two forms: `bare` returns the accumulator as is,
;; and `hint` returns (fl+ acc), the idiom that already kept the
;; accumulator unboxed.  With loop-exit unboxing the two should match.

(optimize-level 3)

;; sum of 1/i
(define (harmonic-bare n)
  (let loop ([i 1] [acc 0.0])
    (if (fx> i n) acc (loop (fx+ i 1) (fl+ acc (fl/ 1.0 (fixnum->flonum i)))))))
(define (harmonic-hint n)
  (let loop ([i 1] [acc 0.0])
    (if (fx> i n) (fl+ acc) (loop (fx+ i 1) (fl+ acc (fl/ 1.0 (fixnum->flonum i)))))))

;; dot product, the shape Racket's `for/fold` expands to
(define (dot-bare a b)
  (let ([n (flvector-length a)])
    (let loop ([i 0] [acc 0.0])
      (if (fx< i n)
          (let ([acc (fl+ acc (fl* (flvector-ref a i) (flvector-ref b i)))])
            (loop (fx+ i 1) acc))
          acc))))
(define (dot-hint a b)
  (let ([n (flvector-length a)])
    (let loop ([i 0] [acc 0.0])
      (if (fx< i n)
          (let ([acc (fl+ acc (fl* (flvector-ref a i) (flvector-ref b i)))])
            (loop (fx+ i 1) acc))
          (fl+ acc)))))

;; Newton's method for sqrt: two flonum loop variables, exit returns one
(define (newton-bare x)
  (let loop ([k 0] [y 1.0] [prev 0.0])
    (if (fx= k 40) y (loop (fx+ k 1) (fl* 0.5 (fl+ y (fl/ x y))) y))))
(define (newton-hint x)
  (let loop ([k 0] [y 1.0] [prev 0.0])
    (if (fx= k 40) (fl+ y) (loop (fx+ k 1) (fl* 0.5 (fl+ y (fl/ x y))) y))))
(define (newton-sum newton n)
  (let loop ([i 1] [s 0.0])
    (if (fx> i n) s (loop (fx+ i 1) (fl+ s (newton (fixnum->flonum i)))))))

(define (run name thunk)
  (collect)
  (let* ([b0 (+ (bytes-allocated) (bytes-deallocated))]
         [t0 (current-time 'time-monotonic)]
         [r (thunk)]
         [d (time-difference (current-time 'time-monotonic) t0)]
         [ms (+ (* 1000 (time-second d)) (/ (time-nanosecond d) 1e6))])
    (printf "~a ~8,1f ms ~12d bytes allocated  ~s\n" name ms (- (+ (bytes-allocated) (bytes-deallocated)) b0) r)))

(define A (let ([v (make-flvector 1000000)])
            (do ([i 0 (fx+ i 1)]) ((fx= i 1000000) v)
              (flvector-set! v i (fixnum->flonum (fxremainder i 17))))))

(define (best-of n thunk) (do ([k 0 (fx+ k 1)]) ((fx= k n)) (thunk)))
(best-of 2 (lambda () (harmonic-bare 1000) (harmonic-hint 1000)))
(run "harmonic bare" (lambda () (harmonic-bare 100000000)))
(run "harmonic hint" (lambda () (harmonic-hint 100000000)))
(run "dot      bare" (lambda () (do ([k 0 (fx+ k 1)] [r 0.0 (dot-bare A A)]) ((fx= k 100) r))))
(run "dot      hint" (lambda () (do ([k 0 (fx+ k 1)] [r 0.0 (dot-hint A A)]) ((fx= k 100) r))))
(run "newton   bare" (lambda () (newton-sum newton-bare 2000000)))
(run "newton   hint" (lambda () (newton-sum newton-hint 2000000)))
