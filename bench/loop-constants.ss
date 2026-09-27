;; Loops with wide constants, for the hoisting experiment.  Compare
;;   scheme -q bench/loop-constants.ss
;;   CHEZ_NO_HOIST_IMM=1 scheme -q bench/loop-constants.ss

;; 64-bit hashing in Chez: generic (bignum) arithmetic vs. 32-bit fixnum halves.
(optimize-level 3)
(debug-level 0)

(define M64 #xFFFFFFFFFFFFFFFF)

;; ---------------------------------------------------------------- FNV-1a
(define (fnv32 bv)
  (let ([n (bytevector-length bv)])
    (let loop ([i 0] [h #x811c9dc5])
      (if (fx= i n)
          h
          (loop (fx+ i 1)
                (fxlogand (fx* (fxlogxor h (bytevector-u8-ref bv i)) 16777619) #xFFFFFFFF))))))

(define (fnv64-generic bv)
  (let ([n (bytevector-length bv)])
    (let loop ([i 0] [h #xcbf29ce484222325])
      (if (fx= i n)
          h
          (loop (fx+ i 1)
                (logand (* (logxor h (bytevector-u8-ref bv i)) #x100000001b3) M64))))))

;; P = 2^40 + #x1b3, so h*P mod 2^64 = (lo<<40) + h*#x1b3, split into halves
(define (fnv64-halves bv)
  (let ([n (bytevector-length bv)])
    (let loop ([i 0] [hi #xcbf29ce4] [lo #x84222325])
      (if (fx= i n)
          (+ (ash hi 32) lo)
          (let* ([lo (fxlogxor lo (bytevector-u8-ref bv i))]
                 [t (fx* lo #x1b3)])
            (loop (fx+ i 1)
                  (fxlogand (fx+ (fx* hi #x1b3) (fxsrl t 32) (fxsll lo 8)) #xFFFFFFFF)
                  (fxlogand t #xFFFFFFFF)))))))

;; ---------------------------------------------------------------- SipHash-2-4 compression
;; (no finalization; returns v0^v1^v2^v3 over all 8-byte words)

(define (sip-generic bv)
  (define-syntax add (syntax-rules () [(_ a b) (logand (+ a b) M64)]))
  (define-syntax rotl (syntax-rules () [(_ x k) (logand (logior (ash x k) (ash x (- k 64))) M64)]))
  (define (round v0 v1 v2 v3)
    (let* ([v0 (add v0 v1)] [v1 (rotl v1 13)] [v1 (logxor v1 v0)] [v0 (rotl v0 32)]
           [v2 (add v2 v3)] [v3 (rotl v3 16)] [v3 (logxor v3 v2)]
           [v0 (add v0 v3)] [v3 (rotl v3 21)] [v3 (logxor v3 v0)]
           [v2 (add v2 v1)] [v1 (rotl v1 17)] [v1 (logxor v1 v2)] [v2 (rotl v2 32)])
      (values v0 v1 v2 v3)))
  (let ([n (bytevector-length bv)])
    (let loop ([i 0] [v0 #x736f6d6570736575] [v1 #x646f72616e646f6d]
               [v2 #x6c7967656e657261] [v3 #x7465646279746573])
      (if (fx> (fx+ i 8) n)
          (logxor v0 v1 v2 v3)
          (let ([m (bytevector-u64-native-ref bv i)])
            (let-values ([(v0 v1 v2 v3) (round v0 v1 v2 (logxor v3 m))])
              (let-values ([(v0 v1 v2 v3) (round v0 v1 v2 v3)])
                (loop (fx+ i 8) (logxor v0 m) v1 v2 v3))))))))

(define-syntax add64
  (syntax-rules ()
    [(_ (ah al) (bh bl) body ...)
     (let* ([s (fx+ al bl)]
            [al (fxlogand s #xFFFFFFFF)]
            [ah (fxlogand (fx+ ah bh (fxsrl s 32)) #xFFFFFFFF)])
       body ...)]))
(define-syntax xor64
  (syntax-rules ()
    [(_ (ah al) (bh bl) body ...)
     (let* ([ah (fxlogxor ah bh)] [al (fxlogxor al bl)]) body ...)]))
(define-syntax rotl64 ; 0 < k < 32
  (syntax-rules ()
    [(_ (h l) k body ...)
     (let* ([nh (fxlogand (fxlogor (fxsll h k) (fxsrl l (fx- 32 k))) #xFFFFFFFF)]
            [nl (fxlogand (fxlogor (fxsll l k) (fxsrl h (fx- 32 k))) #xFFFFFFFF)]
            [h nh] [l nl])
       body ...)]))
(define-syntax rot32
  (syntax-rules ()
    [(_ (h l) body ...) (let* ([t h] [h l] [l t]) body ...)]))
(define-syntax sipround
  (syntax-rules ()
    [(_ (v0h v0l v1h v1l v2h v2l v3h v3l) body ...)
     (add64 (v0h v0l) (v1h v1l) (rotl64 (v1h v1l) 13 (xor64 (v1h v1l) (v0h v0l) (rot32 (v0h v0l)
     (add64 (v2h v2l) (v3h v3l) (rotl64 (v3h v3l) 16 (xor64 (v3h v3l) (v2h v2l)
     (add64 (v0h v0l) (v3h v3l) (rotl64 (v3h v3l) 21 (xor64 (v3h v3l) (v0h v0l)
     (add64 (v2h v2l) (v1h v1l) (rotl64 (v1h v1l) 17 (xor64 (v1h v1l) (v2h v2l) (rot32 (v2h v2l)
       body ...))))))))))))))]))

(define (sip-halves bv)
  (let ([n (bytevector-length bv)])
    (let loop ([i 0]
               [v0h #x736f6d65] [v0l #x70736575] [v1h #x646f7261] [v1l #x6e646f6d]
               [v2h #x6c796765] [v2l #x6e657261] [v3h #x74656462] [v3l #x79746573])
      (if (fx> (fx+ i 8) n)
          (logxor (+ (ash v0h 32) v0l) (+ (ash v1h 32) v1l) (+ (ash v2h 32) v2l) (+ (ash v3h 32) v3l))
          (let ([ml (bytevector-u32-native-ref bv i)]
                [mh (bytevector-u32-native-ref bv (fx+ i 4))])
            (xor64 (v3h v3l) (mh ml)
              (sipround (v0h v0l v1h v1l v2h v2l v3h v3l)
                (sipround (v0h v0l v1h v1l v2h v2l v3h v3l)
                  (xor64 (v0h v0l) (mh ml)
                    (loop (fx+ i 8) v0h v0l v1h v1l v2h v2l v3h v3l))))))))))


(define (str-hash s)
  (let ([n (string-length s)])
    (let loop ([i 0] [h 0])
      (if (fx= i n)
          h
          (loop (fx+ i 1)
                (fxlogand (fx+ (fx*/wraparound h 31) (char->integer (string-ref s i)))
                          #xFFFFFFFFFFF))))))

(define (lcg n a c)
  (let loop ([i 0] [x 1])
    (if (fx= i n)
        x
        (loop (fx+ i 1) (fxlogand (fx+/wraparound (fx*/wraparound x a) c) #xFFFFFFFFFFFF)))))

(define (horner v x)
  (let ([n (fxvector-length v)])
    (let loop ([i 0] [acc 0])
      (if (fx= i n)
          acc
          (loop (fx+ i 1)
                (fxlogand (fx+/wraparound (fx*/wraparound acc x) (fxvector-ref v i))
                          #xFFFFFFFFFFFF))))))

(define (xorshift n)
  (let loop ([i 0] [x 88172645463325252] [acc 0])
    (if (fx= i n)
        acc
        (let* ([x (fxlogxor x (fxsll/wraparound x 13))]
               [x (fxlogxor x (fxsrl x 7))]
               [x (fxlogxor x (fxsll/wraparound x 17))])
          (loop (fx+ i 1) x (fxlogxor acc x))))))

;; murmur3 fmix32 over 0..n-1: two multiplies by 32-bit odd constants
(define (murmur-sum n)
  (let loop ([i 0] [acc 0])
    (if (fx= i n)
        acc
        (let* ([h (fxlogxor i (fxsrl i 16))]
               [h (fxlogand (fx*/wraparound h #x85ebca6b) #xFFFFFFFF)]
               [h (fxlogxor h (fxsrl h 13))]
               [h (fxlogand (fx*/wraparound h #xc2b2ae35) #xFFFFFFFF)]
               [h (fxlogxor h (fxsrl h 16))])
          (loop (fx+ i 1) (fxlogxor acc h))))))

;; xxHash32 main loop: four lanes, each acc = rotl13(acc + lane*P2) * P1
(define-syntax xxround
  (syntax-rules ()
    [(_ acc lane)
     (let* ([a (fxlogand (fx+ acc (fx*/wraparound lane #x85EBCA77)) #xFFFFFFFF)]
            [a (fxlogand (fxlogor (fxsll a 13) (fxsrl a 19)) #xFFFFFFFF)])
       (fxlogand (fx*/wraparound a #x9E3779B1) #xFFFFFFFF))]))
(define (xxh32-core bv)
  (let ([n (bytevector-length bv)])
    (let loop ([i 0] [v1 #x24234428] [v2 #x85EBCA77] [v3 0] [v4 #x61C8864F])
      (if (fx> (fx+ i 16) n)
          (fxlogxor v1 v2 v3 v4)
          (loop (fx+ i 16)
                (xxround v1 (bytevector-u32-native-ref bv i))
                (xxround v2 (bytevector-u32-native-ref bv (fx+ i 4)))
                (xxround v3 (bytevector-u32-native-ref bv (fx+ i 8)))
                (xxround v4 (bytevector-u32-native-ref bv (fx+ i 12))))))))

(define BV (let ([b (make-bytevector 4000000)])
             (do ([i 0 (fx+ i 1)]) ((fx= i (bytevector-length b)) b)
               (bytevector-u8-set! b i (fxlogand (fx* i 7) 255)))))
(define S (let ([s (make-string 4000000)])
            (do ([i 0 (fx+ i 1)]) ((fx= i (string-length s)) s) (string-set! s i (integer->char (fx+ 97 (fxremainder i 26)))))))
(define FV (let ([v (make-fxvector 4000000)])
             (do ([i 0 (fx+ i 1)]) ((fx= i (fxvector-length v)) v) (fxvector-set! v i (fxlogand i 1023)))))
(define (time-it name iters thunk)
  (let loop ([k 0] [best +inf.0] [r #f])
    (if (fx= k 7)
        (printf "~a ~,3f ns/iter  ~x\n" name (/ (* best 1e9) iters) r)
        (let* ([t0 (current-time 'time-monotonic)]
               [r (thunk)]
               [d (time-difference (current-time 'time-monotonic) t0)])
          (loop (fx+ k 1) (min best (+ (time-second d) (/ (time-nanosecond d) 1e9))) r)))))
(time-it "murmur-fmix32         " 40000000 (lambda () (murmur-sum 40000000)))
(time-it "xxh32-core  (per byte)" 4000000 (lambda () (xxh32-core BV)))
(time-it "sip-halves  (per byte)" 4000000 (lambda () (sip-halves BV)))
(time-it "fnv64-halves(per byte)" 4000000 (lambda () (fnv64-halves BV)))
(time-it "fnv32       (per byte)" 4000000 (lambda () (fnv32 BV)))
(time-it "str-hash              " 4000000 (lambda () (str-hash S)))
(time-it "lcg                   " 40000000 (lambda () (lcg 40000000 25214903917 11)))
(time-it "horner                " 4000000 (lambda () (horner FV 3)))
(time-it "xorshift              " 40000000 (lambda () (xorshift 40000000)))
