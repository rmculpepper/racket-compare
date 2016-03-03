#lang racket/base
(require racket/list
         racket/math
         racket/date
         racket/fixnum
         racket/flonum)
(provide general-cmp
         cmp-rules
         cmp*
         lexico
         prop:compare)

;; TODO: distinguish immutable?

;; partial orders, where most built-in values are comparable
;; *-cmp : Any Any -> (U '< '= '> #f)
;; Sort first by type (except possibly for numbers), then within type.
;; May diverge on cyclical input. May behave badly if concurrently modified.

(define-syntax cmp-rules
  (syntax-rules ()
    [(_ x y)
     (void)]
    [(_ x y [#:else body ...])
     (let () body ...)]
    [(_ x y [#:cond test body ...] clause ...)
     (cond [test body ...]
           [else (cmp-rules x y clause ...)])]
    [(_ x y [pred? body ...] clause ...)
     (cond [(pred? x) (if (pred? y) (let () body ...) '<)]
           [(pred? y) '>]
           [else (cmp-rules x y clause ...)])]))

(define-syntax-rule (cmp* <? =? xe ye)
  (let ([x xe] [y ye])
    (if (=? x y) '= (if (<? x y) '< '>))))

(define-syntax lexico
  (syntax-rules ()
    [(_ e) e]
    [(_ e1 e2 ...)
     (let ([v e1]) (if (eq? v '=) (lexico e2 ...) v))]))

;; all-perms-lexico : (Listof Comparison) -> Comparison
;; Returns x if all permutations of cmps lexicographically compare to x, else #f.
(define (all-perms-lexico cmps)
  (let loop ([cmps cmps] [result '=])
    (cond [(pair? cmps)
           (case (car cmps)
             [(=) (loop (cdr cmps) result)]
             [(<) (and (memq result '(< =)) (loop (cdr cmps) '<))]
             [(>) (and (memq result '(> =)) (loop (cdr cmps) '>))]
             [else #f])]
          [else result])))

;; ============================================================

(define-values (prop:compare prop:compare? prop:compare-ref)
  (make-struct-type-property 'compare))

;; ============================================================

(define (general-cmp x y natural?)
  (define (recur x* y*)
    (general-cmp x* y* natural?))
  (cmp-rules x y
    [#:cond (eq? x y) '=]
    [null? '=]
    [pair?
     (lexico (recur (car x) (car y)) (recur (cdr x) (cdr y)))]
    [boolean?  ;; #f < #t
     (cmp-rules x y [not '=] [#:else '=])]
    [char?
     (cmp* char<? char=? x y)]
    [string?
     (cmp* string<? string=? x y)]
    [bytes?
     (cmp* bytes<? bytes=? x y)]
    [symbol?
     (symbol-cmp x y)]
    [real?
     (real-cmp x y natural?)]
    [complex?
     (lexico (recur (real-part x) (real-part y))
             (recur (imag-part x) (imag-part y)))]
    [vector?
     (vector-cmp x y 0 recur)]
    [keyword?
     (cmp* keyword<? eq? x y)]
    [path-for-some-system?
     (cmp* bytes<? bytes=? (path->bytes x) (path->bytes y))]
    [regexp?
     (regexp-cmp x y)]
    [byte-regexp?
     (byte-regexp-cmp x y)]
    [box?
     (recur (unbox x) (unbox y))]
    [fxvector?
     (fxvector-cmp x y 0 recur)]
    [flvector?
     (flvector-cmp x y 0 recur)]
    [hash?
     (hash-cmp x y recur)]
    [date*?
     (date-cmp x y natural?)]
    [mpair?
     (lexico (recur (mcar x) (mcar y)) (recur (mcdr x) (mcdr y)))]
    [void? '=]
    [eof-object? '=]
    [syntax?
     (lexico (recur (syntax-e x) (syntax-e y))
             #| if not eq?, then incomparable |# #f)]
    [prefab-struct-key
     (lexico (recur (prefab-struct-key x) (prefab-struct-key y))
             (vector-cmp (struct->vector x) (struct->vector y) 1 recur))]
    [#:cond (and (prop:compare? x) (prop:compare? y)
                 (let ([xcmp (prop:compare-ref x)]
                       [ycmp (prop:compare-ref y)])
                   (and (equal? xcmp ycmp)
                        xcmp)))
            => (lambda (xcmp) (xcmp x y recur))]
    [fully-transparent-struct-type
     (lexico (vector-cmp (struct->vector x) (struct->vector y) 0 recur)
             (recur (fully-transparent-struct-type x)
                    (fully-transparent-struct-type y)))]
    ;; [#:cond extcmp (extcmp x y recur)]
    [#:else '#f]))

;; ----------------------------------------

(define (symbol-cmp x y)
  (cmp-rules x y
    [symbol-interned? (cmp* symbol<? eq? x y)]
    [symbol-unreadable? (cmp* symbol<? eq? x y)]
    [#:else #| uninterned |# (cmp* symbol<? eq? x y)]))

;; ----------------------------------------

(define (real-cmp x y natural?)
  (cond [natural?   ;; use = on non-NaN reals (eg, 1 = 1.0 = 1.0f0)
         (cmp-rules x y
           [nan? '=]
           [#:else (cmp* < = x y)])]
        [else       ;; consistent with eqv?; 1 < 1.0f0 < 1.0
         (cmp-rules x y
           [nan?
            (cmp-rules x y [exact? '=] [single-flonum? '=] [#:else '=])]
           [#:else
            (cond [(< x y) '<]
                  [(> x y) '>]
                  [else (=-cmp x y)])])]))

;; eqv?-compatible orders for =-comparing real numbers
;; Complicated by: want if x <? y, then -y <? -x
;; eg, -1.0 < -1.0f0 < -1 < -0.0 < -0.0f0 < 0 < 0.0f0 < 0.0 < 1 < 1.0f0 < 1.0
(define (=-cmp x y)
  (cond [(positive? x)
         (=-cmp* x y)]
        [(negative? x)
         (=-cmp* y x)]
        [else ;; zero :(
         (cmp-rules x y
           [(lambda (v) (eqv? v -0.0)) '=]
           [(lambda (v) (eqv? v -0.0f0)) '=]
           [(lambda (v) (eqv? v 0)) '=]
           [(lambda (v) (eqv? v 0.0f0)) '=]
           [#:else '=])]))

(define (=-cmp* x y)
  (cmp-rules x y
    [exact? '=]
    [single-flonum? '=]
    [#:else '=]))

;; ----------------------------------------

(define (hash-cmp x y recur)
  (cmp-rules x y
    [hash-eq? (hash-cmp/m x y eq? recur)]
    [hash-eqv? (hash-cmp/m x y eqv? recur)]
    [hash-equal? (hash-cmp/m x y equal? recur)]))

(define (hash-cmp/m x y =? recur)
  (cmp-rules x y
    [immutable? (hash-cmp/w x y =? recur)]
    [#:else (hash-cmp/w x y =? recur)]))

(define (hash-cmp/w x y =? recur)
  (cmp-rules x y
    [hash-weak? (hash-cmp* x y =? recur)]
    [#:else (hash-cmp* x y =? recur)]))

(define (hash-cmp* x y =? recur)
  (define (datum-cmp x y) (general-cmp x y #f))
  (define (datum<? x y) (eq? (datum-cmp x y) '<))
  (define all-keys (append (hash-keys x) (hash-keys y)))
  (define sorted-keys (remove-duplicates (sort all-keys datum<?) =?))
  ;; Compare lexicographic wrt sorted keys, where any value > "undefined"
  ;; Note: want cmp to be deterministic, and datum<? is partial order.
  ;; So detect if *examined* sorted-keys not totally ordered, return #f.

  (define (cmp-at-key key)
    (cond [(and (hash-has-key? x key) (hash-has-key? y key))
           (recur (hash-ref x key) (hash-ref y key))]
          [(hash-has-key? x key) '>]
          [(hash-has-key? y key) '<]
          [else
           ;; "impossible" neither has key, except for concurrent mutation
           '=]))

  ;; get-incomp-prefix : Any List -> #f or (Cons List List)
  (define (get-incomp-prefix key keys)
    (let loop ([keys keys] [key key] [prefix null])
      (cond [(and (pair? keys)
                  (memq (datum-cmp key (car keys)) '(= #f)))
             (loop (cdr keys) (car keys) (cons key prefix))]
            [(pair? prefix)
             (cons (cons key prefix) keys)]
            [else #f])))

  ;; let key1 = (list 0), key2 = (list 0) --- not eq?
  ;; want: (hasheq) < (hasheq (list 0) 1 (list 0) 2)
  ;;       (hasheq key1 1) < (hasheq key1 1 key2 2)
  ;;       (hasheq key2 2) < (hasheq key1 1 key2 2)
  (let loop ([keys sorted-keys])
    (cond [(pair? keys)
           (define key (car keys))
           (cond [(get-incomp-prefix key (cdr keys))
                  ;; all keys in prefix are pairwise EITHER incomp. OR datum=? but not =?
                  => (lambda (prefix+rest)
                       (define prefix (car prefix+rest))
                       (define rest (cdr prefix+rest))
                       (lexico (all-perms-lexico (map cmp-at-key prefix))
                               (loop rest)))]
                 [else (lexico (cmp-at-key key) (loop (cdr keys)))])]
          [else '=])))

;; ----------------------------------------

(define-syntax-rule (define-indexed-cmp name -length -ref)
  (define (name x y i recur)
    (cond [(and (< i (-length x)) (< i (-length y)))
           (lexico (recur (-ref x i) (-ref y i))
                   (name x y (add1 i) recur))]
          [(< i (-length y)) ;; x is shorter than y
           '<]
          [(< i (-length x)) ;; y is shorter than x
           '>]
          [else '=])))

(define-indexed-cmp vector-cmp   vector-length   vector-ref)
(define-indexed-cmp fxvector-cmp fxvector-length fxvector-ref)
(define-indexed-cmp flvector-cmp flvector-length flvector-ref)

;; ----------------------------------------

(define (regexp-cmp x y)
  (cmp-rules x y
    [pregexp? (cmp* string<? string=? (object-name x) (object-name y))]
    [#:else (cmp* string<? string=? (object-name x) (object-name y))]))
(define (byte-regexp-cmp x y)
  (cmp-rules x y
    [byte-pregexp? (cmp* bytes<? bytes=? (object-name x) (object-name y))]
    [#:else (cmp* bytes<? bytes=? (object-name x) (object-name y))]))

;; ----------------------------------------

;; weak inspector; if it can inspect, must be transparent
(define weak-inspector (make-inspector))

;; fully-transparent-struct-type : any -> struct-type or #f
(define (fully-transparent-struct-type x)
  (parameterize ((current-inspector weak-inspector))
    (let-values ([(x-type x-skipped?) (struct-info x)])
      (and (not x-skipped?) x-type))))

;; ----------------------------------------

(define (date-cmp x y natural?)
  (let ([xsec (- (date->seconds x) (date-time-zone-offset x))]
        [ysec (- (date->seconds y) (date-time-zone-offset y))])
    (lexico (cmp* < = xsec ysec)
            (cmp* < = (date*-nanosecond x) (date*-nanosecond y))
            (if natural?
                '=
                (lexico (cmp* < = (date-week-day x) (date-week-day y))
                        (cmp* < = (date-year-day x) (date-year-day y))
                        (cmp* < = (date-time-zone-offset x) (date-time-zone-offset y))
                        (cmp* string<? equal?
                              (date*-time-zone-name x) (date*-time-zone-name y)))))))

;; ============================================================

(provide gendatum
         genhash
         genhasheq)

(define-syntax-rule (random-case [n body] ...)
  (random-case* (list (cons n (lambda () body)) ...)))
(define (random-case* dist)
  (define r (random (apply + (map car dist))))
  (let loop ([r r] [dist dist])
    (cond [(< r (caar dist)) ((cdar dist))]
          [else (loop (- r (caar dist)) (cdr dist))])))

(define (gendatum)
  ;; null/pair boolean char string bytes symbol real complex vector keyword
  ;; path regexp box fxvector flvector hash mpair prefab-struct-key
  (random-case
   [7 (< (random) 0.5)]
   [3 (integer->char (+ 32 (random (- 255 32))))]
   [9 (apply string (map integer->char (genbytelist)))]
   [6 (apply bytes (genbytelist))]
   [7 (string->symbol (apply string (map integer->char (genbytelist))))]
   [3 (string->keyword (apply string (map integer->char (genbytelist))))]
   [9 (- 1000 (random 2000))]
   [9 (* 2000 (- (random) 0.5))]
   ;; --
   [3 (append (for/list ([i (random 10)]) (gendatum))
              (random-case [4 null] [1 (gendatum)]))]
   [2 (for/vector ([i (random 10)]) (gendatum))]
   [1 (box (gendatum))]
   [1 (genhash)]
   [0 (genhasheq)]))

(define (genhash) (for/hash ([i (random 4)]) (values (genkey) (gendatum))))
(define (genhasheq) (for/hasheq ([i (random 4)]) (values (genkey) (gendatum))))

(define (genkey)
  (random-case
   [4 (random 5)]
   [4 (format "str~s" (random 5))]
   [3 (string->symbol (format "sym~s" (random 5)))]
   [1 (gendatum)]))

(define (genbytelist)
  (for/list ([i (random 20)]) (+ 97 (random 32))))

;; ----

(provide (struct-out wrap)
         (struct-out twrap))
(struct wrap (v)
        #:property prop:compare
        (lambda (x y recur)
          (recur (wrap-v x) (wrap-v y))))
(struct twrap (v) #:transparent)
