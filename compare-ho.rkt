#lang racket/base
(require (for-syntax racket/base))
(provide (all-defined-out))

;; A Comparison is one of '<, '=, '>, or #f, where #f means incomparable.

;; For compatibilty with equal?, mutability is currently not considered for
;; strings, bytes, vectors, and boxes; but it is for hashes.
;; Thus (vector-immutable 1 2 3) = (vector 1 2 3) and (box 1) = (immutable-box 1)
;; but (make-hash '((a . 1) (b . 2))) != (make-immutable-hash '((a . 1) (b . 2)))

;; Comparing numbers:
;;  A) by type then by value: eg 1 < 2 < 3 < ... 1.0 < 2.0 < 3.0
;;  B) by value then by type: eg 1 < 1.0 < 2 < 2.0 ...
;;  C) by value: 1 = 1.0 = 1.0f
;; A and B are like eqv?; C is like with = (except for NaN).
;; Use B for datum-cmp and C for natural-cmp. A doesn't seem useful.

;; Comparing vectors: lexicographic rather than length-first (unlike srfi-67)

;; Comparing hashes:
;; by type first, eg hasheq < hasheqv < hash ...? (also, mutability?, weak?)
;;  A) function-ordering on values (ie, < if all points <= and not all =, etc)
;;     A1) require keys same, else incomparable
;;     A2) union of keys, absent < any value
;;  B) lexico on values (beware! not well defined if keys not totally ordered!)
;;     B1) require keys same, else incomparable
;;     B2) union of keys, absent < any value
;; A1 is a subrelation of A2 and B1, which are both subrelations of B2.
;; A2,B2 coincide with subset order for (hashof X #t) set rep.
;; A2 seems reasonable.

;; Handling cyclic data:
;; - Must not diverge on cyclic data, else useless for generic situations like
;;   sorting set contents for pretty-printing.
;; - Fuel-limited version alone is a partial order (I think), but loses
;;   compatibility property: if A = A' and B = B' then (cons A B) = (cons A' B'),
;;   because |A|+|B|+1 might exhaust fuel even though neither |A| nor |B| does.
;; - So try fuel-limited first, then fall back to cycle-detecting version.
;; - Cycle detection: rather than detecting cycles of pairs of arguments (needs
;;   eq-eq binary hash), abort if cycle detected on *both* arguments.

;; Prop: (null < everything else) implies ls <= (append ls b)

;; Prop: datum-cmp, natural-cmp are partial orders even for cyclic data.
;; - irreflexive: not (X < X).
;; - <-transitive: if X < Y < Z, then X < Z.
;;   Let Fxy be the position (fuel) where X differs from Y, likewise Fyz.
;;   Since X < Y, Fxy is before a cycle is discovered.
;;   X < Z at point min(Fxy, Fyz) <= Fxy, so still before cycle is discovered.
;; - =-transitive: if X = Y = Z, then X = Z.
;;   If cyclic subvalues in X and Y are skipped because eqv?, then same cyclic
;;   subvalues must be present in Z.
;; - =-symmetric: if X = Y, then Y = X
;;   No if cycle checking is asymmetric (eg, xvisited but no yvisited)
;;   Let l = (shared ([l (cons 'a l)]) l) and set FUEL = 0.
;;   Then cmp((cons 'a l), l) is '=, but cmp(l, (cons 'a l)) is #f.
;;   Yes with cycle checking on both x and y.

;; Conjecture: if exists FUEL s.t. cmp_fuel(X, Y, FUEL) = C,
;; then cmp_cycle(X, Y) = C.

;; Conjecture: X = X' and Y = Y' implies (cons X Y) = (cons X' Y')
;; Should be true unless previous conjecture is false and the fuel threshold is
;; exhausted.

;; Note: more ambitious cyclic comparison would be hard; example:
;; - x = (list y x 1), y = (list x y 2), cmp(x, y)
;;   cmp(x, y) = lexico( cmp(y, x), cmp(x, y), cmp(1, 2) )
;;             = lexico( eq, eq, lt )   -- using "assume equal on recur"
;;             = lt
;;       check:  lexico( cmp(y, x), cmp(x, y), cmp(1, 2) ) assuming cmp(x, y) = lt
;;             = lexico( gt, lt, lt ) = gt  -- inconsistent!

;; ============================================================

(define (NaN? x) (or (eqv? x +nan.0) (eqv? x (real->single-flonum +nan.0))))

(define-syntax-rule (is-eqv? v)
  (lambda (x) (eqv? x v)))

(define-syntax-rule (negate f)
  (lambda (x) (not (f x))))

;; partial-order : (X X -> Bool) (X X -> Bool) X X -> Comparison
(define (partial-order <? =? x y)
  (cond [(=? x y) '=]
        [(<? x y) '<]
        [(<? y x) '>]
        [else #f]))

;; total-order : (X X -> Bool) (X X -> Bool) X X -> Comparison
;; like partial-order except x, y known to be {<?,=?}-comparable
(define (total-order <? =? x y)
  (cond [(=? x y) '=]
        [(<? x y) '<]
        [else '>]))

;; (lexico C1 ... CN) combines comparisons C1..CN lexicographically;
;; that is, it returns the first non-= result (or = if all =).
(define-syntax lexico
  (syntax-rules ()
    [(lexico c) c]
    [(lexico c1 c2 ...)
     (let ([r1 c1])
       (if (eq? result '=) (lexico c2 ...) r1))]))

;; (conj C1 C2) conjoins comparisons C1 and C2; cf derived partial order on function space
(define-syntax-rule (conj c1 c2)
  (let ([k (lambda () c2)])
    (case c1
      [(<) (case (k) [(< =) '<] [else #f])]
      [(=) (k)]
      [(>) (case (k) [(> =) '>] [else #f])]
      [(#f) #f])))

;; with-cmp-cases compares two variables by ascending predicate then by custom comparisons
;; Example: (with-cmp-case x y [#:pred A? (A-cmp x y)] [#:pred B? (B-cmp x y)])
;;   If x:A, y:B, then x < y. If x:B, y:A, then x > y. If x:A, y:A, then use A-cmp.
(define-syntax (with-cmp-cases stx)
  (syntax-case stx ()
    [(wcc x y clause ...)
     (let ()
       (define (handle-clause c)
         (syntax-case c ()
           [[#:pred pred body ...]
            #'([(pred x)
                (cond [(pred y) body ...]
                      [else '<])]
               [(pred y) '>])]
           [[#:pred=> pred proc]
            #'([(pred x)
                => (lambda (xv)
                     (cond [(pred y) => (lambda (yv) (proc xv yv))]
                           [else '<]))]
               [(pred y) '>])]
           [[#:else body ...]
            #'([else body ...])]
           [_ (raise-syntax-error #f "bad clause" stx c)]))
       (with-syntax ([((cclause ...) ...)
                      (map handle-clause (syntax->list #'(clause ...)))])
         #'(cond cclause ... ...)))]))

;; ------------------------------------------------------------

(define (datum-cmp x y)   (safe-gen-cmp x y #f))
(define (natural-cmp x y) (safe-gen-cmp x y #t))

(define (datum<? x y)   (eq? (datum-cmp x y) '<))
(define (natural<? x y) (eq? (natural-cmp x y) '<))

;; ------------------------------------------------------------

(define FUEL 0) ;;#e1e6)
(define CYCLE (gensym 'cycle))
(define OUT-OF-FUEL (gensym 'out-of-fuel))

(define (safe-gen-cmp x y natural?)
  (define (try-cycle)
    (with-handlers ([(lambda (e) (eq? e CYCLE))
                     (lambda (e) #f)])
      (gen-cmp/cycle x y natural?)))
  (define (try-fuel)
    (with-handlers ([(lambda (e) (eq? e OUT-OF-FUEL))
                     (lambda (e) (try-cycle))])
      (gen-cmp/fuel x y natural? FUEL)))
  (try-fuel))

;; ----

(define (gen-cmp/fuel x y natural? fuel)
  (define (recur x y)
    (if (zero? fuel)
        (raise OUT-OF-FUEL)
        (set! fuel (sub1 fuel)))
    (cmp/recur x y natural? recur))
  (cmp/recur x y natural? recur))

(define (gen-cmp/cycle x y natural?)
  ;; simple? : Any -> Boolean
  (define (simple? x) ;; ok to miss some types, just means unnecessary hash updates
    (or (null? x) (number? x) (boolean? x) (char? x) (symbol? x) (keyword? x)
        (string? x) (bytes? x) (path-for-some-system? x)))
  (define xvisited (make-hasheq))
  (define yvisited (make-hasheq))
  (define (recur x y)
    (cond [(or (simple? x) (simple? y))
           (cmp/recur x y natural? recur)]
          [else
           (define xcycle? (hash-ref xvisited x #f))
           (define ycycle? (hash-ref yvisited y #f))
           (when (and xcycle? ycycle?) (raise CYCLE))
           (unless xcycle? (hash-set! xvisited x #t))
           (unless ycycle? (hash-set! yvisited y #t))
           (begin0 (cmp/recur x y natural? recur)
             (unless xcycle? (hash-remove! xvisited x))
             (unless ycycle? (hash-remove! yvisited y)))]))
  (recur x y))

(define (cmp/recur x y natural? recur)
  (with-cmp-cases x y
    ;; Lists
    [#:pred null? '=]
    [#:pred pair?
     (lexico (recur (car x) (car y))
             (recur (cdr x) (cdr y)))]
    ;; Numbers
    [#:pred real?
     (real-cmp x y natural?)]
    [#:pred complex?
     (lexico (real-cmp (real-part x) (real-part y) natural?)
             (real-cmp (imag-part x) (imag-part y) natural?))]
    ;; Other atomic/simple
    [#:pred boolean?
     (with-cmp-cases x y [#:pred (is-eqv? #f) '=] [#:else '=])]
    [#:pred char?
     (total-order char<? char=? x y)]
    [#:pred symbol?
     (cond [(symbol<? x y) '<]
           [(symbol<? y x) '>]
           [else ;; contents are same
            (with-cmp-cases x y
              [#:pred symbol-interned? '=]
              [#:pred symbol-unreadable? '=]
              [#:else #f])])]
    [#:pred keyword?
     (total-order keyword<? eq? x y)]
    [#:pred string?
     (total-order string<? string=? x y)]
    [#:pred bytes?
     (total-order bytes<? bytes=? x y)]
    [#:pred path-for-some-system?
     ;; FIXME: type?
     (partial-order path<? equal? x y)]
    [#:pred regexp?
     (lexico (with-cmp-cases x y
               [#:pred (negate pregexp?) '=]
               [#:else '=])
             (recur (object-name x) (object-name y)))]
    ;; Other compound
    [#:pred vector?
     (vector-cmp x y 0 recur)]
    [#:pred box?
     (recur (unbox x) (unbox y))]
    [#:pred hash?
     (lexico (hash-type-cmp x y)
             (let ([result
                    (for/fold ([acc '=]) ([(k xv) (in-hash x)])
                      (conj acc (if (hash-has-key? y k)
                                    (recur xv (hash-ref y k))
                                    '>)))])
               (for/fold ([acc result]) ([(k yv) (in-hash y)]
                                         #:when (not (hash-has-key? x k)))
                 (conj acc '<))))]
    [#:pred=> prefab-struct-key
     (lambda (xkey ykey)
       (lexico (prefab-struct-key-cmp xkey ykey)
               (vector-cmp (struct->vector x) (struct->vector y) 1 recur)))]
    [#:pred=> fully-transparent-struct-type
     (lambda (xtype ytype)
       (lexico (struct-type-cmp xtype ytype)
               (vector-cmp (struct->vector x) (struct->vector y) 1 recur)))]
    [#:else #f]))

(define (vector-cmp x y i recur)
  (let ([n (min (vector-length x) (vector-length y))])
    (let loop ([i i])
      (if (< i n)
          (lexico (recur (vector-ref x i) (vector-ref y i))
                  (loop (add1 i)))
          (total-order < = (vector-length x) (vector-length y))))))

;; ----------------------------------------

(define (real-cmp x y natural?)
  (with-cmp-cases x y
    [#:pred (negate NaN?)
     (lexico (total-order < = x y)
             (if natural? '= (real-type/sign-cmp x y)))]
    [#:else (if natural? '= (real-type-cmp x y))]))

(define (real-type/sign-cmp x y)
  ;; PRE: x = y
  ;; -1.0 < -1 < -0.0 < 0 < 0.0 < 1 < 1.0    -- if x < y, then -x > -y.
  (cond [(zero? x)
         (with-cmp-cases x y
           [#:pred (is-eqv? -0.0) '=]
           [#:pred (is-eqv? (real->single-flonum -0.0)) '=]
           [#:pred (is-eqv? 0) '=]
           [#:pred (is-eqv? (real->single-flonum 0.0))  '=]
           [#:pred (is-eqv? 0.0) '=])]
        [(negative? x) (real-type-cmp y x)]  ;; invert type ordering
        [else (real-type-cmp x y)]))

(define (real-type-cmp x y)
  ;; exact < single-flonum < (double-)flonum
  (with-cmp-cases x y
    [#:pred exact? '=]
    [#:pred single-flonum? '=]
    [#:else '=]))

(define (hash-type-cmp x y)
  (lexico (with-cmp-cases x y [#:pred hash-eq? '=] [#:pred hash-eqv? '=] [#:pred hash-equal? '=])
          (with-cmp-cases x y [#:pred (negate hash-weak?) '=] [#:else '=])
          (with-cmp-cases x y [#:pred immutable? '=] [#:else '=])))

;; weak inspector controls no struct types;
;; so if it can inspect, must be transparent
(define weak-inspector (make-inspector))

;; fully-transparent-struct-type : Any -> StructType/#f
(define (fully-transparent-struct-type x)
  (parameterize ((current-inspector weak-inspector))
    (let-values ([(x-type x-skipped?) (struct-info x)])
      (and (not x-skipped?) (fully-transparent? x-type) x-type))))

;; fully-transparent? : StructType -> Boolean
(define (fully-transparent? stype)
  (define-values (_name _inits _autos _accessor _mutator _imm super skipped?)
    (struct-type-info stype))
  (and (not skipped?)
       (or (not super) (fully-transparent? super))))

(define (prefab-struct-key-cmp xkey ykey)
  (datum-cmp xkey ykey))

(define (struct-type-cmp xtype ytype)
  (lexico (partial-order symbol<? eq? (object-name xtype) (object-name ytype))
          (total-order < = (eq-hash-code xtype) (eq-hash-code ytype))
          #f))
