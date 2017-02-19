#lang racket/base
(require (for-syntax racket/base))
(provide (all-defined-out))

;; A Comparison is one of '<, '=, '>, or #f
;; A Comparator is (Any Any -> Comparison)

(define (real/not-NaN? x) (and (real? x) (not (NaN? x))))
(define (NaN? x) (or (eqv? x +nan.0) (eqv? x (real->single-flonum +nan.0))))

;; ============================================================

;; Beware: comparison may diverge on cyclic input

;; For compatibilty with equal?, mutability is currently not considered for
;; strings, bytes, vectors, and boxes; but it is for hashes.

;; Comparing numbers:
;;  A) by type then by value: eg 1 < 2 < 3 < ... 1.0 < 2.0 < 3.0
;;  B) by value then by type: eg 1 < 1.0 < 2 < 2.0 ...
;;  C) by value: 1 = 1.0 = 1.0f
;; A and B are compatible with eqv; C is compatible with = (except for NaN)

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

;; Names: datum-cmp, value-cmp, natural-cmp, ???


#|
    null
  < pair
    ;; Atomic:
  < number (!)
  < boolean
  < character
  < symbol
  < keyword
  < string
  < bytes
  < path
  < regexp
    ;; Other Compound:
  < vector
  < box
  < hash
  < prefab-struct
  < fully-transparent-struct

FIXME: extensible comparison?
|#

(define-syntax-rule (tcmp <? =? xe ye)
  (let ([x xe] [y ye])
    (cond [(=? x y) '=]
          [(<? x y) '<]
          [else '>])))

(define-syntax-rule (pcmp <? =? xe ye)
  (let ([x xe] [y ye])
    (cond [(=? x y) '=]
          [(<? x y) '<]
          [(<? y x) '>]
          [else #f])))

(define-syntax lexico
  (syntax-rules ()
    [(lexico c) c]
    [(lexico c1 c2 ...) (lexico2 c1 (lexico c2 ...))]))

(define-syntax-rule (lexico2 c1 c2)
  (case c1 ((<) '<) ((=) c2) ((>) '>) ((#f) #f)))

(define-syntax-rule (conj c1 c2)
  (let ([k (lambda () c2)])
    (case c1
      [(<) (case (k) [(< =) '<] [else #f])]
      [(=) (k)]
      [(>) (case (k) [(> =) '>] [else #f])]
      [(#f) #f])))

(define-syntax (with-cmp-cases stx)
  (syntax-case stx ()
    [(wcc x y clause ...)
     (let ()
       (define (handle-clause c)
         (syntax-case c ()
           [[#:test test body ...]
            #'([test body ...])]
           [[#:eqv? v body ...]
            #'([(eqv? x v)
                (cond [(eqv? y v) body ...]
                      [else '<])]
               [(eqv? y v) '>])]
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

(define (datum-cmp x y #:fuel [fuel #f])   (gen-cmp x y #f fuel))
(define (natural-cmp x y #:fuel [fuel #f]) (gen-cmp x y #t fuel))

(define (datum<? x y) (eq? (datum-cmp x y) '<))
(define (natural<? x y) (eq? (natural-cmp x y) '<))

(define FUEL #e1e6)
(define (try-datum<? x y [fuel FUEL]) (eq? (datum-cmp x y fuel) '<))
(define (try-natural<? x y [fuel FUEL]) (eq? (natural-cmp x y fuel) '<))

;; ------------------------------------------------------------

(define (gen-cmp x y natural? fuel xvisited)
  (define (recur x y)
    (cond [xvisited
           (cond [(hash-ref xvisited x #f) #f]
                 [else
                  (hash-set! xvisited x #t)
                  (begin0 (recur* x y)
                    (hash-remove! xvisited x))])]
          [else (recur* x y)]))
  (define (recur* x y)
    (with-cmp-cases x y
      [#:test (eqv? x y) '=]
      [#:test (and fuel (begin0 (zero? fuel) (set! fuel (sub1 fuel)))) '#f]
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
       (with-cmp-cases x y [#:eqv? #f '=] [#:else '=])]
      [#:pred char?
       (tcmp char<? char=? x y)]
      [#:pred symbol?
       (cond [(symbol<? x y) '<]
             [(symbol<? y x) '>]
             [else ;; contents are same
              (with-cmp-cases x y
                [#:pred symbol-interned? '=]
                [#:pred symbol-unreadable? '=]
                [#:else #f])])]
      [#:pred keyword?
       (tcmp keyword<? eq? x y)]
      [#:pred string?
       (tcmp string<? string=? x y)]
      [#:pred bytes?
       (tcmp bytes<? bytes=? x y)]
      [#:pred path-for-some-system?
       ;; FIXME: type?
       (pcmp path<? equal? x y)]
      [#:pred regexp?
       (lexico (with-cmp-cases x y
                 [#:pred (lambda (v) (not (pregexp? v))) '=]
                 [#:else '=])
               (recur (object-name x) (object-name y)))]
      ;; Other compound
      [#:pred vector?
       (vector-cmp x y natural?)]
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
                 (vector-cmp (struct->vector x) (struct->vector y) 1 natural?)))]
      [#:pred=> fully-transparent-struct-type
       (lambda (xtype ytype)
         (lexico (struct-type-cmp xtype ytype)
                 (vector-cmp (struct->vector x) (struct->vector y) 1 natural?)))]
      [#:else #f]))
  (define (vector-cmp x y i)
    (let ([n (min (vector-length x) (vector-length y))])
      (let loop ([i i])
        (if (< i n)
            (lexico (recur (vector-ref x i) (vector-ref y i))
                    (loop (add1 i)))
            (tcmp < = (vector-length x) (vector-length y))))))
  (recur x y))

;; ----------------------------------------

(define (real-cmp x y natural?)
  (with-cmp-cases x y
    [#:pred (lambda (x) (not (NaN? x)))
     (lexico (tcmp < = x y)
             (if natural? '= (real-type/sign-cmp x y)))]
    [#:else (if natural? '= (real-type-cmp x y))]))

(define (real-type/sign-cmp x y)
  ;; PRE: x = y
  ;; -1.0 < -1 < -0.0 < 0 < 0.0 < 1 < 1.0
  (cond [(zero? x)
         (with-cmp-cases x y
           [#:eqv? -0.0 '=]
           [#:eqv? (real->single-flonum -0.0) '=]
           [#:eqv? 0 '=]
           [#:eqv? (real->single-flonum 0.0)  '=]
           [#:eqv? 0.0 '=])]
        [(positive? x) (real-type-cmp x y)]
        [else (real-type-cmp y x)]))

(define (real-type-cmp x y)
  (with-cmp-cases x y
    [#:pred exact? '=]
    [#:pred single-flonum? '=]
    [#:else '=]))

(define (hash-type-cmp x y)
  (lexico (with-cmp-cases x y [#:pred hash-eq? '=] [#:pred hash-eqv? '=] [#:pred hash-equal? '=])
          (with-cmp-cases x y [#:pred (lambda (v) (not (hash-weak? v))) '=] [#:else '=])
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
  (lexico (pcmp symbol<? eq? (object-name xtype) (object-name ytype))
          (lexico (pcmp < = (eq-hash-code xtype) (eq-hash-code ytype))
                  #f)))
