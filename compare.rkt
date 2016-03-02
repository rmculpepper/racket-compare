#lang racket/base
(provide natural-cmp
         natural<?
         natural>?
         natural=?
         natural<=?
         natural>=?
         datum-cmp
         datum<?
         datum>?
         datum=?
         datum<=?
         datum>=?)

;; ============================================================

(define (natural-cmp x y)
  (general-cmp x y #t))
;; ... < NaN < real (<, =) < complex (lexico) < ...

(define (datum-cmp x y)
  (general-cmp x y #f))
;; ... < NaN < real (< then by type, eqv?) < complex (lexico) < ...

;; If x natural<? y, then x datum<? y.
;; That is, datum-cmp makes finer distinctions than natural-cmp.

;; If x equal? y, then x datum-cmp y in {'=, #f}
;; That is, datum-cmp doesn't make more distinctions than equal?.
;; Note: custom-equal? may violate.

;; ============================================================

(define-syntax-rule (defchaining (f x y) rhs)
  (define f
    (case-lambda [(x y) rhs]
            [(x y . zs)
             (and rhs
                  ;; We use stop-on-shortest behavior of for/and
                  (for/and ([x (in-list (cons y zs))]
                            [y (in-list zs)])
                    rhs))])))
(define-syntax-rule (defcmp cmp <? >? =? <=? >=?)
  (begin (defchaining (<? x y) (eq? (cmp x y) '<))
         (defchaining (>? x y) (eq? (cmp x y) '>))
         (defchaining (=? x y) (eq? (cmp x y) '=))
         (defchaining (<=? x y) (and (memq (cmp x y) '(< =)) #t))
         (defchaining (>=? x y) (and (memq (cmp x y) '(> =)) #t))))

(defcmp datum-cmp   datum<?   datum>?   datum=?   datum<=?   datum>=?)
(defcmp natural-cmp natural<? natural>? natural=? natural<=? natural>=?)
