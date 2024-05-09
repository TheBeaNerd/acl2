; Flattens partial products and applies associated lemmas to already simplified
; summation tree terms.

; Copyright (C) 2021 Centaur Technology
; Copyright (C) 2022 Intel Corporation
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
; Original Author(s):
; Mertcan Temel         <mert@centtech.edu>

(in-package "RP")

(include-book "summation-tree-meta-fncs")

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "lemmas"))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (in-theory (disable +-IS-SUM)))

(local
 (in-theory (disable rp-termp)))

(local
 (in-theory (disable ex-from-rp
                     (:definition acl2::apply$-badgep)
                     (:linear acl2::apply$-badgep-properties . 1)
                     (:definition subsetp-equal)
                     (:definition member-equal)
                     (:rewrite
                      acl2::member-equal-newvar-components-1)
                     include-fnc)))

(local
 (set-induction-depth-limit 1))

(progn
  (define hons-copy2 ((term))
    (if (atom term)
        term
      (hons (hons-copy2 (car term))
            (hons-copy2 (cdr term))))
    ///
    (defthm hons-copy2-is-its-arg
      (equal (hons-copy2 term)
             term)))

  (memoize 'hons-copy2 :condition '(consp term))

  (encapsulate
    (((unpack-booth-later-hons-copy-enabled) => *))
    (local
     (defun unpack-booth-later-hons-copy-enabled ()
       nil)))

  (defmacro enable-unpack-booth-later-hons-copy (enable)
    (if enable
        `(defattach unpack-booth-later-hons-copy-enabled return-t)
      `(defattach  unpack-booth-later-hons-copy-enabled return-nil)))

  (enable-unpack-booth-later-hons-copy t)

  (define hons-copy-for-unpack-booth (term)
    :returns (res)
    (if (unpack-booth-later-hons-copy-enabled)
        (time$ (hons-copy2 term)
               :msg "-- hons-copy took ~st seconds
       (real-time), or ~sc seconds (cpu-time), and ~sa bytes allocated.~%"
               :run-mintime 1/8)
      term)
    ///
    (defret <fn>-correct (equal res term))))

#!RP
(local
 (defthm integerp-of-*RW-BACKCHAIN-LIMIT*
   (implies (rp-statep rp-state)
            (integerp
             (nth
              *rw-backchain-limit* rp-state)))
   :hints (("Goal"
            :in-theory (e/d (rp-statep) ())))))

(define unpack-booth-for-pp-lst ((pp-lst rp-term-listp))
  :returns (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
  :verify-guards :after-returns
  :prepwork ((local
              (in-theory (enable rp-term-listp))))
  (if (atom pp-lst)
      nil
    (pp-sum-merge-aux
     (b* (((mv coef cur) (get-pp-and-coef (car pp-lst))))
       (cond ((pp-term-p cur)
              (append-with-times coef (pp-flatten-with-binds cur) nil))
             ((or (and-list-p cur)
                  (--.p cur)
                  (logbit-p cur))
              (list (create-times-instance coef cur)))
             ((binary-fnc-p (ex-from-rp cur))
              (list (create-times-instance coef cur)))
             (t
              (progn$ (hard-error 'unpack-booth-for-pp-lst
                                  "Unexpected pp-arg ~p0 ~%"
                                  (list (cons #\0 (car pp-lst))))
                      (list (car pp-lst))))))
     (unpack-booth-for-pp-lst (cdr pp-lst)))))

(define include-binary-fnc-p (term)
  (or (include-fnc term 'binary-not)
      (include-fnc term 'binary-and)
      (include-fnc term 'binary-or)
      (include-fnc term 'binary-?)
      (include-fnc term 'binary-xor)))

(define need-to-unpack-s/c-buried-in-pp ((term rp-termp))
  :returns (res booleanp)
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((term (ex-from-rp$ term)))
    (cond ((binary-?-p term)
           (and (need-to-unpack-s/c-buried-in-pp (cadr term))
                (need-to-unpack-s/c-buried-in-pp (caddr term))
                (need-to-unpack-s/c-buried-in-pp (cadddr term))))
          ((or (binary-or-p term)
               (binary-and-p term)
               (binary-xor-p term))
           (and (need-to-unpack-s/c-buried-in-pp (cadr term))
                (need-to-unpack-s/c-buried-in-pp (caddr term))))
          ((or (binary-not-p term))
           (and (need-to-unpack-s/c-buried-in-pp (cadr term))))
          ((or (single-s-p term)
               (single-c-p term)
               (s-c-res-p term))
           (include-binary-fnc-p term))
          (t nil))))

(local
 (defthm rp-termp-of-binary-and/or/xor
   (implies (or (equal x 'binary-and)
                (equal x 'binary-or)
                (equal x 'binary-xor))
            (iff (rp-termp (list x a b))
                 (and (rp-termp a)
                      (rp-termp b))))
   :hints (("Goal"
            :in-theory (e/d (rp-termp) ())))))

(local
 (defthm rp-termp-of-binary-?
   (implies (or (equal x 'binary-?)
                )
            (iff (rp-termp (list x a b c))
                 (and (rp-termp a)
                      (rp-termp b)
                      (rp-termp c))))
   :hints (("Goal"
            :in-theory (e/d (rp-termp) ())))))

(local
 (defthm rp-termp-of-binary-not
   (implies (or (equal x 'binary-not)
                )
            (iff (rp-termp (list x a))
                 (and (rp-termp a))))
   :hints (("Goal"
            :in-theory (e/d (rp-termp) ())))))

(define unique-e-count (lst)
  (if (atom lst)
      0
    (if (atom (cdr lst))
        1
      (if (rp-equal-cnt (ex-from-rp/times (car lst)) (ex-from-rp/times (cadr lst)) 3)
          (unique-e-count (cdr lst))
        (1+ (unique-e-count (cdr lst)))))))

(defthm rp-termp-of-trans-list
  (implies (rp-term-listp lst)
           (rp-termp (trans-list lst))))

(acl2::defines
 unpack-booth-for-s

 :flag-defthm-macro defthm-unpack-booth-for-s
 :flag-local nil

 :prepwork ((local
             (in-theory (enable measure-lemmas)))

            (local
             (defthm cons-count-of-list-to-lst-1
               (implies (and (consp s-term)
                             (consp (cdr s-term))
                             (consp (cddr s-term))
                             (consp (cdddr s-term))
                             (not (cddddr s-term)))
                        (o< (cons-count (list-to-lst (cadddr s-term)))
                            (cons-count s-term)))
               :hints (("goal"
                        :do-not-induct t
                        :expand ((cons-count s-term)
                                 (cons-count (cdr s-term))
                                 (list-to-lst (cadddr s-term)))
                        :in-theory (e/d (cons-count
                                         list-to-lst
                                         )
                                        ())))))

            (local
             (defthm cons-count-of-list-to-lst-2
               (implies (and (consp c-term)

                             (consp (cdr c-term))
                             (consp (cddr c-term))
                             (consp (cdddr c-term))
                             (consp (cddddr c-term))
                             (not (cdr (cddddr c-term))))
                        (o< (cons-count (list-to-lst (car (cddddr c-term))))
                            (cons-count c-term)))
               :hints (("goal"
                        :do-not-induct t
                        :expand ((cons-count c-term)
                                 (cons-count (cdr c-term))
                                 (list-to-lst (car (cddddr c-term))))
                        :in-theory (e/d (cons-count
                                         list-to-lst
                                         )
                                        ())))))

            (local
             (defthm cons-count-of-list-to-lst-3
               (implies (and (consp c-term)
                             (consp (cdr c-term))
                             (consp (cddr c-term))
                             (consp (cdddr c-term))
                             (consp (cddddr c-term))
                             (not (cdr (cddddr c-term))))
                        (o< (cons-count (list-to-lst (caddr c-term)))
                            (cons-count c-term)))
               :hints (("goal"
                        :do-not-induct t
                        :expand ((cons-count c-term)
                                 (CONS-COUNT (CDDR C-TERM))
                                 (CONS-COUNT (CDDDR C-TERM))
                                 (cons-count (cdr c-term))
                                 (list-to-lst (caddr c-term)))
                        :in-theory (e/d (cons-count
                                         list-to-lst
                                         )
                                        ())))))

            (local
             (defthm cons-count-of-ex-from-rp
               (<= (cons-count (ex-from-rp term))
                   (cons-count term))))

            (local
             (defthm dummy-mes-lemma
               (implies (and
                         (integerp other)
                         (o< other (cons-count (ex-from-rp term))))
                        (o< other (cons-count term)))
               :hints (("Goal"
                        :do-not-induct t
                        :use ((:instance cons-count-of-ex-from-rp))
                        :in-theory (e/d (o<) (cons-count-of-ex-from-rp))))))

            (local
             (defthm dummy-equiva-lemma
               (implies (and (<= x y)
                             (natp x)
                             (natp y)
                             (natp a)
                             (natp b))
                        (<= x (+ a y b)))))

            (local
             (defthm cons-count-of-ex-from-rp-2
               (<= (cons-count (ex-from-rp (cadr term)))
                   (cons-count term))
               :hints (("Goal"
                        :expand ((CONS-COUNT TERM)
                                 (CONS-COUNT (CDR TERM)))
                        :use ((:instance cons-count-of-ex-from-rp (term (cadr term)))
                              (:instance dummy-equiva-lemma
                                         (x (CONS-COUNT (EX-FROM-RP (CADR
                                                                     TERM))))
                                         (y    (CONS-COUNT (CADR TERM)))
                                         (a (CONS-COUNT (CAR TERM)))
                                         (b (CONS-COUNT (CDDR TERM)))))
                        :in-theory (e/d () (cons-count-of-ex-from-rp))))))

            (local
             (defthm dummy-mes-lemma-2
               (implies (and
                         (integerp other)
                         (consp term)
                         (consp (cdr term))
                         (o< other (cons-count (ex-from-rp (cadr term)))))
                        (o< other (cons-count term)))
               :hints (("Goal"
                        :do-not-induct t
                        :use ((:instance cons-count-of-ex-from-rp-2))
                        :in-theory (e/d (o<) (cons-count-of-ex-from-rp))))))

            )

 :verify-guards nil

 (define unpack-booth-buried-in-pp ((term rp-termp)
                                    &optional
                                    ((limit natp) 'limit))
   :returns (res-term rp-termp :hyp (rp-termp term))
   :measure (nfix limit)
   :no-function t
   (if (zp limit)
       term
     (let ((limit (1- limit)))
       (b* ((has-bitp (has-bitp-rp term))
            (term (ex-from-rp$ term)))
         (cond ((binary-not-p term)
                (cons-with-hint (car term)
                                (cons-with-hint
                                 (unpack-booth-buried-in-pp (cadr term))
                                 nil
                                 (cdr term))
                                term))
               ((or (binary-or-p term)
                    (binary-and-p term)
                    (binary-xor-p term))
                (cons-with-hint (car term)
                                (cons-with-hint
                                 (unpack-booth-buried-in-pp (cadr term))
                                 (cons-with-hint (unpack-booth-buried-in-pp (caddr term))
                                                 nil
                                                 (cddr term))
                                 (cdr term))
                                term))
               ((binary-?-p term)
                (cons-with-hint (car term)
                                (cons-with-hint
                                 (unpack-booth-buried-in-pp (cadr term))
                                 (cons-with-hint (unpack-booth-buried-in-pp (caddr term))
                                                 (cons-with-hint (unpack-booth-buried-in-pp (cadddr term))
                                                                 nil
                                                                 (cdddr term))
                                                 (cddr term))
                                 (cdr term))
                                term))
               ((single-s-p term)
                (b* (((mv s-res-lst pp-res-lst c-res-lst)
                      (unpack-booth-for-s term)))
                  (create-s-c-res-instance s-res-lst pp-res-lst c-res-lst t)))
               ((single-c-p term)
                (b* (((mv s-res-lst pp-res-lst c-res-lst)
                      (unpack-booth-for-c term)))
                  (create-s-c-res-instance s-res-lst pp-res-lst c-res-lst
                                           has-bitp)))
               (t term))))))

 (define unpack-booth-process-pp-arg ((pp-arg rp-termp) &optional
                                      ((limit natp) 'limit))
   :returns (mv (s-res-lst rp-term-listp
                           :hyp (rp-termp pp-arg))
                (pp-res-lst rp-term-listp
                            :hyp (rp-termp pp-arg))
                (c-res-lst rp-term-listp
                           :hyp (rp-termp pp-arg)))
   :measure (nfix limit)
   :no-function t
   (if (zp limit)
       (mv nil (list-to-lst pp-arg) nil)
     (let ((limit (1- limit)))
       (b* ((pp-arg-lst (list-to-lst pp-arg))
            (pp-arg-lst (unpack-booth-buried-in-pp-lst pp-arg-lst))
            (pp-arg-lst (unpack-booth-for-pp-lst pp-arg-lst))

            ((mv s-lst1 pp-arg-lst c-lst1) (ex-from-pp-lst pp-arg-lst))
            ((mv s-lst2 pp-arg-lst c-lst2) (cross-product-pp pp-arg-lst))

            #|(- (and (not (pp-lst-orderedp pp-arg-lst))
            (not (cw "in unpack-booth-process-pp-arg
            ~%"))))|#)
         (mv (s-sum-merge-aux s-lst1 s-lst2)
             pp-arg-lst
             (s-sum-merge-aux c-lst1 c-lst2))))))

 (define unpack-booth-buried-in-pp-lst ((lst rp-term-listp)
                                        &optional
                                        ((limit natp) 'limit))
   :returns (res-lst rp-term-listp
                     :hyp (rp-term-listp lst))
   :measure (nfix limit)
   :no-function t
   (if (zp limit)
       lst
     (let ((limit (1- limit)))
       (cond
        ((atom lst)
         nil)
        (t
         (cons-with-hint (if (need-to-unpack-s/c-buried-in-pp (car lst))
                             (unpack-booth-buried-in-pp (car lst))
                           (car lst))
                         (unpack-booth-buried-in-pp-lst (cdr lst))
                         lst))))))

 (define unpack-booth-for-s ((s-term rp-termp)
                             &optional
                             ((limit natp) 'limit))
   :returns (mv (s-res-lst rp-term-listp
                           :hyp (rp-termp s-term))
                (pp-res-lst rp-term-listp
                            :hyp (rp-termp s-term))
                (c-res-lst rp-term-listp
                           :hyp (rp-termp s-term)))
   :measure (nfix limit)
   :no-function t
   (if (zp limit)
       (mv (list s-term) nil nil)
     (let ((limit (1- limit)))
       (b* (((Unless (include-binary-fnc-p s-term))
             (mv (list s-term) nil nil))
            (?orig s-term)
            ;; ((mv s-term negated) (case-match s-term
            ;;                        (('-- s-term) (mv s-term t))
            ;;                        (& (mv s-term nil))))

            ((mv coef s-term)
             (get-pp-and-coef s-term)
             ;; (case-match c-term
             ;;   (('-- term) (mv term t))
             ;;   (& (mv c-term nil)))
             )

            (term (ex-from-rp$ s-term)))
         (case-match term
           (('s hash pp-arg c-arg)
            (b* ((- hash)
                 (& (cw "Unpack-booth-meta: s hash ~p0 ~%" hash))

                  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

                 (pp-arg-lst0
                  (extract-binary-xor-for-s-spec-aux-lst (list-to-lst pp-arg)))

                 ((mv s0 pp-arg-lst0 c-arg-lst0)
                  (new-sum-merge (trans-list pp-arg-lst0)))
                 (s-arg-lst0 (list-to-lst s0))

                  ;;;;;;;;;;;;;;;;;

                 ;; first lest unpack these pp args
                 ((mv s-arg-lst1 pp-arg-lst0 c-arg-lst1)
                  (unpack-booth-process-pp-arg (create-list-instance pp-arg-lst0)))

                 #|(- (and (not (ordered-s/c-p-lst s-arg-lst0))
                 (not (cw "in unpack-booth-for-s. s-arg-lst0 after unpack-booth-process-pp-arg
                 ~%"))
                 (cwe "pp-arg that goes into
                 unpack-booth-process-pp-arg:~p0 ~%"
                 pp-arg)))|#

                 #|(- (and (not (pp-lst-orderedp pp-arg-lst2))
                 (not (cw "in unpack-booth-for-s. pp-arg-lst2 before unpack-booth-for-c-lst ~%"))))|#

                 ;; then unpack the c-args
                 (c-arg-lst (list-to-lst c-arg))
                 ((mv s-arg-lst2 pp-arg-lst2 c-arg-lst2)
                  (unpack-booth-for-c-lst c-arg-lst))
                 ;; merge the new pp args derived from the c args

                 #|(- (and (not (ordered-s/c-p-lst s-arg-lst))
                 (not (cw "in unpack-booth-for-s. s-arg-lst after unpack-booth-for-c-lst
                 ~%"))))|#

                 #|(- (and (not (pp-lst-orderedp pp-arg-lst))
                 (not (cw "in unpack-booth-for-s. pp-arg-lst before
                 pp-sum-merge-lst-for-s ~%"))))|#

                 #|(- (and (not (pp-lst-orderedp pp-arg-lst2))
                 (not (cw "in unpack-booth-for-s. pp-arg-lst2 before pp-sum-merge-lst-for-s ~%"))))|#

                 ;;(pp-arg-lst (pp-sum-merge-lst-for-s pp-arg-lst1 pp-arg-lst2))
                 (pp-arg-lst (pp-sum-merge-lst-for-s pp-arg-lst2 pp-arg-lst0))

                 (& (or (pp-lst-orderedp pp-arg-lst)
                        (hard-error 'unpack-booth-for-s
                                    "place3: unordered pp-arg-lst
input:~p0~%output:~p1~%" (list (cons #\0 s-term)
                               (cons #\1 pp-arg-lst)))))

                 (c-arg-lst (sum-merge-lst-for-s c-arg-lst0 (sum-merge-lst-for-s c-arg-lst1 c-arg-lst2)))
                 (s-arg-lst (sum-merge-lst-for-s s-arg-lst0 (sum-merge-lst-for-s s-arg-lst1 s-arg-lst2))) ;; no need to keep it sorted

                 #| (- (and (not (pp-lst-orderedp pp-arg-lst))
                 (not (cw "in unpack-booth-for-s. before s-of-s-fix-lst
                 ~%"))))

                 (- (and (not (ordered-s/c-p-lst s-arg-lst))
                 (not (cw "in unpack-booth-for-s. s-arg-lst before
                 s-of-s-fix-lst ~%"))))

                 (- (and (not (ordered-s/c-p-lst c-arg-lst))
                 (not (cw "in unpack-booth-for-s. c-arg-lst before s-of-s-fix-lst ~%"))))|#

                 ((mv pp-arg-lst c-arg-lst)
                  (s-of-s-fix-lst (s-fix-pp-args-aux s-arg-lst)
                                  (s-fix-pp-args-aux pp-arg-lst)
                                  (s-fix-pp-args-aux c-arg-lst)
                                  ))

                 (& (cw "after s-of-s-fix-lst len of pp-arg-lst  ~p0, c-arg-lst ~p1. Unique: pp-arg-lst ~p2 c-arg-lst ~p3 ~%"
                        (len pp-arg-lst) (len c-arg-lst)
                        "-" #|(unique-e-count pp-arg-lst)|# "-"#|(unique-e-count c-arg-lst)|#))

                 ;; (& (or (ordered-s/c-p-lst s-arg-lst)
                 ;;                         (hard-error 'unpack-booth-for-s
                 ;;                                     "place4: unordered s-arg-lst
                 ;; input:~p0~%output:~p1~%" (list (cons #\0 s-term)
                 ;;                                (cons #\1 s-arg-lst)))))
                 ;;                  (& (or (pp-lst-orderedp pp-arg-lst)
                 ;;                         (hard-error 'unpack-booth-for-s
                 ;;                                     "place4: unordered pp-arg-lst
                 ;; input:~p0~%output:~p1~%" (list (cons #\0 s-term)
                 ;;                                (cons #\1 pp-arg-lst)))))

                 #|(- (and (not (pp-lst-orderedp pp-arg-lst))
                 (not (cw "in unpack-booth-for-s. before s-fix-pp-args-aux ~%"))))|#

                 (pp-arg-lst (s-fix-pp-args-aux pp-arg-lst))
                 (c-arg-lst (s-fix-pp-args-aux c-arg-lst))

                 (& (cw "after s-fix-pp-args-aux len of pp-arg-lst  ~p0, ~
c-arg-lst  ~p1. Unique: pp-arg-lst ~p2 c-arg-lst ~p3 ~%"
                        (len pp-arg-lst) (len c-arg-lst)
                        "-"#|(unique-e-count pp-arg-lst)|# "-"#|(unique-e-count c-arg-lst)|#
                        ))

                 ;; (& (or (pp-lst-orderedp pp-arg-lst)
                 ;;                         (hard-error 'unpack-booth-for-s
                 ;;                                     "place5: unordered pp-arg-lst
                 ;; input:~p0~%output:~p1~%" (list (cons #\0 s-term)
                 ;;                                (cons #\1 pp-arg-lst)))))

                 ;;                  (& (or (ordered-s/c-p-lst c-arg-lst)
                 ;;                         (hard-error 'unpack-booth-for-s
                 ;;                                     "unordered c-arg-lst
                 ;; input:~p0~%output:~p1~%" (list (cons #\0 s-term)
                 ;;                                (cons #\1 c-arg-lst)))))

                 #|(- (and (not (pp-lst-orderedp pp-arg-lst))
                 (not (cw "in unpack-booth-for-s. pp-arg-lst is not
                 ordered ~%"))
                 (cwe "Input s-term: ~p0. Current pp-arg-lst ~p1~%"
                 s-term pp-arg-lst)))|#

                 ((mv s-res-lst pp-res-lst c-res-lst)
                  (create-s-instance (create-list-instance pp-arg-lst)
                                     (create-list-instance c-arg-lst))))

              (mv (append-with-times coef s-res-lst nil)
                  (append-with-times coef pp-res-lst nil)
                  (append-with-times coef c-res-lst nil))
              ;; (if negated
              ;;     (mv (negate-lst s-res-lst)
              ;;         (negate-lst pp-res-lst)
              ;;         (negate-lst c-res-lst))
              ;;   (mv s-res-lst pp-res-lst c-res-lst))
              ))
           (''0
            (mv nil nil nil))
           (& (progn$
               (hard-error 'unpack-booth-for-s
                           "Unrecognized s instance: ~p0 ~%"
                           (list (cons #\0 orig)))
               (mv (list orig) nil nil))))))))

 (define unpack-booth-for-s-lst ((s-lst rp-term-listp)
                                 &optional
                                 ((limit natp) 'limit))
   :returns (mv (s-res-lst rp-term-listp
                           :hyp (rp-term-listp s-lst))
                (pp-res-lst rp-term-listp
                            :hyp (rp-term-listp s-lst))
                (c-res-lst rp-term-listp
                           :hyp (rp-term-listp s-lst)))
   :measure (nfix limit)
   :no-function t
   (if (zp limit)
       (mv s-lst nil nil)
     (let ((limit (1- limit)))
       (cond
        ((atom s-lst)
         (mv nil nil nil))
        (t
         (b* (((mv s-res-lst1 pp-res-lst1 c-res-lst1)
               (unpack-booth-for-s (car s-lst)))
              ((mv s-res-lst2 pp-res-lst2 c-res-lst2)
               (unpack-booth-for-s-lst (cdr s-lst))))
           (mv (s-sum-merge-aux s-res-lst1 s-res-lst2)
               (pp-sum-merge-aux pp-res-lst1 pp-res-lst2)
               (s-sum-merge-aux c-res-lst1 c-res-lst2))))))))

 (define unpack-booth-for-c ((c-term rp-termp)
                             &optional
                             ((limit natp) 'limit))
   :returns (mv (s-res-lst rp-term-listp
                           :hyp (rp-termp c-term))
                (pp-res-lst rp-term-listp
                            :hyp (rp-termp c-term))
                (c-res-lst rp-term-listp
                           :hyp (rp-termp c-term)))
   :measure (nfix limit)
   :no-function t
   (if (zp limit)
       (mv nil nil (list c-term))
     (let ((limit (1- limit)))
       (b* (((Unless (include-binary-fnc-p c-term))
             (mv nil nil (list c-term)))
            (?orig c-term)
            ((mv coef c-term)
             (get-pp-and-coef c-term)
             ;; (case-match c-term
             ;;   (('-- term) (mv term t))
             ;;   (& (mv c-term nil)))
             )
            (term (ex-from-rp c-term))
            )
         (case-match term
           (('c hash s-arg pp-arg c-arg)
            (b* ((- hash)
                 (& (cw "Unpack-booth-meta: c hash ~p0 ~%" hash))

                 ;; first lest unpack these pp args
                 ;; (pp-arg-lst (list-to-lst pp-arg))
                 ;; (pp-arg-lst (unpack-booth-buried-in-pp-lst pp-arg-lst))
                 ;; (pp-arg-lst (unpack-booth-for-pp-lst pp-arg-lst))

                 ((mv s-arg-lst0 pp-arg-lst c-arg-lst0)
                  (unpack-booth-process-pp-arg pp-arg))

                 (s-arg-lst (s-sum-merge-aux s-arg-lst0 (list-to-lst s-arg)))
                 (c-arg-lst (s-sum-merge-aux c-arg-lst0 (list-to-lst c-arg)))
                 ;; then unpack the s-args

                 ((mv s-arg-lst pp-arg-lst2 c-arg-lst2)
                  (unpack-booth-for-s-lst s-arg-lst))
                 (pp-arg-lst (pp-sum-merge-aux pp-arg-lst pp-arg-lst2))

                 ;; unpack the c-args
                 ((mv s-arg-lst3 pp-arg-lst3 c-arg-lst)
                  (unpack-booth-for-c-lst c-arg-lst))
                 (c-arg-lst (s-sum-merge-aux c-arg-lst c-arg-lst2))

                 (s-arg-lst (s-sum-merge-aux s-arg-lst s-arg-lst3))

                 (pp-arg-lst (pp-sum-merge-aux pp-arg-lst pp-arg-lst3))

                 ;; cough out s-args
                 ((mv coughed-s-lst s-arg-lst)
                  (c-fix-arg-aux s-arg-lst ))

                 ((mv pp-arg-lst c-arg-lst
                      coughed-s-lst2 coughed-pp-lst2 coughed-c-lst2)
                  (c-of-s-fix-lst s-arg-lst pp-arg-lst c-arg-lst nil))

                 (& (cw "after c-of-s-fix-lst: len of pp-arg-lst ~p0, c-arg-lst ~p1 ~
coughed-s-lst2 ~p2, coughed-pp-lst2 ~p3, coughed-c-lst2 ~p4. Unique pp-arg-lst ~p5 ~%" (len pp-arg-lst)
(len c-arg-lst)
(len coughed-s-lst2) (len coughed-pp-lst2) (len coughed-c-lst2) (unique-e-count
                                                                 pp-arg-lst)))

                 (s-arg-lst nil)

                 ;; cough out pp-args
                 ((mv coughed-pp-lst pp-arg-lst)
                  (c-fix-arg-aux pp-arg-lst ))

                 ((mv coughed-c-lst c-arg-lst)
                  (c-fix-arg-aux c-arg-lst ))

                 (& (cw "after c-fix-arg-aux len of pp-arg-lst  ~p0, c-arg-lst ~p1~
, coughed-pp-lst ~p2, coughed-c-lst ~p3. Unique coughed-pp-lst ~p4~%" (len pp-arg-lst)
  (len c-arg-lst)
  (len coughed-pp-lst) (len coughed-c-lst) "-"#|(unique-e-count coughed-pp-lst)|#))

                 #|(- (cw "create-c-instance args: s-arg-lst:~p0
                 pp-arg-lst:~p1 ; ;
                 c-arg-lst:~p2~%" s-arg-lst pp-arg-lst c-arg-lst))|#
                 ;; create-c-instance
                 ((mv s-res-lst pp-res-lst c-res-lst)
                  (create-c-instance s-arg-lst pp-arg-lst c-arg-lst))

                 (c-res-lst (s-sum-merge-aux c-res-lst coughed-c-lst))
                 (c-res-lst (s-sum-merge-aux c-res-lst coughed-c-lst2))
                 (s-res-lst (s-sum-merge-aux s-res-lst coughed-s-lst))
                 (s-res-lst (s-sum-merge-aux s-res-lst coughed-s-lst2))
                 (pp-res-lst (pp-sum-merge-aux pp-res-lst coughed-pp-lst))
                 (pp-res-lst (pp-sum-merge-aux pp-res-lst coughed-pp-lst2))

                 (& (cw "after final sum-merges in c len of pp-res-lst  ~p0, s-res-lst ~p1~
c-res-lst ~p2, ~%~%" (len pp-res-lst)
(len s-res-lst)
(len c-res-lst)))

                 #|(- (and (not (pp-lst-orderedp pp-res-lst))
                 (cw "in unpack-booth-for-c. pp-res-lst is not ordered ~%")))|#

                 (& (or (pp-lst-orderedp pp-res-lst)
                        (hard-error 'unpack-booth-for-c
                                    "unordered pp-res-lst
input:~p0~%output:~p1~%" (list (cons #\0 c-term)
                               (cons #\1 pp-res-lst)))))

                 (& (or (ordered-s/c-p-lst c-res-lst)
                        (hard-error 'unpack-booth-for-c
                                    "unordered c-res-lst
input:~p0~%output:~p1~%" (list (cons #\0 c-term)
                               (cons #\1 c-res-lst)))))

                 (& (or (ordered-s/c-p-lst s-res-lst)
                        (hard-error 'unpack-booth-for-c
                                    "unordered s-res-lst
input:~p0~%output:~p1~%" (list (cons #\0 c-term)
                               (cons #\1 s-res-lst))))))

              (mv (append-with-times coef s-res-lst nil)
                  (append-with-times coef pp-res-lst nil)
                  (append-with-times coef c-res-lst nil))
              ;; (if signed
              ;;     (mv (negate-lst s-res-lst)
              ;;         (Negate-Lst pp-res-lst)
              ;;         (negate-lst c-res-lst))
              ;;   (mv s-res-lst pp-res-lst c-res-lst))
              ))
           (''0
            (mv nil nil nil))
           (& (progn$
               (hard-error 'unpack-booth-for-c
                           "Unrecognized c instance: ~p0 ~%"
                           (list (cons #\0 orig)))
               (mv (list orig) nil nil))))))))

 (define unpack-booth-for-c-lst ((c-lst rp-term-listp)
                                 &optional
                                 ((limit natp) 'limit))
   :returns (mv (s-res-lst rp-term-listp
                           :hyp (rp-term-listp c-lst))
                (pp-res-lst rp-term-listp
                            :hyp (rp-term-listp c-lst))
                (c-res-lst rp-term-listp
                           :hyp (rp-term-listp c-lst)))
   :measure (nfix limit)
   :no-function t
   (if (zp limit)
       (mv nil nil c-lst)
     (let ((limit (1- limit)))
       (cond ((atom c-lst)
              (mv nil nil nil))
             (t
              (b* (((mv s-res-lst1 pp-res-lst1 c-res-lst1)
                    (unpack-booth-for-c (car c-lst)))
                   ((mv s-res-lst2 pp-res-lst2 c-res-lst2)
                    (unpack-booth-for-c-lst (cdr c-lst))))
                (mv (s-sum-merge-aux s-res-lst1 s-res-lst2)
                    (pp-sum-merge-aux pp-res-lst1 pp-res-lst2)
                    (s-sum-merge-aux c-res-lst1 c-res-lst2))))))))

 ///

 (verify-guards unpack-booth-for-c-lst-fn))

(acl2::memoize-partial
 ((unpack-booth-buried-in-pp* unpack-booth-buried-in-pp-fn)
  (unpack-booth-process-pp-arg* unpack-booth-process-pp-arg-fn
                                :condition nil
                                :aokp t)
  (unpack-booth-buried-in-pp-lst* unpack-booth-buried-in-pp-lst-fn)
  ;; unpack for subsequent mult proofs in the same module:
  (unpack-booth-for-s* unpack-booth-for-s-fn
                       :condition t
                       :aokp t)
  (unpack-booth-for-s-lst* unpack-booth-for-s-lst-fn)
  (unpack-booth-for-c* unpack-booth-for-c-fn
                       :condition t
                       :aokp t)
  (unpack-booth-for-c-lst* unpack-booth-for-c-lst-fn))
 :condition nil)

#|(define good-s-chain ((term))
:measure (cons-count term)
:hints (("Goal"
:in-theory (e/d (measure-lemmas) ())))
(b* ((term (ex-from-rp term)))
(case-match term
(('s & & ('list single-c))
(good-s-chain single-c))
(('s & & ''nil)
t)
(('c & & & ('list single-c))
(good-s-chain single-c))
(('c & & & ''nil)
t)
(& nil))))|#

(local
 (defthm binary-fnc-p-implies
   (implies (BINARY-FNC-P x)
            (and (not (equal (car x) 'c))
                 (not (equal (car x) 's))
                 (not (equal (car x) 's-c-res))))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (binary-fnc-p) ())))))

(local
 (defthm rp-termp-list-lemma
   (iff (RP-TERMP (LIST 'LIST x))
        (RP-TERMP x))
   :hints (("Goal"
            :in-theory (e/d (rp-termp) ())))))

(defines has-binary-fnc-p
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (define has-binary-fnc-p (term (level natp))
    :measure (acl2::nat-list-measure (list level (cons-count term)))
    (b* ((term (ex-from-rp term)))
      (cond ((zp level)
             nil)
            ((atom term)
             nil)
            ((binary-fnc-p term)
             t)
            (t (has-binary-fnc-p-lst (cdr term) (1- level))))))
  (define has-binary-fnc-p-lst (lst (level natp))
    :measure (acl2::nat-list-measure (list level (cons-count lst)))
    (if (atom lst)
        nil
      (or (has-binary-fnc-p (car lst) level)
          (has-binary-fnc-p-lst (cdr lst) level)))))

(define unpack-booth-meta ((term rp-termp))
  :returns (mv (res rp-termp
                    :hyp (rp-termp term)
                    :hints (("Goal"
                             :expand ((:free (x)
                                             (rp-termp (cons '-- x))))
                             :in-theory (e/d ()
                                             (nfix)))))
               (dont-rw))
  :guard-hints (("Goal"
                 :in-theory (e/d () (nfix))))

  (b* ((subterm (case-match term (('unpack-booth subterm) subterm) (& term)))
       ((unless (or ;;(binary-fnc-p (ex-from-rp subterm))
                 (unpack-booth-later-enabled)
                 (has-binary-fnc-p subterm 4)))
        (mv term nil))

       ;;(- (hard-error 'stop-hre "" nil))
       ((mv coef subterm)
        (get-pp-and-coef subterm))
       ;; (case-match subterm
       ;;   (('-- subterm) (mv subterm t))
       ;;   (& (mv subterm nil)))

       (subterm-orig subterm)
       (subterm (ex-from-rp subterm))

       (has-bitp (or* (has-bitp-rp subterm-orig)
                      (binary-fnc-p subterm)
                      (single-s-p subterm)))

       #|((when (binary-fnc-p subterm))
       (mv term nil))|#
       ((when (or (logbit-p subterm)
                  (and (has-bitp-rp subterm-orig)
                       (atom subterm))))
        (b* ((res (create-and-list-instance (list subterm-orig))))
          (mv (create-times-instance coef res) t)))
       ;;(subterm-orig (hons-copy subterm-orig))
       (subterm-orig
        (hons-copy-for-unpack-booth subterm-orig))

       #|(- (or (good-s-chain subterm)
       (hard-error 'unpack-booth-meta ; ;
       "Not a good s chain ~p0~%" ; ;
       (list (cons #\0 subterm)))))|#

       ((mv s-res-lst pp-res-lst c-res-lst)
        (cond
         ((single-s-p subterm)
          (unpack-booth-for-s* subterm-orig))
         ((single-c-p subterm)
          (unpack-booth-for-c* subterm-orig))
         ((single-s-c-res-p subterm)
          (b* (((mv s-arg pp-arg c-arg)
                (mv (cadr subterm) (caddr subterm) (cadddr subterm)))
               ((mv s-res-lst0 pp-res-lst0 c-res-lst0)
                (unpack-booth-process-pp-arg* pp-arg))
               ((mv s-res-lst1 pp-res-lst1 c-res-lst1)
                (unpack-booth-for-s-lst* (list-to-lst s-arg)))
               ((mv s-res-lst2 pp-res-lst2 c-res-lst2)
                (unpack-booth-for-c-lst* (list-to-lst c-arg)))
               ;; merge  the results

               (pp-res-lst (pp-sum-merge-aux pp-res-lst0
                                             (pp-sum-merge-aux pp-res-lst1
                                                               pp-res-lst2)))
               (s-res-lst (s-sum-merge-aux s-res-lst0 (s-sum-merge-aux s-res-lst1 s-res-lst2)))
               (c-res-lst (s-sum-merge-aux c-res-lst0 (s-sum-merge-aux c-res-lst1 c-res-lst2))))
            (mv s-res-lst pp-res-lst c-res-lst)))
         ((binary-fnc-p subterm)
          (b* (;; THIS CASE LIKELY HAPPENS FOR FLAGS OR SATURATION CASES. it's
               ;; possible that the user might set the term-size-limit to a
               ;; large number. We don't want a large number to be applied to
               ;; the pp-flatten that will take place here. So calling
               ;; pp-flatten ahead of time to see if the term can be simplified
               ;; with a small limit. If so, all is good. Otherwise, it's
               ;; probably best to rely on the SAT solver to deal with this
               ;; case.
               (flatten-res (and (pp-term-p subterm)
                                 (pp-flatten subterm :term-size-limit 100)))
               ;; try with a small limit before going crazy over it.
               ((when (equal (len flatten-res) 1))
                (mv nil (list subterm) nil)))
            (unpack-booth-process-pp-arg* `(list ,subterm))))
         (t
          (progn$ (hard-error 'unpack-booth-meta
                              "Unrecognized term ~p0 ~%"
                              (list (cons #\0 subterm-orig)))
                  (mv nil nil nil)))))

       ((unless (or* (single-s-p subterm)
                     (single-c-p subterm)
                     (single-s-c-res-p subterm)
                     (binary-fnc-p subterm)))
        ;; same conditions as above the case statement.
        (mv term nil))

       ;; (& (or (ordered-s/c-p-lst c-res-lst)
       ;;                  (hard-error 'unpack-booth-meta
       ;;                              "unordered c-res-lst
       ;; input:~p0~%output:~p1~%" (list (cons #\0 subterm)
       ;;                                (cons #\1 c-res-lst)))))
       ;;           (& (or (ordered-s/c-p-lst s-res-lst)
       ;;                  (hard-error 'unpack-booth-meta
       ;;                              "unordered s-res-lst
       ;; input:~p0~%output:~p1~%" (list (cons #\0 subterm)
       ;;                                (cons #\1 s-res-lst)))))
       ;;           (& (or (pp-lst-orderedp pp-res-lst)
       ;;                  (hard-error 'unpack-booth-meta
       ;;                              "unordered pp-res-lst
       ;; input:~p0~%output:~p1~%" (list (cons #\0 subterm)
       ;;                                (cons #\1 pp-res-lst)))))

       (res (create-s-c-res-instance s-res-lst pp-res-lst c-res-lst
                                     has-bitp))

       #|(- (and (not (ordered-s/c-p res))
       (not (cwe "res has unordered things in it in unpack-booth-meta ~%")) ; ;
       (not (cwe "input term: ~p0 ~%" term)) ; ;
       (hard-error nil "" nil)))|#

       ;; (& (or (ordered-s/c-p res)
       ;;                  (hard-error 'unpack-booth-meta
       ;;                              "unordered c-res-lst
       ;; input:~p0~%output:~p1~%" (list (cons #\0 subterm)
       ;;                                (cons #\1 res)))))

       (res (create-times-instance coef res)))
    (mv res t)))

#|(local
(defthm is-rp-lemma
(implies (and (rp-termp term)
(equal (car term) 'rp))
(and (quotep (cadr term))
(consp (cdr term))
(implies (and (equal (car other) (cadr term))
(CONSP (CDR OTHER))
(NOT (CDDR OTHER)))
(is-rp (cons 'rp other)))))
:hints (("Goal"
:in-theory (e/d (rp-termp is-rp) ())))))|#

(defines unpack-booth-general-meta
  :flag-local nil
  :guard-hints (("Goal"
                 :in-theory (e/d (is-rp-implies-fc) ())))
  (define unpack-booth-general-meta ((term rp-termp))
    :returns (mv (result)
                 (dont-rw)
                 (changed))
    (b* (((when (or (atom term)
                    (quotep term)))
          (mv term t nil))
         ((when (eq (car term) 'falist))
          (mv term t nil))
         ((when (or (single-s-p term)
                    (single-c-p term)
                    (single-s-c-res-p term)
                    (and (binary-fnc-p term)
                         (pp-term-p term :strict t))))
          (b* (((mv res dont-rw) (unpack-booth-meta term)))
            (mv res dont-rw (not (rp-equal-cnt res term 3)))))

         ((when (equal (car term) 'if))
          (b* (((unless (is-if term))
                (progn$
                 (acl2::raise "Term function is if but does not satisfy is-if: ~p0 ~%" term)
                 (mv term t nil)))
               ((mv test test-dont-rw test-changed)
                (unpack-booth-general-meta (cadr term)))
               ((mv then then-dont-rw then-changed)
                (unpack-booth-general-meta (caddr term)))
               ((mv else else-dont-rw else-changed)
                (unpack-booth-general-meta (cadddr term))))
            (cond ((or test-changed then-changed else-changed)
                   (mv `(if ,test ,then ,else)
                       `(nil ,test-dont-rw ,then-dont-rw ,else-dont-rw)
                       t))
                  (t (mv term t nil)))))
         ((when (equal (car term) 'rp))
          (b* (((unless (is-rp term))
                (progn$
                 (acl2::raise "Term function is rp but does not satisfy is-rp: ~p0 ~%" term)
                 (mv term t nil)))
               ((mv res dont-rw changed)
                (unpack-booth-general-meta (caddr term))))
            (cond
             ;;((quotep res) (mv res t changed))
             (changed (mv `(rp ,(cadr term) ,res) `(nil t ,dont-rw) t))
             (t (mv term t nil)))))

         ((when (equal (car term) 'equals))
          (b* (((unless (is-equals term))
                (progn$
                 (acl2::raise "Term function is equals but does not satisfy is-equals: ~p0 ~%" term)
                 (mv term t nil)))
               ((mv res dont-rw changed)
                (unpack-booth-general-meta (cadr term)))
               ((mv res2 dont-rw2 changed2)
                (unpack-booth-general-meta (cadr term))))
            (cond
             ;;((quotep res) (mv res t changed))
             ((or changed changed2) (mv `(equals ,res ,res2) `(nil ,dont-rw ,dont-rw2) t))
             (t (mv term t nil)))))

         ((mv args args-dont-rw changed)
          (unpack-booth-general-meta-lst (cdr term)))
         ((unless changed)
          (mv term t nil)))
      (mv (cons-with-hint (car term) args term)
          `(nil . ,args-dont-rw)
          changed)))

  (define unpack-booth-general-meta-lst ((lst rp-term-listp))
    :returns (mv (result-lst )
                 (dont-rw-lst)
                 (changed))
    (if (atom lst)
        (mv nil nil nil)
      (b* (((mv this-term this-dont-tw this-changed)
            (unpack-booth-general-meta (car lst)))
           ((mv rest-lst rest-dont-tw rest-changed)
            (unpack-booth-general-meta-lst (cdr lst))))
        (if (or this-changed
                rest-changed)
            (mv (cons-with-hint this-term rest-lst lst)
                (cons this-dont-tw rest-dont-tw)
                t)
          (mv lst nil nil)))))

  ///

  (local
   (defthm is-rp-lemma
     (implies (is-rp term)
              (is-rp (list 'rp (cadr term) other)))
     :hints (("goal"
              :in-theory (e/d (is-rp) ())))))

  (defret-mutual rp-termp-of<fn>
    (defret rp-termp-<fn>
      (implies (rp-termp term)
               (rp-termp result))
      :fn unpack-booth-general-meta)
    (defret rp-term-listp-<fn>
      (implies (rp-term-listp lst)
               (rp-term-listp result-lst))
      :fn unpack-booth-general-meta-lst)
    :hints (("Goal"
             :expand ((:free (x) (rp-termp (cons 'if x)))
                      (:free (x) (rp-termp (cons 'rp x))))
             :in-theory (e/d ()
                             (FALIST-CONSISTENT
                              rp-termp))))))

(define unpack-booth-general-meta$ ((term rp-termp))
  ;;:enabled t
  (b* ((- (cw "Starting unpack-booth-general-meta$ ~%"))
       ((mv term dont-rw &)
        (unpack-booth-general-meta term)))
    (mv term dont-rw)))

(define unpack-booth-general-postprocessor ((term rp-termp)
                                            (rp-state)
                                            (state))
  ;;:enabled t
  :prepwork
  ((local
    (include-book "projects/rp-rewriter/proofs/rp-rw-lemmas" :dir :system)))
  :guard (and (VALID-RP-STATE-SYNTAXP RP-STATE))
  :guard-hints (("goal"
                 :in-theory (e/d () (nth-of-constant))))
  :returns (mv (res-term rp-termp
                         :hyp (and (rp-termp term)
                                   (valid-rp-state-syntaxp rp-state)))
               (res-rp-state (valid-rp-state-syntaxp res-rp-state)
                             :hyp (valid-rp-state-syntaxp rp-state)))
  (b* ((- (cw "Starting unpack-booth-general-postprocessor. (to disable run: (disable-postprocessor unpack-booth-general-postprocessor))~%"))
       ((mv term dont-rw changed)
        (time$
         (unpack-booth-general-meta term)
         :msg "-- unpack-booth-general-postprocessor took ~st seconds (real-time), or ~sc seconds ~
  (cpu-time), and ~sa bytes allocated.~%"
         :run-mintime 1/8)))
    (if (and changed
             (or (rp-meta-fnc-formula-checks state) ;; expected to return t
                 (acl2::raise "rp-meta-fnc-formula-checks didn't return t!`~%")))
        (rp-rw term dont-rw nil t (rp::rw-backchain-limit rp::rp-state) (expt 2 15) rp-state state)
      (mv term rp-state))))
