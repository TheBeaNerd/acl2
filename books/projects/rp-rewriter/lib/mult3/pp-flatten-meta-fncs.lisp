; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "fnc-defs")

(include-book "sum-merge-fncs")

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(local
 (in-theory (enable pp)))

(define pp-lists-p (x)
  :enabled t
  (if (atom x)
      (eq x nil)
    (and (consp (car x))
         (booleanp (caar x))
         (true-listp (cdar x))
         (pp-lists-p (cdr x)))))

(local
 (in-theory (disable lexorder)))

(local
 (set-induction-depth-limit 1))

(local
 (encapsulate
   nil

   (local
    (use-arith-5 t))

   (defthm floor-len-is-less-than-len
     (implies (and (natp len))
              (<= (floor len 2) len)))

   (defthm natp-len
     (natp (len x)))

   (defthmd dummy-arith-lemma-1
     (implies (NOT (CONSP LST))
              (equal (len lst) 0)))

   (defthmd dummy-arith-lemma-2
     (implies (and (<= SIZE (LEN LST))
                   (case-split (consp lst)))
              (equal (< (LEN (CDR LST)) (+ -1 SIZE)) nil)))))

(define pp-term-p (term
                   &key
                   (strict 'nil))
  :enabled t
  :measure (cons-count term)
  :hints (("goal"
           :in-theory (e/d (measure-lemmas) ())))
  (b* ((orig term)
       (term (ex-from-rp term)))
    (cond ((or (binary-and-p term)
               (binary-or-p term)
               (binary-xor-p term))
           (and (pp-term-p (cadr term) :strict strict)
                (pp-term-p (caddr term) :strict strict)))
          ((binary-?-p term)
           (and (pp-term-p (cadr term) :strict strict)
                (pp-term-p (caddr term) :strict strict)
                (pp-term-p (cadddr term) :strict strict)))
          ((or (binary-not-p term)
               (pp-p term))
           (and (pp-term-p (cadr term) :strict strict)))
          ((or (bit-of-p term)
               (bit-fix-p term)
               (equal term ''1)
               (equal term ''0))
           t)
          (t (and (has-bitp-rp orig)

                  (or (not strict)
                      (atom term)
                      (single-s-p term)
                      (single-c-p term)
                      (single-s-c-res-p term)))))))

(define pp-term-list-p (lst &key (strict 'nil))
  (if (atom lst)
      (equal lst nil)
    (and (pp-term-p (car lst) :strict strict)
         (pp-term-list-p (cdr lst) :strict strict))))

(define cut-list-by-half ((lst true-listp)
                          (size natp))
  :returns (mv (first rp-term-listp :hyp (and (rp-term-listp lst)
                                              (<= size (len lst))))
               (second rp-term-listp :hyp (and (rp-term-listp lst)
                                               (<= size (len lst)))))
  (if (zp size)
      (mv nil lst)
    (b* (((mv rest1 rest2)
          (cut-list-by-half (cdr lst) (1- size))))
      (mv (cons (car lst) rest1)
          rest2)))
  ///
  (defret true-listp-of-<fn>
    (and (true-listp first)
         (implies (true-listp lst)
                  (true-listp second))))

  (defret rp-term-list-listp-cut-list-by-half
    (implies (and (rp-term-list-listp lst)
                  (<= size (len lst)))
             (and (rp-term-list-listp first)
                  (rp-term-list-listp second)))
    :hints (("Goal"
             :do-not-induct t
             :induct (cut-list-by-half lst size)
             :in-theory (e/d (cut-list-by-half)
                             ()))))

  (defret rp-term-list-listp-cut-list-by-half-2
    (implies (and (rp-term-list-listp (strip-cdrs lst))
                  (<= size (len lst)))
             (and (rp-term-list-listp (strip-cdrs first))
                  (rp-term-list-listp (strip-cdrs second))))
    :hints (("Goal"
             :do-not-induct t
             :induct (cut-list-by-half lst size)
             :in-theory (e/d (cut-list-by-half
                              dummy-arith-lemma-1) ())))))

(local
 (defthm cut-list-by-half-returns-pp-lists
   (implies (and (pp-lists-p lst)
                 (< size (len lst)))
            (and (pp-lists-p (mv-nth 0 (cut-list-by-half lst size)))
                 (pp-lists-p (mv-nth 1 (cut-list-by-half lst size)))))
   :hints (("Goal"
            :in-theory (e/d (cut-list-by-half) ())))))

(local
 (in-theory (disable floor len)))

(in-theory (disable pp-list-order))

(encapsulate
  nil

  (local
   (encapsulate
     nil

     (local
      (use-arith-5 t))

     (defthm sort-measure-lemma1
       (IMPLIES
        (AND (<= 0 size)
             (integerp size)
             (<= size (len lst)))
        (equal (LEN (MV-NTH 1 (CUT-LIST-BY-HALF LST size)))
               (- (len lst) size)))
       :hints (("goal"
                :induct (CUT-LIST-BY-HALF LST size)
                :do-not-induct t
                :in-theory (e/d (len cut-list-by-half) ()))))

     (defthm sort-measure-lemma1-v2
       (IMPLIES
        (AND (<= 0 size)
             (integerp size)
             (<= size (len lst)))
        (equal (LEN (MV-NTH 0 (CUT-LIST-BY-HALF LST size)))
               size))
       :hints (("goal"
                :induct (CUT-LIST-BY-HALF LST size)
                :do-not-induct t
                :in-theory (e/d (len cut-list-by-half) ()))))

     (defthmd sort-measure-lemma2
       (implies (and (<= 2 (len lst)))
                (and (consp lst)
                     (consp (cdr lst))))
       :hints (("goal"
                :in-theory (e/d (len) ()))))

     (defthmd sort-measure-lemma2-v2-
       (equal  (<= 1 (len lst))
               (and (consp lst)))
       :hints (("goal"
                :in-theory (e/d (len) ()))))

     (defthm sort-measure-lemma3
       (implies (and (<= 2 (len lst)))
                (< (floor (len lst) 2) (len lst)))
       :hints (("goal"
                :in-theory (e/d (len) ()))))

     (defthm sort-measure-lemma4
       (implies (and (<= 2 (len lst)))
                (not (zp (floor (len lst) 2))))
       :hints (("goal"
                :in-theory (e/d (len) ()))))

     (defthm len-of-cut-list-by-half-second
       (implies (and (<= 2 (len lst))
                     (< size (len lst))
                     (not (zp size)))
                (equal (len (mv-nth 1
                                    (cut-list-by-half lst size)))
                       (+ (len lst) (- size))))
       :hints (("goal"
                :in-theory (e/d (cut-list-by-half len) ()))))

     (defthm len-of-cut-list-by-half-first
       (implies (and (<= 2 (len lst))
                     (< size (len lst))
                     (not (zp size)))
                (equal (len (mv-nth 0
                                    (cut-list-by-half lst size)))
                       size))
       :hints (("goal"
                :in-theory (e/d (cut-list-by-half len) ()))))

     (defthm guard-lemma1
       (implies (<= 2 (len lst))
                (<= 0 (+ (len lst) (- (floor (len lst) 2))))))

     (defthm o<-floor
       (implies (and (< 0 x)
                     (integerp x))
                (O< (FLOOR x 2) x))
       :hints (("Goal"
                :in-theory (e/d (o<) ()))))

     (defthm o<-floor-2
       (implies (and (< 1 x)
                     (integerp x))
                (O< (+ x (- (FLOOR x 2)))
                    x))
       :hints (("Goal"
                :in-theory (e/d (o<) ()))))

     (defthm floor-is-pos
       (implies (and (< 0 x)
                     (integerp x))
                (<= 0 (FLOOR x 2)))
       :hints (("Goal"
                :in-theory (e/d () ()))))

     (defthm floor-is-less-than
       (implies (and (< 0 x)
                     (integerp x))
                (<= (FLOOR x 2) x))
       :hints (("Goal"
                :in-theory (e/d () ()))))

     (defthm consp-cdr-implies
       (implies (consp (cdr lst))
                (< 1 (LEN LST)))
       :hints (("Goal"
                :in-theory (e/d (len) ()))))

     (defthm pos-len-implies
       (implies (< 0 (LEN LST))
                (consp lst))
       :hints (("Goal"
                :in-theory (e/d (len) ()))))

     (defthm less-than-2-of-len-is
       (equal (< (LEN LST) 2)
              (Not (and (consp lst)
                        (consp (cdr lst)))))
       :hints (("Goal"
                :in-theory (e/d (len) ()))))))

  (progn
    (define merge-sorted-and$-lists ((first true-listp)
                                     (second true-listp))
      :measure (+ (acl2-count first)
                  (acl2-count second))
      :returns (res rp-term-listp
                    :hyp (and (rp-term-listp first)
                              (rp-term-listp second))
                    :rule-classes (:rewrite :type-prescription))
      (cond
       ((atom first)
        second)
       ((atom second)
        first)
       (t
        (b* ((f (car first))
             (s (car second)))
          (cond ((equal f ''1)
                 (merge-sorted-and$-lists (cdr first)
                                          second))
                ((or (equal s ''1)
                     (rp-equal-cnt f s 1))
                 (merge-sorted-and$-lists first
                                          (cdr second)))
                ((lexorder2- f s)
                 (cons (car first) ;;hons
                       (merge-sorted-and$-lists (cdr first)
                                                second)))
                (t
                 (cons (car second) ;;hons
                       (merge-sorted-and$-lists first
                                                (cdr second))))))))
      ///
      (defret true-listp-of-<fn>
        (implies (and (true-listp first)
                      (true-listp second))
                 (true-listp res))))

    (define sort-and$-list ((lst true-listp)
                            (len natp))
      ;; :prepwork
      ;; ((local
      ;;   (use-arith-5 t)))
      :guard (equal (len lst) len)
      :measure (nfix (len lst))
      :hints (("Goal"
               :in-theory (e/d ()
                               (floor))))
      :verify-guards nil
      :returns (res rp-term-listp :hyp (rp-term-listp lst))
      (b* ((len (mbe :logic (len lst) ;; I don't want to bother adding len to
                     ;; correctness proofs.
                     :exec len)))
        (cond
         ((zp len)
          lst)
         ((= len 1)
          lst)
         ((= len 2)
          (b* ((a (car lst)) (b (cadr lst)))
            (cond
             ((equal a ''1) (cdr lst))
             ((or (equal b ''1)
                  (rp-equal-cnt b a 1))
              (list a))
             ((lexorder2- a b) lst)
             (t (list b a)))))
         (t (b* ((first-size (floor len 2))
                 (second-size (- len first-size))
                 ((mv first-half second-half)
                  (cut-list-by-half lst first-size))
                 (first-half (sort-and$-list first-half first-size))
                 (second-half (sort-and$-list second-half second-size)))
              (merge-sorted-and$-lists first-half second-half)))))
      ///

      (defret true-listp-of-<fn>
        (implies (true-listp lst)
                 (true-listp res)))

      (local
       (use-arith-5 t))
      (verify-guards sort-and$-list
        :hints (("Goal"
                 :in-theory (e/d () (floor len))))))

    (define and$-list-ordered-p (lst)
      (if (or (atom lst)
              (atom (cdr lst)))
          t

        (and
         (b* ((a (car lst)) (b (cadr lst)))
           (cond
            ((or (equal a ''1)
                 (equal b ''1)
                 (rp-equal-cnt b a 1))
             nil)
            ((lexorder2- a b) t)
            (t nil)))
         (and$-list-ordered-p (cdr lst)))))

    )

  (local
   (defthm pp-lists-p-implies-alistp
     (implies (pp-lists-p x)
              (alistp x))))

  (progn
    (define merge-sorted-pp-lists ((first pp-lists-p)
                                   (second pp-lists-p))
      :measure (+ (acl2-count first)
                  (acl2-count second))
      :returns (res pp-lists-p
                    :hyp (and (pp-lists-p first)
                              (pp-lists-p second))
                    :hints (("Goal"
                             :in-theory (e/d ()
                                             ((:REWRITE
                                               RP-TERM-LISTP-IS-TRUE-LISTP)
                                              (:DEFINITION TRUE-LISTP)
                                              (:REWRITE
                                               RP-TERMP-IMPLIES-SUBTERMS)
                                              (:DEFINITION RP-TERM-LISTP)
                                              (:REWRITE SORT-MEASURE-LEMMA2)
                                              (:DEFINITION QUOTEP)

                                              (:DEFINITION ACL2::APPLY$-BADGEP)
                                              (:LINEAR
                                               ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                                              (:DEFINITION RP-TERMP)
                                              (:DEFINITION LEN)
                                              (:DEFINITION SUBSETP-EQUAL)
                                              (:DEFINITION MEMBER-EQUAL)
                                              (:REWRITE DEFAULT-CDR)
                                              (:REWRITE
                                               RP-TERMP-IMPLIES-CDR-LISTP)
                                              (:REWRITE
                                               ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                                              (:REWRITE IS-IF-RP-TERMP)
                                              (:REWRITE DEFAULT-CAR)
                                              (:REWRITE RP-TERMP-CADR)
                                              (:REWRITE DEFAULT-+-2))))))
      :verify-guards nil
      (cond
       ((atom first) second)
       ((atom second) first)
       (t (b* ((sign1 (caar first))
               (term1 (cdar first))
               (sign2 (caar second))
               (term2 (cdar second)))
            (cond
             ((and (not (equal sign1 sign2))
                   (equal term1 term2))
              (merge-sorted-pp-lists (cdr first) (cdr second)))
             ((b* (((mv order &) (pp-list-order term1 term2 nil))) order)
              (acons sign1
                     term1
                     (merge-sorted-pp-lists (cdr first) second)))
             (t
              (acons sign2
                     term2
                     (merge-sorted-pp-lists first (cdr second))))))))
      ///

      (defthm rp-term-list-listp-merge-sorted-pp-lists
        (implies (and (rp-term-list-listp (strip-cdrs lst1))
                      (rp-term-list-listp (strip-cdrs lst2)))
                 (rp-term-list-listp
                  (strip-cdrs
                   (merge-sorted-pp-lists lst1 lst2))))
        :hints (("Goal"
                 :induct (merge-sorted-pp-lists lst1 lst2)
                 :in-theory (e/d (merge-sorted-pp-lists) ()))))

      (verify-guards merge-sorted-pp-lists
        :hints (("Goal"
                 :in-theory (e/d () (not
                                     (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                                     (:DEFINITION TRUE-LISTP)
                                     (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                                     (:DEFINITION RP-TERM-LISTP)
                                     (:DEFINITION QUOTEP)
                                     (:DEFINITION ACL2::APPLY$-BADGEP)
                                     (:REWRITE SORT-MEASURE-LEMMA2)
                                     (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)

                                     (:DEFINITION LEN)
                                     (:DEFINITION SUBSETP-EQUAL)
                                     (:DEFINITION RP-TERMP)
                                     (:DEFINITION MEMBER-EQUAL)
                                     (:REWRITE DEFAULT-CDR)
                                     (:REWRITE
                                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                                     (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                                     (:REWRITE IS-IF-RP-TERMP)
                                     (:DEFINITION ALISTP)
                                     (:REWRITE DEFAULT-CAR)))))))

    (define sort-pp-lists ((lst pp-lists-p)
                           (len natp))
      :guard (equal (len lst) len)
      :measure (nfix (len lst))
      :hints (("Goal"
               :in-theory (e/d (measure-lemmas
                                sort-measure-lemma2-v2-
                                sort-measure-lemma2)
                               (floor))))
      :verify-guards nil
      :returns (res pp-lists-p :hyp (pp-lists-p lst)
                    :hints (("Goal"
                             :in-theory (e/d () (floor)))))
      (b* ((len (mbe :logic (len lst) ;; I don't want to bother adding len to
                     ;; correctness proofs.
                     :exec len)))
        (cond
         ((zp len)
          lst)
         ((= len 1)
          lst
          #|(acons (caar lst)
          (sort-and$-list (cdar lst) (len (cdar lst)))

          nil)||#)
         ((= len 2)
          (b* ((f (car lst))
               (s (cadr lst))
               (sign1 (car f))
               (term1 (cdr f))
               (sign2 (car s))
               (term2 (cdr s)))
            (cond
             ((and (not (equal sign1 sign2))
                   (equal term1 term2))
              nil)

             ((b* (((mv order &) (pp-list-order term1 term2 nil))) order)
              lst)
             (t
              `(,(cadr lst)
                ,(car lst))))))
         (t (b* ((first-size (floor len 2))
                 (second-size (- len first-size))
                 ((mv first-half second-half)
                  (cut-list-by-half lst first-size))
                 (first-half (sort-pp-lists first-half first-size))
                 (second-half (sort-pp-lists second-half second-size)))
              (merge-sorted-pp-lists first-half  second-half)))))
      ///
      (local
       (defthm RP-TERM-LIST-LISTP-of-STRIP-CDRS-lemma
         (implies (RP-TERM-LIST-LISTP (STRIP-CDRS x))
                  (RP-TERM-LISTP (CDR (CADR x))))))

      (defthm rp-term-list-listp-sort-pp-lists
        (implies (rp-term-list-listp (strip-cdrs lst1))
                 (rp-term-list-listp (strip-cdrs
                                      (sort-pp-lists lst1 len))))
        :hints (("Goal"
                 ;;:induct (sort-pp-lists lst1 len)
                 ;;:do-not-induct t
                 :in-theory (e/d (RP-TERM-LIST-LISTP
                                  sort-pp-lists
                                  RP-TERM-LISTP)
                                 ()))))

      (verify-guards sort-pp-lists
        :hints (("Goal"
                 :in-theory (e/d () (floor len))))))))

#|(sort-pp-lists '((t b x y a)
                 (nil b x a)
                 (nil b y a)
                 (nil a)
                 (t b y)
                 (t b x)
                 (nil b x y)
                 (t a))
               8)||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; FLATTEN FUNCTIONS

(define and$-pp-lists-aux ((cur true-listp)
                           (lst2 pp-lists-p)
                           (acc pp-lists-p)
                           (sign booleanp))
  :returns (res-acc pp-lists-p :hyp (and (true-listp cur)
                                         (pp-lists-p lst2)
                                         (pp-lists-p acc)
                                         (booleanp sign))
                    :rule-classes :type-prescription)
  (if (atom lst2)
      acc
    (cons (cons (xor sign (caar lst2))
                (merge-sorted-and$-lists cur (cdar lst2))
;(append cur (cdar lst2)) ;; HERE!! replace with merge-sorted
                ;; and lists.
                )
          (and$-pp-lists-aux cur (cdr lst2) acc sign)))

  ///

  (defthm rp-term-list-listp-and$-pp-lists-aux
    (implies (and (rp-term-listp cur)
                  (rp-term-list-listp (strip-cdrs lst2))
                  (rp-term-list-listp (strip-cdrs acc)))
             (rp-term-list-listp (strip-cdrs (and$-pp-lists-aux cur lst2 acc
                                                                sign))))
    :hints (("Goal"
             :in-theory (e/d (and$-pp-lists-aux) ())))))

(define and$-pp-lists ((lst1 pp-lists-p)
                       (lst2 pp-lists-p)
                       (acc pp-lists-p)
                       (sign booleanp))
  :returns (res-acc pp-lists-p :hyp (and (pp-lists-p lst1)
                                         (pp-lists-p lst2)
                                         (pp-lists-p acc)
                                         (booleanp sign))
                    :rule-classes :type-prescription)
  (if (atom lst1)
      acc
    (b* ((acc (and$-pp-lists (cdr lst1) lst2 acc sign)))
      (and$-pp-lists-aux (cdar lst1) lst2 acc (xor sign (caar lst1)))))
  ///
  (defthm rp-term-list-listp-and$-pp-lists
    (implies (and (rp-term-list-listp (strip-cdrs lst1))
                  (rp-term-list-listp (strip-cdrs lst2))
                  (rp-term-list-listp (strip-cdrs acc)))
             (rp-term-list-listp (strip-cdrs (and$-pp-lists lst1 lst2 acc
                                                            sign))))
    :hints (("Goal"
             :in-theory (e/d (and$-pp-lists) ())))))

(local
 (defthm append-of-pp-list-p
   (implies (and (pp-lists-p x)
                 (pp-lists-p y))
            (pp-lists-p (append x y)))
   :rule-classes :type-prescription))

(local
 (in-theory (disable ex-from-rp)))

(local
 (defthmd pp-lists-p-implies-true-listp
   (implies (pp-lists-p x)
            (true-listp x))))

(local
 ;; auxilary function used only in the local lemmas for correctness proofs.
 (define apply-sign-to-pp-lists (lst sign)
   :returns (res pp-lists-p
                 :hyp (pp-lists-p lst))
   :verify-guards nil
   (if (atom lst)
       nil
     (acons (xor sign (caar lst))
            (cdar lst)
            (apply-sign-to-pp-lists (cdr lst) sign)))))

(encapsulate
  (((pp-lists-limit) => *))
  (local
   (defun pp-lists-limit ()
     2047))
  (defthm integerp-of-pp-lists-limit
    (integerp (pp-lists-limit))))

(define return-16000 ()
  16000)

(defattach pp-lists-limit return-16000)

(define pp-term-to-pp-lists ((term pp-term-p)
                             (sign booleanp)
                             &key
                             ((term-size-limit integerp) 'term-size-limit))
  :measure (cons-count term)
  :hints (("goal"
           :in-theory (e/d (measure-lemmas) ())))
  :returns (mv (result pp-lists-p
                       :hyp (booleanp sign)
                       :rule-classes :type-prescription)
               (too-large-p booleanp))
  :verify-guards nil
  ;;:ret-patbinder t
  (b* ((orig term)
       (term (ex-from-rp term)))

    (cond ((binary-and-p term)
           (b* ((x (cadr term))
                (y (caddr term))
                ((mv lst1 too-large1) (pp-term-to-pp-lists x nil))
                ((mv lst2 too-large2) (pp-term-to-pp-lists y nil))
                ((when (or too-large1 too-large2)) (mv `((,sign ,term)) t))

                (anded (and$-pp-lists lst1 lst2 nil sign))
                (len-added (len anded))
                ((when (> len-added term-size-limit)) (mv `((,sign ,term)) t))
                (anded (sort-pp-lists anded len-added)))
             (mv anded nil)))
          ((binary-or-p term)
           (b* ((x (cadr term))
                (y (caddr term))
                ((mv lst1 too-large1) (pp-term-to-pp-lists x sign))
                ((mv lst2 too-large2) (pp-term-to-pp-lists y sign))
                ((when (or too-large1 too-large2)) (mv `((,sign ,term)) t))

                (lst1+lst2 (merge-sorted-pp-lists lst1 lst2))

                (lst1&lst2 (and$-pp-lists lst1 lst2 nil (not sign)))
                (len-lst1&lst2 (len lst1&lst2))
                ((when (> len-lst1&lst2 term-size-limit)) (mv `((,sign ,term)) t))
                (lst1&lst2 (sort-pp-lists lst1&lst2 len-lst1&lst2))

                (merged (merge-sorted-pp-lists lst1+lst2 lst1&lst2))
                ((when (> (len merged) term-size-limit)) (mv `((,sign ,term)) t)))
             (mv merged nil)))
          ((binary-xor-p term)
           (b* ((x (cadr term))
                (y (caddr term))
                ((mv lst1 too-large1) (pp-term-to-pp-lists x sign))
                ((mv lst2 too-large2) (pp-term-to-pp-lists y sign))
                ((when (or too-large1 too-large2)) (mv `((,sign ,term)) t))

                (acc (merge-sorted-pp-lists lst1  lst2 ))
                (minus-x-and-y (and$-pp-lists lst1 lst2 nil (not sign)))
                (len-minus-x-and-y (len minus-x-and-y))
                (minus-x-and-y (sort-pp-lists minus-x-and-y len-minus-x-and-y))
                (merged (merge-sorted-pp-lists
                         acc
                         (merge-sorted-pp-lists minus-x-and-y minus-x-and-y)))
                ((when (> (len merged) term-size-limit)) (mv `((,sign ,term)) t)))
             (mv merged nil)))
          ((binary-?-p term)
           (b* ((test (cadr term))
                (x (caddr term))
                (y (cadddr term))
                ((mv test-lst too-large1) (pp-term-to-pp-lists test sign))
                ((mv x-lst too-large2) (pp-term-to-pp-lists x sign))
                ((mv y-lst too-large3) (pp-term-to-pp-lists y sign))
                ((when (or too-large1 too-large2 too-large3)) (mv `((,sign ,term)) t))

                (x-and-test (and$-pp-lists test-lst x-lst nil sign))
                (len-x-and-test (len x-and-test))
                ((when (> len-x-and-test term-size-limit)) (mv `((,sign ,term)) t))
                (x-and-test (sort-pp-lists x-and-test (len x-and-test)))

                (--y-and-test (and$-pp-lists test-lst y-lst nil (not sign)))
                (len--y-and-test (len --y-and-test))
                (--y-and-test (sort-pp-lists --y-and-test len--y-and-test))
                ((when (> len-x-and-test term-size-limit)) (mv `((,sign ,term)) t))
                (merged
                 (merge-sorted-pp-lists x-and-test
                                        (merge-sorted-pp-lists --y-and-test
                                                               y-lst)))
                ((when (> (len merged) term-size-limit)) (mv `((,sign ,term)) t)))
             (mv merged nil)))
          ((binary-not-p term)
           (b* ((x (cadr term))
                ((mv lst1 too-large1) (pp-term-to-pp-lists x (not sign)))
                (merged (merge-sorted-pp-lists (list (cons sign (list ''1))) lst1)))
             (mv merged too-large1)))
          ((pp-p term)
           (pp-term-to-pp-lists (cadr term) sign))
          ((bit-of-p term)
           (mv (list (cons sign (list term))) nil))
          ((bit-fix-p term)
           (mv (list (cons sign (list term))) nil))
          ((equal term ''1)
           (mv (list (cons sign (list term))) nil))
          ((equal term ''0)
           (mv nil nil))
          (t (if (has-bitp-rp orig)
                 (mv (list (cons sign (list orig))) nil)
               (progn$
                (cw "unexpected term ~p0 ~%" orig)
                (hard-error 'pp-term-to-pp-lists
                            "unexpected term ~p0 ~%"
                            (list (cons #\0 orig)))
                (mv `((,sign ,term)) nil))))))

  ///

  (defret rp-term-list-listp-pp-term-to-pp-lists
    (implies (and (rp-termp term)
                  (not too-large-p))
             (rp-term-list-listp (strip-cdrs result)))
    :fn pp-term-to-pp-lists
    :hints (("Goal"
             :in-theory (e/d (pp-term-to-pp-lists) ()))))

  (verify-guards pp-term-to-pp-lists-fn
    :hints (("goal"
             :in-theory (e/d () ())))))

;; (pp-term-to-pp-lists `(binary-not (binary-or (bit-of a 1) (bit-of b 1))) nil)

;; (pp-term-to-pp-lists `(binary-or (binary-and b (binary-or x y)) a) t)
;; =
;; (+ xb yb - xyb + a -axb -ayb - axyb)

;; (pp-term-to-pp-lists '(binary-or x y) t)

;; (pp-term-to-pp-lists `(binary-or (binary-and b (binary-or x y)) (binary-not a)) nil)
;; =
;; -xby by bx 1 -a axb -xb aby -by -axby xby

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; CONVERT PP-LISTS TO TERMS

;; (define pp-lists-to-term-and-list ((cur true-listp))
;;   :returns (res rp-term-listp
;;                 :hyp
;;   (cond ((atom cur)
;;          nil)
;;         (t
;;          (cons (car cur)
;;                (pp-lists-to-term-and-list (cdr cur))))))

;; (define ppf-2 ()
;;   ())

;; (define ppf-1 ()
;;   ())

;; (define ppf-3 ()
;;   ())

;; (define ppf-4 ()
;;   ())

;; (define ppf-5+ ()
;;   ())

;; (profile 'ppf-2)
;; (profile 'ppf-1)
;; (profile 'ppf-3)
;; (profile 'ppf-4)
;; (profile 'ppf-5+)

(define pp-lists-to-term-pp-lst ((lst pp-lists-p))
  (cond ((atom lst)
         nil)
        (t
         (b* ((cur (cdar lst))
              (cur (cond ((atom cur)  ''1)
                         ((atom (cdr cur))
                          (cond ((equal (car cur) ''1)
                                 ''1)
                                #|((or (bit-of-p (car cur))
                                (has-bitp-rp (car cur)))
                                (car cur))|#
                                (t (create-and-list-instance (list (car cur))))))
                         ((atom (cddr cur)) (create-and-list-instance cur))
                         (t (create-and-list-instance cur))))
              )
           (if (caar lst)
               (cons `(-- ,cur)
                     (pp-lists-to-term-pp-lst (cdr lst)))
             (cons cur
                   (pp-lists-to-term-pp-lst (cdr lst)))))))
  ///
  (defthm rp-termp-of-pp-lists-to-term-pp-lst
    (implies (rp-term-list-listp (strip-cdrs lst))
             (rp-term-listp (pp-lists-to-term-pp-lst lst)))
    :hints (("Goal"
             :in-theory (e/d (pp-lists-to-term-pp-lst) ())))))

(local (include-book "ordinals/ordinals-without-arithmetic" :dir :system))

(define pp-remove-extraneous-sc (term)
  :returns (res-term pp-term-p :hyp (pp-term-p term)
                     :hints (("Goal"
                              :do-not-induct t
                              :induct (pp-remove-extraneous-sc term)
                              :expand ((:free (x y) (pp-term-p (cons x y)))
                                       (:free (x y) (BINARY-AND-P (cons x y)))
                                       (:free (x y) (BINARY-OR-P (cons x y)))
                                       (:free (x y) (BINARY-XOR-P (cons x y)))
                                       (:free (x y) (BINARY-?-p (cons x y)))
                                       (:free (x y) (PP-P (cons x y)))
                                       (:free (x y) (BINARY-NOT-P (cons x y)))
                                       (:free (x y) (BIT-OF-P (cons x y))))
                              :in-theory (e/d (ex-from-rp is-rp) ()))))
  :measure (cons-count term)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas) ())))
  (let* ((term- (ex-from-rp term)))
    (cond ((or (atom term)
               (quotep term))
           term)
          ((bit-of-p term-)
           `(bit-of ,(ex-from-rp (cadr term-))
                    ,(ex-from-rp (caddr term-))))
          ((or (BINARY-AND-p term-)
               (BINARY-OR-p term-)
               (BINARY-XOR-p term-))
           (cons-with-hint
            (car term-)
            (cons-with-hint (pp-remove-extraneous-sc (cadr term-))
                            (cons-with-hint (pp-remove-extraneous-sc (caddr term-))
                                            nil
                                            (cddr term-))
                            (cdr term-))
            term-))

          ((or (BINARY-NOT-p term-)
               (pp-p term-))
           (cons-with-hint (car term-)
                           (cons-with-hint (pp-remove-extraneous-sc (cadr
                                                                     term-))
                                           nil
                                           (cdr term-))
                           term-))

          ((BINARY-?-p term-)
           (cons-with-hint
            (car term-)
            (cons-with-hint
             (pp-remove-extraneous-sc (cadr term-))
             (cons-with-hint
              (pp-remove-extraneous-sc (caddr term-))
              (cons-with-hint
               (pp-remove-extraneous-sc (cadddr term-))
               nil
               (cdddr term-))
              (cddr term-))
             (cdr term-))
            term-))
          (t term)))
  ///
  (defret rp-termp-of-<fn>
    (implies (rp-termp term)
             (rp-termp res-term))
    :fn pp-remove-extraneous-sc
    :hints (("Goal"
             :in-theory (e/d (pp-remove-extraneous-sc) ())))))

(define pp-remove-extraneous-sc-lst (lst)
  :returns (res-lst pp-term-list-p
                    :hyp (pp-term-list-p lst)
                    :hints (("Goal"
                             :in-theory (e/d (pp-term-list-p) ()))))
  (if (atom lst)
      nil
    (cons (pp-remove-extraneous-sc (car lst))
          (pp-remove-extraneous-sc-lst (cdr lst))))
  ///
  (defret rp-term-listp-of-<fn>
    (implies (rp-term-listp lst)
             (rp-term-listp  res-lst))
    :hints (("Goal"
             :in-theory (e/d () ())))))

(define pp-flatten ((term pp-term-p)
                    (sign booleanp)
                    &key
                    (disabled 'nil))
  :returns pp-lst
  (b* ((term (pp-remove-extraneous-sc term)))
    (cond (disabled
           (list (if sign `(-- ,term) term)))
          ((and (case-match term
                  (('binary-and ('bit-of & &) ('bit-of & &)) t))
                (not (rp-equal (cadr term) (caddr term))))
           (b* ((cur-single
                 (if (lexorder2- (cadr term) (caddr term))
                     (if sign
                         `(-- ,(create-and-list-instance (cdr term)))
                       (create-and-list-instance (cdr term)))
                   (if sign
                       `(-- ,(create-and-list-instance (list (caddr term) (cadr term))))
                     (create-and-list-instance (list (caddr term) (cadr term)))))))
             (list cur-single)))
          (t (b* ((term-size-limit (pp-lists-limit))
                  ((mv pp-lists too-large) (pp-term-to-pp-lists term sign))
                  ((when too-large)
                   (progn$ (cwe "Warning: pp-flatten got a term that grows too large: ~p0 ~%"
                                term)
                           (list (if sign `(-- ,term) term))))
                  (pp-lst (pp-lists-to-term-pp-lst pp-lists))
                  #|(result (If pp-lists (cons 'list result) ''nil))||#
                  )
               pp-lst))))
  ///

  (defret rp-term-listp-of-pp-flatten
    (implies (rp-termp term)
             (rp-term-listp pp-lst))
    :fn pp-flatten
    :hints (("Goal"
             :in-theory (e/d (pp-flatten) ()))))

  (profile 'pp-flatten-fn))

(define pp-flatten-memoized ((term pp-term-p)
                             (sign booleanp))
  :enabled t
  (pp-flatten term sign :disabled nil)
  ///

  (memoize 'pp-flatten-memoized
           :aokp t
           ;;:condition '(not disabled)
           ))

(acl2::defsection sort-sum-meta

  (define valid-single-bitp (a)
    :inline t
    (b* (((when (case-match a (('rp ''bitp &) t)))
          t)
         (a (ex-from-rp a)))
      (case-match a (('bit-of & &) t) (''1 t)))
    ///
    (defthm valid-single-bitp-implies
      (implies (valid-single-bitp a)
               (b* (((when (case-match a (('rp ''bitp &) t)))
                     t)
                    (a (ex-from-rp a)))
                 (case-match a (('bit-of & &) t) (''1 t))))
      :rule-classes :forward-chaining))

  (define sort-sum-meta-aux-aux (cur)
    :returns (mv valid pp-list-entry)
    :verify-guards nil
    (b* (((when (case-match cur (('rp ''bitp x) (atom x))))
          (mv t (list nil cur)))
         (cur (ex-from-rp cur)))
      (case-match cur
        (('binary-and a b)
         (b* (((unless (and (valid-single-bitp a)
                            (valid-single-bitp b)))
               (mv nil nil)))
           (mv t
               (cons nil (pp-remove-extraneous-sc-lst (sort-and$-list (cdr cur) 2))))))
        (('bit-of & &)
         (mv t (list nil (pp-remove-extraneous-sc cur))))
        (''1
         (mv t (list nil cur)))
        (''0
         (mv t nil))
        (&
         (mv nil nil))))
    ///
    (local
     (defthm lemma1
       (implies (consp x)
                (equal (len x) (1+ (len (cdr x)))))))

    (defret rp-term-listp-of-<fn>
      (implies (and (rp-termp cur)
                    valid
                    (consp PP-LIST-ENTRY))
               (and (rp-term-listp (cdr PP-LIST-ENTRY))))
      :fn sort-sum-meta-aux-aux
      :hints (("Goal"
               :in-theory (e/d (sort-sum-meta-aux-aux)
                               ((:DEFINITION FALIST-CONSISTENT)

                                (:DEFINITION FALIST-CONSISTENT-AUX)
                                ;;                            (:REWRITE ACL2::O-P-O-INFP-CAR)
                                (:REWRITE IS-IF-RP-TERMP)
                                (:TYPE-PRESCRIPTION RP-TERMP)
                                (:TYPE-PRESCRIPTION O<)
                                (:REWRITE DEFAULT-CDR)
                                #|(:FORWARD-CHAINING
                                ACL2::|a <= b & b <= c  =>  a <= c|)|#
                                #|(:FORWARD-CHAINING
                                ACL2::|a <= b & b < c  =>  a < c|)|#)))))

    (verify-guards sort-sum-meta-aux-aux
      :hints (("Goal"
               :in-theory (e/d () ((:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                                   (:DEFINITION RP-TERMP)
                                   (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                                   (:DEFINITION RP-TERM-LISTP)
                                   (:DEFINITION QUOTEP)
                                   (:DEFINITION ACL2::APPLY$-BADGEP)
                                   (:DEFINITION SUBSETP-EQUAL)
                                   (:DEFINITION MEMBER-EQUAL)
                                   (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                                   (:REWRITE DEFAULT-CDR)
                                   ;;                                   (:REWRITE ACL2::SUBSETP-REFLEXIVE-LEMMA)
                                   (:REWRITE
                                    ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                                   (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2))))))

    (defret pp-list-entry-p-of-<fn>
      (implies (and valid)
               (and (true-listp (cdr pp-list-entry))
                    (booleanp (car pp-list-entry))
                    (true-listp pp-list-entry)))
      :hints (("Goal"
               :in-theory (e/d ()
                               ((:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                                (:DEFINITION RP-TERM-LISTP)
                                (:DEFINITION FALIST-CONSISTENT)
                                (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                                (:REWRITE DEFAULT-CDR)
                                (:REWRITE IS-IF-RP-TERMP)
                                (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                                (:REWRITE DEFAULT-CAR)
                                (:REWRITE RP-TERMP-CADDR)
                                (:TYPE-PRESCRIPTION RP-TERMP)
                                (:TYPE-PRESCRIPTION O<)
                                (:TYPE-PRESCRIPTION TRUE-LISTP)
                                (:TYPE-PRESCRIPTION O-P)
                                (:DEFINITION NOT)
                                ;; (:TYPE-PRESCRIPTION SV::SVEXLIST-P)
                                ;; (:TYPE-PRESCRIPTION SV::SVEX-ENV-P)
                                ;; (:TYPE-PRESCRIPTION SV::SVEX-ALIST-P)
                                (:DEFINITION RP-TERMP)))))))

  (define sort-sum-meta-aux (term)
    :returns (mv valid pp-lists)
    :measure (cons-count term)
    :hints (("Goal"
             :in-theory (e/d (measure-lemmas)
                             ())))
    (b* ((term-orig term)
         (term (ex-from-rp term)))
      (case-match term
        (('binary-sum cur rest)
         (b* (((mv rest-valid rest)
               (sort-sum-meta-aux rest))
              ((unless rest-valid)
               (mv nil nil))
              ((mv cur-valid cur)
               (sort-sum-meta-aux-aux cur))
              ((unless cur-valid)
               (mv nil nil)))
           (if (consp cur)
               (mv t (cons cur rest))
             (mv t rest))))
        (& (b* (((mv cur-valid cur)
                 (sort-sum-meta-aux-aux term-orig))
                ((unless cur-valid)
                 (mv nil nil)))
             (if (consp cur)
                 (mv t (list cur))
               (mv t nil))))))
    ///

    (defret rp-term-list-listp-strip-cdrs-sort-sum-meta-aux
      (implies (rp-termp term)
               (rp-term-list-listp (strip-cdrs pp-lists)))

      :hints (("goal"
               :in-theory (e/d (sort-sum-meta-aux)
                               ((:definition acl2::apply$-badgep)
                                (:linear acl2::apply$-badgep-properties . 1)
                                (:rewrite rp-termp-implies-cdr-listp)
                                (:definition member-equal)
                                (:rewrite rp-term-listp-is-true-listp)
                                (:linear acl2::apply$-badgep-properties . 2)
                                (:definition true-listp)
                                (:rewrite is-if-rp-termp)
                                ;;                            (:rewrite acl2::o-p-o-infp-car)
                                (:rewrite is-rp-pseudo-termp)
                                (:rewrite atom-rp-termp-is-symbolp)
                                falist-consistent
                                (:definition subsetp-equal))))))

    (acl2::defret pp-lists-p-of-<fn>
      (implies valid
               (pp-lists-p pp-lists))))

  (define sort-sum-meta-aux2 (term)
    :returns (mv valid pp-lists)
    :verify-guards nil
    :measure (cons-count term)
    :hints (("Goal"
             :in-theory (e/d (measure-lemmas)
                             ())))
    (b* ((?term-orig term)
         (term (ex-from-rp term)))
      (case-match term
        (('binary-sum cur rest)
         (b* (((unless (pp-term-p cur))
               (mv nil nil))
              (term-size-limit (pp-lists-limit))
              ((when (or (include-fnc cur 's)
                         (include-fnc cur 'c)
                         (include-fnc cur 's-c-res)))
               (mv nil nil))
              (cur (pp-remove-extraneous-sc cur))
              ((mv pp-lists1 too-large) (pp-term-to-pp-lists cur nil))
              ((when too-large)
               (progn$
                (cwe "Warning: sort-sum-meta-aux2 got a term that grows too large: ~p0 ~%"
                     cur)
                (mv nil nil)))
              ((mv rest-valid pp-lists2)
               (sort-sum-meta-aux2 rest))
              ((unless rest-valid)
               (mv nil nil)))
           (mv t (merge-sorted-pp-lists pp-lists1 pp-lists2))))
        (& (b* (((unless (pp-term-p term-orig))
                 (mv nil nil))
                ((when (or (include-fnc term 's)
                           (include-fnc term 'c)
                           (include-fnc term 's-c-res)))
                 (mv nil nil))
                (term-orig (pp-remove-extraneous-sc term-orig))
                (term-size-limit (pp-lists-limit))
                ((mv res too-large) (pp-term-to-pp-lists term-orig nil))
                ((when too-large)
                 (progn$
                  (cwe "Warning: sort-sum-meta-aux2 got a term that grows too large: ~p0 ~%"
                       term-orig)
                  (mv nil nil))))
             (mv t res)))))
    ///

    (defthm rp-term-list-listp-strip-cdrs-sort-sum-meta-aux2
      (implies (rp-termp term)
               (rp-term-list-listp (strip-cdrs (mv-nth 1 (sort-sum-meta-aux2
                                                          term)))))
      :hints (("goal"
               :in-theory (e/d (sort-sum-meta-aux2)
                               ((:definition acl2::apply$-badgep)
                                (:linear acl2::apply$-badgep-properties . 1)
                                (:rewrite rp-termp-implies-cdr-listp)
                                (:definition member-equal)
                                (:rewrite rp-term-listp-is-true-listp)
                                (:linear acl2::apply$-badgep-properties . 2)
                                (:definition true-listp)
                                (:rewrite is-if-rp-termp)
                                ;;(:rewrite acl2::o-p-o-infp-car)
                                (:rewrite is-rp-pseudo-termp)
                                (:rewrite atom-rp-termp-is-symbolp)
                                falist-consistent
                                (:definition subsetp-equal))))))

    (acl2::defret pp-lists-p-of-<fn>
      (implies valid
               (pp-lists-p pp-lists)))
    (verify-guards sort-sum-meta-aux2)) 

  (define sort-sum-meta (term)
    :returns (mv result
                 (dont-rw dont-rw-syntaxp))
    (case-match term
      (('sort-sum x)
       (b* (((mv valid pp-lists)
             (sort-sum-meta-aux2 x))
            ((unless valid)
             (progn$ #|(cwe "Warning: sort-sum-meta got an unexpected term ~p0 ~%"
                         term)|#
                     ;;(hard-error 'sort-sum-meta "Read above.." nil)
                     (mv `(binary-sum ,x '0) '(nil t t))))
            (pp-lists (sort-pp-lists pp-lists (len pp-lists)))
            (pp-lst (pp-lists-to-term-pp-lst pp-lists))
            (result (If pp-lst
                        `(sum-list
                          ,(create-list-instance pp-lst)
                          ;;(list (list . ,result) 'nil 'nil 'nil)
                          )
                        ''0)))
         (mv result t)))
      (&
       (progn$ (cw "sort-sum-meta got an unexpected term ~p0 ~%"
                   term)
               (hard-error 'sort-sum-meta "" nil)
               (mv term t))))
    ///
    (defthm rp-termp-of-sort-sum-meta.result
      (implies (rp-termp term)
               (b* (((mv ?result ?dont-rw)
                     (sort-sum-meta term)))
                 (rp-termp result)))
      :rule-classes :rewrite
      :hints (("Goal"
               :in-theory (e/d (sort-sum-meta)
                               ()))))))
