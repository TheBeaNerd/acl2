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
;
; Original author: Mertcan Temel <mert.temel@intel.com>

(in-package "RP")
(include-book "svl-spec")

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

#|(local
(include-book "projects/rp-rewriter/proofs/rp-rw-lemmas" :dir :system))|#

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  :disabled t))

(local
 (include-book "pp-flatten-meta-correct"))

(local
 (include-book "sum-merge-fncs-correct"))

(local
 (include-book "lemmas"))
(local
 (include-book "lemmas-2"))

#|
(BINARY-* (ACL2::RP 'INTEGERP
(SVL::4VEC-CONCAT$ '23
(SVL::BITS (ACL2::RP 'INTEGERP SRC1)
'0
'23)
'1))
(ACL2::RP 'INTEGERP
(SVL::4VEC-CONCAT$ '23
(SVL::BITS (ACL2::RP 'INTEGERP SRC2)
'0
'23)
'1)))

|#

(local
 (defthm is-equals-of-others
   (implies (not (equal (car term) 'equals))
            (not (is-equals term )))
   :hints (("Goal"
            :in-theory (e/d (is-equals) ())))))

(define check-context-for-integerp (term context)
  (if (atom context)
      nil
    (or (b* ((cur (ex-from-rp (car context))))
          (case-match cur
            (('integerp x)
             (rp-equal-cnt term x 1))))
        (check-context-for-integerp term (cdr context)))))

(define logsize ((x integerp))
  :prepwork ((local
              (use-arith-5 t))
             (local
              (in-theory (e/d* ()
                               (rw-dir1
                                +-IS-SUM
                                FLOOR2-IF-F2)))))
  (if (or (equal x 0)
          (equal x -1)
          (not (integerp x)))
      0
    (1+ (logsize (acl2::logcdr x)))))

(define calculate-vec-size ((x rp-termp)
                            (context rp-term-listp))
  :returns (mv (size integerp)
               (integerp booleanp))
  :verify-guards :after-returns
  :measure (cons-count x)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas
                            ACL2::DEFSORT-O<-OF-NATURALS)
                           (RW->-TO-GT
                            (:REWRITE LT-TO-GT)
                            (:REWRITE RW-<-TO-LTE)))))
  (b* ((x-orig x)
       (x (ex-from-rp x)))
    (case-match x
      (('svl::bits vec ('quote start) ('quote size))
       (b* (((unless (and (natp start)
                          (natp size)))
             (mv -1 nil))
            ((mv & integerp)
             (calculate-vec-size vec context)))
         (mv size integerp)))
      (('svl::4vec-concat$ ('quote size) vec1 vec2)
       (b* (((mv & integerp1)
             (calculate-vec-size vec1 context))
            ((mv size2 integerp2)
             (calculate-vec-size vec2 context))
            ((unless (and integerp1
                          integerp2
                          (not (equal size2 -1))
                          (natp size)))
             (mv -1 nil)))
         (mv (+ size size2) t)))
      (('quote x)
       (if (natp x)
           (mv (logsize x) t)
         (mv -1 nil)))
      (&
       (cond ((atom x)
              (mv -1 (check-context-for-integerp x context)))
             ((or* (logbit-p x)
                   (binary-fnc-p x)
                   (has-bitp-rp x-orig))
              (mv 1 t))
             (t
              (mv -1 nil)))))))

#|(calculate-vec-size '(ACL2::RP 'INTEGERP
(SVL::4VEC-CONCAT$ '23
(SVL::BITS (ACL2::RP 'INTEGERP SRC1)
'0
'23)
'1))
'((integerp src1)))|#

(define binary-*-p (term)
  (case-match term
    (('binary-* & &)
     t))
  ///
  (defthm binary-*-p-implies
    (implies (binary-*-p term)
             (case-match term
               (('binary-* & &)
                t)))
    :rule-classes :forward-chaining))

(define binary-+-p (term)
  (case-match term
    (('binary-+ & &)
     t))
  ///
  (defthm binary-+-p-implies
    (implies (binary-+-p term)
             (case-match term
               (('binary-+ & &)
                t)))
    :rule-classes :forward-chaining))

(define binary-subtract-p (term)
  (case-match term
    (('binary-+ & ('unary-- &))
     t))
  ///
  (defthm binary-subtract-p-implies
    (implies (binary-subtract-p term)
             (case-match term
               (('binary-+ & ('unary-- &))
                t)))
    :rule-classes :forward-chaining))

(create-case-match-macro 4vec-<-pattern
                         ('sv::4vec-< x y))

(define */+-to-mult-spec-meta ((term rp-termp)
                               (context rp-term-listp))
  (cond
   ((binary-*-p term) ;;('binary-* x y)
    (b* ((x (cadr term))
         (y (caddr term))
         ((mv size-x integerp-x)
          (calculate-vec-size x context))
         ((mv size-y integerp-y)
          (calculate-vec-size y context))
         ((unless (and integerp-x
                       (not (equal size-x -1))
                       (not (equal size-y -1))
                       integerp-y))
          (mv term nil)))
      (mv `(svl-mult-final-spec ,x ,y ',(+ size-x size-y))
          `(nil t t t))))
   ((binary-subtract-p term) ;;('binary-+ x ('unary-- y))
    (b* ((x (cadr term))
         (y (cadr (caddr term)))
         ((mv size-x integerp-x)
          (calculate-vec-size x context))
         ((mv size-y integerp-y)
          (calculate-vec-size y context))
         ((unless (and integerp-x
                       integerp-y
                       (not (equal size-x -1))
                       (not (equal size-y -1))))
          (mv term nil)))
      (mv `(2vec-subtract ,x ,y ',(max size-x size-y) '1)
          `(nil t t t t))))
   ((and (binary-+-p term)
         (binary-+-p (caddr term)))
    (b* ((x (cadr term))
         (y (cadr (caddr term)))
         (z (caddr (caddr term)))
         ((mv size-x integerp-x)
          (calculate-vec-size x context))
         ((mv size-y integerp-y)
          (calculate-vec-size y context))
         ((mv size-z integerp-z)
          (calculate-vec-size z context))
         ((unless (and integerp-x
                       integerp-y
                       integerp-z
                       (equal size-z 1)
                       (not (equal size-x -1))
                       (not (equal size-y -1))))
          (mv term nil)))
      (mv `(2vec-adder ,x ,y ,z ',(1+ (max size-x size-y)))
          `(nil t t t t))))
   ((binary-+-p term)
    (b* ((x (cadr term))
         (y (caddr term))
         ((mv size-x integerp-x)
          (calculate-vec-size x context))
         ((mv size-y integerp-y)
          (calculate-vec-size y context))
         ((unless (and integerp-x
                       integerp-y
                       (not (equal size-x -1))
                       (not (equal size-x 1))
                       (not (equal size-y -1))
                       (not (equal size-y 1))))
          (mv term nil)))
      (mv `(2vec-adder ,x ,y '0 ',(1+ (max size-x size-y)))
          `(nil t t t t))))

   ((4vec-<-pattern-p term)
    (4vec-<-pattern-body
     term
     (b* (((mv size-x integerp-x)
           (calculate-vec-size x context))
          ((mv size-y integerp-y)
           (calculate-vec-size y context))
          ((unless (and integerp-x
                        integerp-y
                        (not (equal size-x -1))
                        (not (equal size-y -1))))
           (mv term nil)))
       (mv `(unary-- (svl::bits (2vec-subtract ,x ,y ',(max size-x size-y) '1)
                                ',(max size-x size-y)
                                '1))
           `(unary-- (svl::bits (2vec-subtract t t t t)
                                t
                                t))))))

   (t (mv term nil))))

#|(*-to-mult-spec-meta  '(BINARY-* (ACL2::RP 'INTEGERP
(SVL::4VEC-CONCAT$ '23
(SVL::BITS (ACL2::RP 'INTEGERP SRC1)
'0
'23)
'1))
(ACL2::RP 'INTEGERP
(SVL::4VEC-CONCAT$ '23
(SVL::BITS (ACL2::RP 'INTEGERP SRC2)
'0
'23)
'1)))
'((integerp src1)
(integerp src2)))|#

(encapsulate
  nil
  (local
   (in-theory
    (e/d* () (+-IS-SUM
              REWRITING-POSITIVE-LTE-GTE-GT-LT
              rw-dir1
              C-SPEC-IS-F2
              S-SPEC-IS-M2
              S-C-SPEC-IS-LIST-M2-F2
              SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
              SVL-SUM-PPS-BYCOL-BYBIT-OPENER))))
  (with-output
    :off :all
    :gag-mode nil
    (rp::def-formula-checks */+-to-mult/adder-spec-meta-fchecks
      (svl::bits svl::4vec-concat$ *
                 2vec-adder
                 2VEC-SUBTRACT
                 unary--
                 sv::4vec-<
                 SVL-MULT-FINAL-SPEC
                 binary-or binary-xor binary-and binary-?
                 logbit$inline binary-not))))

(with-output
  :off :all
  :gag-mode nil
  (local
   (progn
     (in-theory (disable logbit))
     (rp::create-regular-eval-lemma svl::4VEC-CONCAT$ 3
                                    */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma sv::4vec-< 2
                                    */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma SVL-MULT-FINAL-SPEC 3
                                    */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma 2VEC-SUBTRACT 4
                                    */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma unary-- 1
                                    */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma 2vec-adder 4  */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma svl::Bits 3  */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma binary-* 2  */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma binary-+ 2  */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma integerp 1  */+-to-mult/adder-spec-meta-fchecks)

     (rp::create-regular-eval-lemma binary-or 2
                                    */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma binary-and 2
                                    */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma binary-xor 2
                                    */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma logbit$inline 2
                                    */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma binary-not 1
                                    */+-to-mult/adder-spec-meta-fchecks)
     (rp::create-regular-eval-lemma binary-? 3  */+-to-mult/adder-spec-meta-fchecks)
     )))

(local
 (defthm CHECK-CONTEXT-FOR-INTEGERP-correct
   (implies (and (eval-and-all context a)
                 (rp-evl-meta-extract-global-facts)
                 (*/+-to-mult/adder-spec-meta-fchecks state)
                 (check-context-for-integerp term context))
            (integerp (rp-evlt term a)))
   :hints (("Subgoal *1/2"
            :use ((:instance rp-evlt-of-rp-equal
                             (term1 term)
                             (term2 (CADR (EX-FROM-RP (CAR CONTEXT)))))))
           ("Goal"
            :in-theory (e/d* (check-context-for-integerp
                              RP-EVLT-OF-EX-FROM-RP-REVERSE
                              regular-eval-lemmas
                              regular-eval-lemmas-with-ex-from-rp)
                             (rp-evlt-of-rp-equal
                              rp-evlt-of-ex-from-rp ))))))

(local
 (defthm rp-evlt-when-quoted
   (implies (and (quotep term)
                 (consp (cdr term)))
            (equal (rp-evlt term a)
                   (cadr term)))))

(defthm unsigned-byte-p-of-logsize
  (implies (natp x)
           (unsigned-byte-p (logsize x)
                            x))
  :hints (("Goal"
           :in-theory (e/d* (unsigned-byte-p-redef-to-recursive
                             ;;bitops::ihsext-inductions
                             ;;bitops::ihsext-recursive-redefs
                             logsize
                             )
                            (rw-dir1
                             LOGCOUNT
                             (:induction UNSIGNED-BYTE-P-RECURSIVE)
                             acl2::logcdr
                             acl2::logcar
                             +-IS-SUM)))))

(local
 (defthm unsigned-byte-p-of-logapp2
   (implies (and (natp size)
                 (natp size2)
                 ;;(<= size2 size)
                 (integerp y)
                 (integerp x))
            (equal (unsigned-byte-p (+ size2 size) (logapp size2 x y))
                   (unsigned-byte-p size y)))
   :hints (("Goal"
            :do-not-induct t
            :induct (unsigned-byte-p-recursive size2 x)
            :expand ((LOGAPP SIZE2 0 Y)
                     (UNSIGNED-BYTE-P-RECURSIVE SIZE
                                                (ACL2::LOGCONS 0 (LOGAPP (+ -1 SIZE2) 0 Y))))
            :in-theory (e/d* (SVL::4VEC-CONCAT$
                              BITOPS::LOGCDR-OF-LOGCONS
                              unsigned-byte-p-redef-to-recursive
                              acl2::logapp**
                              SV::4VEC-CONCAT
                              ;;bitops::ihsext-inductions
                              bitops::ihsext-recursive-redefs
                              natp
                              SV::4VEC->UPPER
                              SV::4VEC->lower
                              SV::4VEC)
                             (+-IS-SUM
                              ACL2::LOGCONS$INLINE
                              MOD2-IS-M2
                              acl2::logcdr
                              FLOOR
                              FLOOR2-IF-F2
                              unsigned-byte-p
                              LOGAPP
                              ACL2::LOGHEAD$INLINE
                              rw-dir1))))))

(local
 (defthm unsigned-byte-p-of-4VEC-CONCAT$
   (implies (and (natp size)
                 (natp size2)
                 (integerp x)
                 (integerp y)
                 (<= size2 size))
            (equal (unsigned-byte-p size (SVL::4VEC-CONCAT$ size2 x y))
                   (unsigned-byte-p (- size size2) y)))
   :hints (("Goal"
            :use ((:instance unsigned-byte-p-of-logapp2
                             (y y)
                             (size (- size size2))
                             (size2 size2)))
            :do-not-induct t
            :in-theory (e/d* (SVL::4VEC-CONCAT$
                              unsigned-byte-p-redef-to-recursive

                              SV::4VEC-CONCAT
                              bitops::ihsext-inductions
                              bitops::ihsext-recursive-redefs
                              natp
                              SV::4VEC->UPPER
                              SV::4VEC->lower
                              SV::4VEC)
                             (+-IS-SUM
                              unsigned-byte-p-of-logapp2
                              MOD2-IS-M2
                              FLOOR
                              FLOOR2-IF-F2
                              unsigned-byte-p
                              LOGAPP
                              ACL2::LOGHEAD$INLINE
                              rw-dir1))))))

(local
 (defthm dumy-sum-cancel-lemma
   (implies (acl2-numberp other)
            (and (equal (+ x (- x) other)
                        other)))))
(local
 (defthm integerp-implies-acl2-numberp
   (implies (integerp x)
            (acl2-numberp x))))

(local
 (defthm natp-of-sums
   (implies (and (NATP X)
                 (natp y))
            (natp (+ x y)))))

(local
 (defthmd rp-trans-when-is-rp
   (implies (is-rp term)
            (equal (rp-evlt term a)
                   (rp-evlt (caddr term) a)))
   :hints (("Goal"
            :expand (RP-TRANS-LST (CDR TERM))
            :in-theory (e/d () ())))))

(defthm has-bitp-rp-lemma
  (implies (and (valid-sc term a)
                (HAS-BITP-RP term))
           (and (bitp (rp-evlt (ex-from-rp term) a))
                (bitp (rp-evlt term a))))
  :hints (("Goal"
           :induct (HAS-BITP-RP term)
           :do-not-induct t
           :expand ((RP-TRANS-LST (CDDR TERM))
                    (RP-TRANS-LST (CDR TERM)))
           :in-theory (e/d (
                            valid-sc-single-step
                            rp-trans-when-is-rp
                            HAS-BITP-RP)
                           ()))))

(local
 (defthm calculate-vec-size-correct-lemma
   (implies (and (OR* (LOGBIT-P (EX-FROM-RP X))
                      (BINARY-FNC-P (EX-FROM-RP X))
                      (HAS-BITP-RP X))
                 (valid-sc x a)
                 (rp-evl-meta-extract-global-facts)
                 (*/+-to-mult/adder-spec-meta-fchecks state))
            (and (bitp (rp-evlt x a))
                 (bitp (rp-evlt (ex-from-rp x) a))))
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d* (or*
                              RP-EVLT-OF-EX-FROM-RP-REVERSE
                              BINARY-FNC-P
                              regular-eval-lemmas
                              regular-eval-lemmas-with-ex-from-rp)
                             (valid-sc
                              rp-evlt-of-ex-from-rp))))))

(local
 (defthm bitp-implies-integerp
   (implies (bitp x)
            (and (integerp x)
                 (UNSIGNED-BYTE-P 1 x)))))

(defret calculate-vec-size-correct
  (implies (and (rp-evl-meta-extract-global-facts)
                (eval-and-all context a)
                (valid-sc x a)
                (*/+-to-mult/adder-spec-meta-fchecks state)
                integerp)
           (and (integerp (rp-evlt x a))
                (integerp size)
                (implies (not (equal size -1))
                         (and (unsigned-byte-p size
                                               (rp-evlt x a))
                              (natp size)))))
  :fn calculate-vec-size
  :hints (("subgoal *1/7"
           :use ((:instance check-context-for-integerp-correct
                            (term (ex-from-rp x)))))
          ("goal"
           :do-not-induct t
           :induct (calculate-vec-size x context)
           :in-theory (e/d* (calculate-vec-size
                             natp
                             rp-evlt-of-ex-from-rp-reverse
                             (:rewrite
                              regular-rp-evl-of_4vec-concat$_when_*/+-to-mult/adder-spec-meta-fchecks_with-ex-from-rp)
                             (:rewrite
                              regular-rp-evl-of_bits_when_*/+-to-mult/adder-spec-meta-fchecks_with-ex-from-rp))
                            (unsigned-byte-p
                             (:rewrite default-cdr)
                             (:definition ex-from-rp)
                             (:rewrite acl2::or*-true-second)
                             (:type-prescription mult-formula-checks)
                             (:rewrite valid-sc-ex-from-rp-2)
                             (:rewrite not-include-rp)
                             (:rewrite acl2::or*-true-first)
                             (:rewrite default-car)
                             valid-sc
                             rp-termp-implies-subterms
                             rp-term-listp
                             rw-dir1
                             natp
                             +-is-sum
                             rp-trans
                             include-fnc
                             rp-evlt-of-ex-from-rp
                             check-context-for-integerp-correct
                             logcount)))))

(defret calculate-vec-size-correct-size=1
  (implies (and (rp-evl-meta-extract-global-facts)
                (eval-and-all context a)
                (valid-sc x a)
                (*/+-to-mult/adder-spec-meta-fchecks state)
                integerp
                (equal size 1))
           (unsigned-byte-p 1 (rp-evlt x a)))
  :fn calculate-vec-size
  :hints (("goal"
           :use ((:instance calculate-vec-size-correct))
           :in-theory nil)))



(local
 (defthm bitp-of-f2-with-3-elements
   (implies (and (bitp x)
                 (bitp y)
                 (bitp z))
            (bitp (f2 (sum x y z))))
   :hints (("Goal"
            :in-theory (e/d (bitp) ())))))

(local
 (defthm bitp-of-f2-with-2-elements
   (implies (and (bitp x)
                 (bitp y))
            (bitp (f2 (sum x y))))
   :hints (("Goal"
            :in-theory (e/d (bitp) ())))))

(defthm integerp-of-2vec-subtract
  (implies (and (natp size)
                (bitp carry-in))
           (integerp (2vec-subtract x y size carry-in)))
  :hints (("Goal"
           :do-not-induct t
           :induct (2vec-subtract x y size carry-in)
           :in-theory (e/d (2vec-subtract)
                           (+-is-sum
                            floor
                            rw-dir1)))))

(local
 (encapsulate
   nil

   (local
    (defthm <-to-negp
      (implies (and (integerp x)
                    (integerp y))
               (equal (SV::4VEC-< x y)
                      (sv::bool->vec (< (+ x (- y)) 0))))
      :hints (("Goal"
               :in-theory (e/d (SV::4VEC-<
                                SV::BOOL->VEC)
                               (+-is-sum
                                rw-dir1))))))

   (local
    (defthmd -to-2vec-subtract-no-carry
      (implies (and (natp size)
                    (unsigned-byte-p size x)
                    (unsigned-byte-p size y))
               (equal (+ x (- y))
                      (2vec-subtract x y size 1)))
      :otf-flg t
      :hints (("Goal"
               :do-not-induct t
               :case-split-limitations (1 1)
               :use ((:instance -to-2vec-subtract
                                (carry-in 1)))
               :in-theory (e/d () (unsigned-byte-p
                                   rw-dir1
                                   +-is-sum))))))

   

   (progn
     (local
      (use-arith-5 t))
   
     (local
      (defthm <-of-4vec-list
        (implies (and (force (integerp x))
                      (force (integerp b)))
                 (equal (< (svl::4vec-list b x) 0)
                        (< x 0)))
        :hints (("Goal"
                 :use ((:instance BITP-M2
                                  (x b)))
                 :in-theory (e/d (svl::4vec-concat$
                                  SV::4VEC-CONCAT
                                  SV::4VEC bitp)
                                 (BITP-M2 rw-dir1
                                  +-is-sum))))))

     (local
      (use-arith-5 nil)))

   (local
    (defthm bitsof-4vec-list
      (implies (and (posp size))
               (equal (svl::bits (svl::4vec-list b x) size 1)
                      (svl::bits x (1- size) 1)))
      :hints (("Goal"
               :use ((:instance SVL::BITS-OF-CONCAT-2
                                (SVL::C-SIZE 1)
                                (SVL::SIZE 1)
                                (SVL::START size)
                                (svl::term1 b)
                                (svl::term2 x)))
                                
               :in-theory (e/d () (rw-dir1
                                   +-is-sum
                                   SVL::BITS-OF-CONCAT-2))))
      ))

   (local
    (defthm neg-2vec-subtract
      (implies (and (natp size)
                    (bitp carry-in))
               (equal (- (svl::bits (2vec-subtract x y size carry-in)
                                    size 1))
                      (sv::bool->vec (< (2vec-subtract x y size carry-in) 0))))
      :hints (("goal"
               :do-not-induct t
               :induct (2vec-subtract x y size carry-in)
               :in-theory (e/d (2vec-subtract
                                sv::bool->vec
                                NOT$ BITP
                                BIT-FIX)
                               (+-is-sum
                                floor

                                unsigned-byte-p
                                rw-dir1))))))

   (defthm 4vec-<-to-subtraction-rewrite
     (implies (and (integerp x)
                   (integerp y)
                   (force (natp size))
                   (unsigned-byte-p size x)
                   (unsigned-byte-p size y))
              (EQUAL
               (- (SVL::BITS (+ x (- y))
                             size
                             1))
               (SV::4VEC-< x y)

               ))
     :hints (("Goal"
              :in-theory (e/d (-to-2vec-subtract-no-carry
                               ;;svl::bits
                               SV::4VEC-PART-SELECT
                               SV::4VEC-RSH
                               SV::4VEC-CONCAT
                               SV::4VEC-SHIFT-CORE
                               #|sv::bool->vec|#)
                              (+-IS-SUM
                               mod2-is-m2
                               floor expt
                               UNSIGNED-BYTE-P
                               rw-dir1)))))))

(local
 (encapsulate
   nil
   (local
    (use-arith-5 t))

   (defthm unsigned-byte-p-max
     (implies (and (unsigned-byte-p size-x x)
                   ;;(natp size-x)
                   (natp other-size)
                   )
              (and (unsigned-byte-p (max size-x other-size) x)
                   (unsigned-byte-p (max other-size size-x) x)))
     :hints (("Goal"
              :in-theory (e/d () (rw-dir1)))))))

(local
 (defthm  natp-of-max
   (implies (and (natp x) (natp y))
            (natp (max x y)))
   :rule-classes :type-prescription))

(defthm */+-to-mult-spec-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts)
                (eval-and-all context a)
                (valid-sc term a)
                (*/+-to-mult/adder-spec-meta-fchecks state))
           (equal (rp-evlt (mv-nth 0 (*/+-to-mult-spec-meta term context)) a)
                  (rp-evlt term a)))
  :hints (("Goal"
           :do-not-induct t
           ;;:case-split-limitations (6 6)
           :use ((:instance *-of-known-sized-vecs
                            (x (rp-evlt (cadr term) a))
                            (y (rp-evlt (caddr term) a))
                            (size1 (mv-nth 0
                                           (calculate-vec-size (cadr term)
                                                               context)))
                            (size2 (mv-nth 0
                                           (calculate-vec-size (caddr term)
                                                               context)))))
           :in-theory (e/d* (+-of-known-sized-vecs-reverse
                             2vec-subtract-binary-subtract
                             */+-to-mult-spec-meta
                             regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas)
                            (+-IS-SUM
                             max ;;floor floor2-if-f2
                             *-of-known-sized-vecs
                             SVL-MULT-FINAL-SPEC
                             RP-TRANS-LST
                             rp-trans
                             rw-dir1
                             natp
                             UNSIGNED-BYTE-P
                             ;;RP-TRANS-OPENER
                             INCLUDE-FNC)))))

(defret */+-to-mult-spec-meta-valid-sc
  (implies (valid-sc term a)
           (valid-sc (mv-nth 0 (*/+-to-mult-spec-meta term context)) a))
  :hints (("Goal"
           :do-not-induct t

           :in-theory (e/d* (*/+-to-mult-spec-meta
                             valid-sc is-rp is-if)
                            ()))))

(defret */+-to-mult-spec-meta-rp-termp
  (implies (rp-termp term)
           (rp-termp (mv-nth 0 (*/+-to-mult-spec-meta term context))))
  :hints (("Goal"
           :do-not-induct t

           :in-theory (e/d* (*/+-to-mult-spec-meta
                             valid-sc is-rp is-if)
                            ()))))
(rp::add-meta-rule
 :meta-fnc */+-to-mult-spec-meta
 :trig-fnc binary-*
 :valid-syntaxp t
 :formula-checks */+-to-mult/adder-spec-meta-fchecks
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc */+-to-mult-spec-meta
 :trig-fnc binary-+
 :valid-syntaxp t
 :formula-checks */+-to-mult/adder-spec-meta-fchecks
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc */+-to-mult-spec-meta
 :trig-fnc sv::4vec-<
 :valid-syntaxp t
 :formula-checks */+-to-mult/adder-spec-meta-fchecks
 :returns (mv term dont-rw))
