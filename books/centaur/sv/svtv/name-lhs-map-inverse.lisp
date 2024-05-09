; SV - Symbolic Vector Hardware Analysis Framework
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
; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

; Matt K. mod: Avoid ACL2(p) error from computed hint that returns state.
(set-waterfall-parallelism nil)

(include-book "fsm-obj")
(include-book "../svex/override-types")
(include-book "../svex/env-ops")
(include-book "centaur/bitops/part-install" :Dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(local (include-book "arithmetic/top" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "std/alists/alist-keys" :dir :System))
(local (std::add-default-post-define-hook :fix))





(define lhatom-eval-x ((x lhatom-p)
                       (env svex-env-p))
  :returns (val 4vec-p)
  (lhatom-case x
    :z (4vec-x)
    :var (4vec-rsh (2vec x.rsh) (svex-env-fastlookup x.name env))))



(local (defthmd logapp-right-assoc-split
         (equal (logapp w1 (logapp w2 x y) z)
                (if (<= (nfix w1) (nfix w2))
                    (logapp w1 x z)
                  (logapp w2 x (logapp (- (nfix w1) (nfix w2)) y z))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthm logapp-neg1s
         (equal (logapp w1 -1 (logapp w2 -1 y))
                (logapp (+ (nfix w1) (nfix w2)) -1 y))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)))))

(local (defthm 4vec-rsh-of-x
         (implies (natp sh)
                  (equal (4vec-rsh (2vec sh) (4vec-x))
                         (4vec-x)))
         :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core)))))

(define lhs-eval-x ((x lhs-p)
                    (env svex-env-p))
  :returns (val 4vec-p)
  (if (atom x)
      (4vec-x)
    (4vec-concat (2vec (lhrange->w (car x)))
                 (lhatom-eval-x (lhrange->atom (car x)) env)
                 (lhs-eval-x (cdr x) env)))
  ///
  (deffixequiv lhs-eval-x)

  (local (defthm lhatom-eval-x-of-z
           (implies (lhatom-case x :z)
                    (Equal (lhatom-eval-x x env) (4vec-x)))
           :hints(("Goal" :in-theory (enable lhatom-eval-x)))))



  (local (defthm 4vec-concat-of-xes
           (implies (and (2vec-p w1)
                         (2vec-p w2)
                         (natp (2vec->val w1))
                         (natp (2vec->val w2)))
                    (equal (4vec-concat w1 (4vec-x) (4vec-concat w2 (4vec-x) y))
                           (4vec-concat (2vec (+ (2vec->val w1) (2vec->val w2)))
                                        (4vec-x)
                                        y)))
           :hints(("Goal" :in-theory (enable 4vec-concat)))))

  (local (defthm 4vec-concat-rshs
           (implies (and (natp w1)
                         (natp sh1)
                         (natp w2)
                         (natp sh2)
                         (equal sh2 (+ w1 sh1)))
                    (equal (4vec-concat (2vec w1)
                                        (4vec-rsh (2vec sh1) x)
                                        (4vec-concat (2vec w2)
                                                     (4vec-rsh (2vec sh2) x)
                                                     y))
                           (4vec-concat (2vec (+ w1 w2)) (4vec-rsh (2vec sh1) x) y)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-rsh 4vec-shift-core)))))


  (defthm lhs-eval-x-of-lhs-cons
    (equal (lhs-eval-x (lhs-cons x y) env)
           (4vec-concat (2vec (lhrange->w x))
                        (lhatom-eval-x (lhrange->atom x) env)
                        (lhs-eval-x y env)))
    :hints(("Goal" :in-theory (enable lhs-cons
                                      lhatom-eval-x
                                      lhrange-nextbit))))



  (defthm lhs-eval-x-of-lhs-rsh
    (equal (lhs-eval-x (lhs-rsh sh x) env)
           (4vec-rsh (2vec (nfix sh)) (lhs-eval-x x env)))
    :hints(("Goal" :in-theory (enable lhs-eval-x lhatom-eval-x lhs-rsh))))

  (defthm lhs-eval-x-of-lhs-concat
    (equal (lhs-eval-x (lhs-concat w x y) env)
           (4vec-concat (2vec (nfix w))
                        (lhs-eval-x x env)
                        (lhs-eval-x y env)))
    :hints(("Goal" :in-theory (enable lhs-eval-x lhatom-eval-x lhs-concat))))

  (defthm lhs-eval-x-of-cons-non-var
    (implies (not (member-equal v (lhs-vars x)))
             (equal (lhs-eval-x x (cons (cons v val) env))
                    (lhs-eval-x x env)))
    :hints(("Goal" :in-theory (enable lhatom-eval-x
                                      lhs-vars
                                      lhatom-vars
                                      svex-env-lookup)))))

(define lhatom->svex-x ((x lhatom-p))
  :returns (val svex-p)
  (lhatom-case x
    :z (svex-x)
    :var (svex-rsh x.rsh (svex-var x.name)))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhatom-eval-x x env))
    :hints(("Goal" :in-theory (enable lhatom-eval-x
                                      svex-apply
                                      svex-eval)))))

(define lhs->svex-x ((x lhs-p))
  :returns (val svex-p)
  (if (atom x)
      (svex-x)
    (svex-concat (lhrange->w (car x))
                 (lhatom->svex-x (lhrange->atom (car x)))
                 (lhs->svex-x (cdr x))))
  ///
  (defret eval-of-<fn>
    (equal (svex-eval val env)
           (lhs-eval-x x env))
    :hints(("Goal" :in-theory (enable lhs-eval-x
                                      svex-apply
                                      svex-eval)))))


(define svtv-name-lhs-map-vars ((x svtv-name-lhs-map-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (append (lhs-vars (cdar x))
                (svtv-name-lhs-map-vars (cdr x)))
      (svtv-name-lhs-map-vars (cdr x))))
  ///
  (local (in-theory (enable svtv-name-lhs-map-fix))))

(define svtv-name-lhs-map-eval-x ((x svtv-name-lhs-map-p) (env svex-env-p))
  :returns (res svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-name-lhs-map-eval-x (cdr x) env)))
    (cons (cons (caar x) (lhs-eval-x (cdar x) env))
          (svtv-name-lhs-map-eval-x (cdr x) env)))
  ///
  (defret lookup-in-<fn>
    (equal (hons-assoc-equal var res)
           (let ((pair (hons-assoc-equal var (svtv-name-lhs-map-fix x))))
             (and pair
                  (cons var (lhs-eval-x (cdr pair) env))))))

  (defret svex-env-boundp-of-<fn>
    (iff (svex-env-boundp var res)
         (hons-assoc-equal (svar-fix var) (svtv-name-lhs-map-fix x)))
    :hints(("Goal" :in-theory (enable svex-env-boundp))))

  (defret svex-env-lookupp-of-<fn>
    (equal (svex-env-lookup var res)
           (let ((pair (hons-assoc-equal (svar-fix var) (svtv-name-lhs-map-fix x))))
             (if pair
                 (lhs-eval-x (cdr pair) env)
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (defcong svex-envs-similar equal (lhs-eval-x x env) 2
    :hints(("Goal" :in-theory (enable lhs-eval-x lhatom-eval-x))))

  (defcong svex-envs-similar equal (svtv-name-lhs-map-eval-x x env) 2)

  (local (in-theory (enable svtv-name-lhs-map-fix)))

  (defthm svtv-name-lhs-map-eval-x-of-cons-non-var
    (implies (not (member-equal v (svtv-name-lhs-map-vars x)))
             (equal (svtv-name-lhs-map-eval-x x (cons (cons v val) env))
                    (svtv-name-lhs-map-eval-x x env)))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-vars)))))


(define svtv-name-lhs-map-eval ((x svtv-name-lhs-map-p) (env svex-env-p))
  :returns (res svex-env-p)
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svtv-name-lhs-map-eval (cdr x) env)))
    (cons (cons (caar x) (lhs-eval-zx (cdar x) env))
          (svtv-name-lhs-map-eval (cdr x) env)))
  ///
  (defret lookup-in-<fn>
    (equal (hons-assoc-equal var res)
           (let ((pair (hons-assoc-equal var (svtv-name-lhs-map-fix x))))
             (and pair
                  (cons var (lhs-eval-zx (cdr pair) env))))))

  (defcong svex-envs-similar equal (lhs-eval-zx x env) 2
    :hints(("Goal" :in-theory (enable lhs-eval-zx lhatom-eval-zero))))

  (defcong svex-envs-similar equal (svtv-name-lhs-map-eval x env) 2)

  (local (in-theory (enable svtv-name-lhs-map-fix))))


(define lhs-range-no-zs ((width posp)
                         (lhs lhs-p))
  :measure (len lhs)
  (if (atom lhs)
      nil
    (b* (((lhrange l1) (car lhs)))
      (and (lhatom-case l1.atom :var)
           (or (<= (lposfix width) l1.w)
               (lhs-range-no-zs (- (lposfix width) l1.w) (cdr lhs))))))
  ///
  (deffixequiv lhs-range-no-zs)

  (defthm lhs-range-no-zs-of-lhs-cons
    (equal (lhs-range-no-zs width (lhs-cons x y))
           (and (lhatom-case (lhrange->atom x) :var)
                (or (<= (pos-fix width) (lhrange->w x))
                    (lhs-range-no-zs (- (pos-fix width) (lhrange->w x)) y))))
    :hints(("Goal" :in-theory (enable lhs-cons))))

  (defthm lhs-range-no-zs-of-cons
    (equal (lhs-range-no-zs width (cons x y))
           (and (lhatom-case (lhrange->atom x) :var)
                (or (<= (pos-fix width) (lhrange->w x))
                    (lhs-range-no-zs (- (pos-fix width) (lhrange->w x)) y)))))

  (defthm lhs-range-no-zs-of-lhs-concat
    (equal (lhs-range-no-zs width (lhs-concat w x y))
           (if (<= (pos-fix width) (nfix w))
               (lhs-range-no-zs width x)
             (and (or (zp w) (lhs-range-no-zs w x))
                  (lhs-range-no-zs (- (pos-fix width) (nfix w)) y))))
    :hints(("Goal" :in-theory (e/d (lhs-concat) (pos-fix)))))

  (defthm lhs-range-no-zs-of-lhs-norm
    (equal (lhs-range-no-zs width (lhs-norm lhs))
           (lhs-range-no-zs width lhs))
    :hints(("Goal" :in-theory (enable lhs-norm))))

  (defcong lhs-norm-equiv equal (lhs-range-no-zs width lhs) 2
    :hints (("goal" :use (lhs-range-no-zs-of-lhs-norm
                          (:instance lhs-range-no-zs-of-lhs-norm (lhs lhs-equiv)))
             :in-theory (disable lhs-range-no-zs-of-lhs-norm
                                 lhs-range-no-zs))))

  (defthmd lhs-range-no-zs-decomp
    (implies (and (posp w1) (posp w2))
             (equal (lhs-range-no-zs (+ w1 w2) lhs)
                    (and (lhs-range-no-zs w1 lhs)
                         (lhs-range-no-zs w2 (lhs-rsh w1 lhs)))))
    :hints(("Goal" :in-theory (enable lhs-rsh))))

  (defthm lhs-range-no-zs-of-rsh-when-prev-range
    (implies (and (posp w1) (posp w2)
                  (lhs-range-no-zs w1 lhs))
             (equal (lhs-range-no-zs w2 (lhs-rsh w1 lhs))
                    (lhs-range-no-zs (+ w1 w2) lhs)))
    :hints(("Goal" :use lhs-range-no-zs-decomp)))

  (defthm lhs-range-no-zs-of-nil
    (not (lhs-range-no-zs width nil))))

(define lhs-range-all-zs ((width posp)
                          (lhs lhs-p))
  :measure (len lhs)
  (if (atom lhs)
      t
    (b* (((lhrange l1) (car lhs)))
      (and (lhatom-case l1.atom :z)
           (or (<= (lposfix width) l1.w)
               (lhs-range-all-zs (- (lposfix width) l1.w) (cdr lhs))))))
  ///
  (deffixequiv lhs-range-all-zs)

  (defthm lhs-range-all-zs-of-lhs-cons
    (equal (lhs-range-all-zs width (lhs-cons x y))
           (and (lhatom-case (lhrange->atom x) :z)
                (or (<= (pos-fix width) (lhrange->w x))
                    (lhs-range-all-zs (- (pos-fix width) (lhrange->w x)) y))))
    :hints(("Goal" :in-theory (enable lhs-cons))))

  (defthm lhs-range-all-zs-of-cons
    (equal (lhs-range-all-zs width (cons x y))
           (and (lhatom-case (lhrange->atom x) :z)
                (or (<= (pos-fix width) (lhrange->w x))
                    (lhs-range-all-zs (- (pos-fix width) (lhrange->w x)) y)))))

  (defthm lhs-range-all-zs-of-lhs-concat
    (equal (lhs-range-all-zs width (lhs-concat w x y))
           (if (<= (pos-fix width) (nfix w))
               (lhs-range-all-zs width x)
             (and (or (zp w) (lhs-range-all-zs w x))
                  (lhs-range-all-zs (- (pos-fix width) (nfix w)) y))))
    :hints(("Goal" :in-theory (e/d (lhs-concat) (pos-fix)))))

  (defthm lhs-range-all-zs-of-lhs-norm
    (equal (lhs-range-all-zs width (lhs-norm lhs))
           (lhs-range-all-zs width lhs))
    :hints(("Goal" :in-theory (enable lhs-norm))))

  (defcong lhs-norm-equiv equal (lhs-range-all-zs width lhs) 2
    :hints (("goal" :use (lhs-range-all-zs-of-lhs-norm
                          (:instance lhs-range-all-zs-of-lhs-norm (lhs lhs-equiv)))
             :in-theory (disable lhs-range-all-zs-of-lhs-norm
                                 lhs-range-all-zs))))

  (defthmd lhs-range-all-zs-decomp
    (implies (and (posp w1) (posp w2))
             (equal (lhs-range-all-zs (+ w1 w2) lhs)
                    (and (lhs-range-all-zs w1 lhs)
                         (lhs-range-all-zs w2 (lhs-rsh w1 lhs)))))
    :hints(("Goal" :in-theory (enable lhs-rsh))))

  (defthm lhs-range-all-zs-of-rsh-when-prev-range
    (implies (and (posp w1) (posp w2)
                  (lhs-range-all-zs w1 lhs))
             (equal (lhs-range-all-zs w2 (lhs-rsh w1 lhs))
                    (lhs-range-all-zs (+ w1 w2) lhs)))
    :hints(("Goal" :use lhs-range-all-zs-decomp)))

  (defthm lhs-range-all-zs-when-lhs-range-no-zs-non-disjoint
    (implies (lhs-range-no-zs width1 lhs)
             (not (lhs-range-all-zs width lhs)))
    :hints(("Goal" :in-theory (enable lhs-range-no-zs))))

  (defthm lhs-range-no-zs-when-lhs-range-all-zs-non-disjoint
    (implies (lhs-range-all-zs width lhs)
             (not (lhs-range-no-zs width1 lhs)))
    :hints (("goal" :in-theory (disable lhs-range-all-zs))))

  (defthm lhs-range-all-zs-of-nil
    (lhs-range-all-zs width nil)))

;; (local (define lhrange-rsh ((sh natp) (x lhrange-p))
;;          :guard (< sh (lhrange->w x))
;;          (b* (((lhrange x)))
;;            (make-lhrange :atom (lhatom-case x.atom
;;                                  :z x.atom
;;                                  :var (lhatom-var x.atom.name (+ x.atom.rsh (lnfix sh))))
;;                          :w (- x.w (lnfix sh))))))

;; (local (defthm lhs-rsh-of-lhs-cons
;;          (equal (lhs-rsh offset (lhs-cons x y))
;;                 (b* (((lhrange x)))
;;                   (if (<= x.w (nfix offset))
;;                       (lhs-rsh (- (nfix offset) x.w) y)
;;                     (lhs-cons (lhrange-rsh sh x) y))))
;;          :hints(("Goal" :in-theory (enable lhs-rsh lhrange-rsh)))))



(local
 (defsection lhs-rsh-of-lhs-concat-under-lhs-norm-equiv
   (local (defun lhs-rsh-of-lhs-concat-under-lhs-norm-equiv-ind (sh w x y)
            (if (atom x)
                (list sh w x y)
              (lhs-rsh-of-lhs-concat-under-lhs-norm-equiv-ind
               (- (nfix sh) (lhrange->w (car x)))
               (- (nfix w) (lhrange->w (car x)))
               (cdr x) y))))

   (defthm lhs-rsh-of-0
     (equal (lhs-rsh 0 x)
            (lhs-fix x))
     :hints(("Goal" :in-theory (enable lhs-rsh))))

   (local (defthm lhs-rsh-when-atom
            (implies (atom x)
                     (equal (lhs-rsh w x) nil))
            :hints(("Goal" :in-theory (enable lhs-rsh)))))

   (defthmd lhs-rsh-of-lhs-concat-under-lhs-norm-equiv
     (lhs-norm-equiv (lhs-rsh sh (lhs-concat w x y))
                     (if (<= (nfix sh) (nfix w))
                         (lhs-concat (- (nfix w) (nfix sh)) (lhs-rsh sh x) y)
                       (lhs-rsh (- (nfix sh) (nfix w)) y)))
     :hints(("Goal" :in-theory (enable lhs-concat)
             :induct (lhs-rsh-of-lhs-concat-under-lhs-norm-equiv-ind sh w x y)
             :expand ((lhs-concat w x y)
                      (:free (x y) (lhs-rsh sh (cons x y)))
                      (:free (x y) (lhs-norm (cons x y)))))))

   ;; (local (defun lhs-rsh-of-lhs-rsh-ind (sh1 sh2 x)
   ;;          (if (atom x)
   ;;              (list sh1 sh2)
   ;;            (lhs-rsh-of-lhs-rsh-ind
   ;;             (- (nfix sh1) (lhrange->w (car x)))
   ;;             (- (nfix sh2) (lhrange->w (car x)))
   ;;             (cdr x)))))

   (defthm lhs-rsh-of-lhs-rsh-under-lhs-norm-equiv
     (lhs-norm-equiv (lhs-rsh sh1 (lhs-rsh sh2 x))
                     (lhs-rsh (+ (nfix sh1) (nfix sh2)) x))
     :hints(("Goal" :induct (lhs-rsh sh2 x)
             :in-theory (enable lhs-rsh lhs-norm))))))

(define lhs-covers-range-p ((width posp)
                            (offset natp)
                            (lhs lhs-p))
  (lhs-range-no-zs width (lhs-rsh offset lhs))
  ///

  (defthm lhs-covers-range-p-of-lhs-cons
    (equal (lhs-covers-range-p width offset (lhs-cons x y))
           (lhs-covers-range-p width offset (cons x y)))
    :hints(("Goal" :in-theory (enable lhs-rsh))))

  (defthm lhs-covers-range-p-of-cons
    (equal (lhs-covers-range-p width offset (cons x y))
           (b* (((lhrange x)))
             (cond ((<= x.w (nfix offset))
                    (lhs-covers-range-p width (- (nfix offset) x.w) y))
                   ((<= (+ (nfix offset) (pos-fix width)) x.w)
                    (lhatom-case x.atom :var))
                   (t (and (lhatom-case x.atom :var)
                           (lhs-covers-range-p (- (+ (pos-fix width) (nfix offset)) x.w) 0 y))))))
    :hints(("Goal" :in-theory (enable lhs-rsh))))

  (defthm lhs-covers-range-p-of-lhs-norm
    (equal (lhs-covers-range-p width offset (lhs-norm lhs))
           (lhs-covers-range-p width offset lhs)))



  (defcong lhs-norm-equiv equal (lhs-covers-range-p width offset lhs) 3
    :hints (("goal" :use (lhs-covers-range-p-of-lhs-norm
                          (:instance lhs-covers-range-p-of-lhs-norm (lhs lhs-equiv)))
             :in-theory (disable lhs-covers-range-p-of-lhs-norm
                                 lhs-covers-range-p))))

  (defthm lhs-covers-range-p-of-lhs-concat
    (equal (lhs-covers-range-p width offset (lhs-concat w x y))
           (cond ((<= (nfix w) (nfix offset))
                  (lhs-covers-range-p width (- (nfix offset) (nfix w)) y))
                 ((<= (+ (nfix offset) (pos-fix width)) (nfix w))
                  (lhs-covers-range-p width offset x))
                 (t (and (lhs-covers-range-p (- (nfix w) (nfix offset)) offset x)
                         (lhs-covers-range-p (- (+ (pos-fix width) (nfix offset)) (nfix w)) 0 y)))))
    :hints(("Goal" :in-theory (enable lhs-rsh-of-lhs-concat-under-lhs-norm-equiv))))

  (defthm lhs-covers-range-p-of-lhs-rsh
    (equal (lhs-covers-range-p width offset (lhs-rsh sh x))
           (lhs-covers-range-p width (+ (nfix offset) (nfix sh)) x)))

  (defthmd lhs-covers-range-p-decomp
    (implies (and (posp w1) (posp w2))
             (equal (lhs-covers-range-p (+ w1 w2) offset lhs)
                    (and (lhs-covers-range-p w1 offset lhs)
                         (lhs-covers-range-p w2 (+ w1 (nfix offset)) lhs))))
    :hints (("goal" :use ((:instance lhs-range-no-zs-decomp
                           (lhs (lhs-rsh offset lhs)))))))

  (deffixequiv lhs-covers-range-p)

  (local (defthm pos-fix-equal-forward
           (implies (equal (pos-fix x) (pos-fix y))
                    (pos-equiv x y))
           :rule-classes :forward-chaining))

  (local (defthm nfix-equal-forward
           (implies (equal (nfix x) (nfix y))
                    (nat-equiv x y))
           :rule-classes :forward-chaining))


  (defthm lhs-covers-range-p-of-subrange
    (implies (and (lhs-covers-range-p width offset lhs)
                  (<= (nfix offset) (nfix offset1))
                  (<= (+ (nfix offset1) (pos-fix width1))
                      (+ (nfix offset) (pos-fix width))))
             (lhs-covers-range-p width1 offset1 lhs))
    :hints (("Goal" :use ((:instance lhs-covers-range-p-decomp
                           (w1 (- (nfix offset1) (nfix offset)))
                           (w2 (- (pos-fix width) (- (nfix offset1) (nfix offset)))))
                          (:instance lhs-covers-range-p-decomp
                           (offset offset1)
                           (w1 (pos-fix width1))
                           (w2 (- (pos-fix width) (+ (pos-fix width1) (- (nfix offset1) (nfix offset)))))))
             :in-theory (disable lhs-covers-range-p))))

  (defthm lhs-covers-range-p-nil
    (not (lhs-covers-range-p width offset nil))
    :hints(("Goal" :in-theory (enable lhs-rsh)))))


(define svtv-name-lhs-map-covers-lhs-p ((x lhs-p)
                                        (map svtv-name-lhs-map-p))
  :prepwork ((local (in-theory (disable hons-assoc-equal
                                        HONS-ASSOC-EQUAL-OF-SVTV-NAME-LHS-MAP-FIX))))
  (if (atom x)
      t
    (and (b* (((lhrange x1) (car x)))
           (lhatom-case x1.atom
             :z t
             :var (lhs-covers-range-p x1.w x1.atom.rsh
                                      (cdr (hons-get x1.atom.name (svtv-name-lhs-map-fix map))))))
         (svtv-name-lhs-map-covers-lhs-p (cdr x) map))))

(define ranges-collide-p ((width1 posp)
                            (offset1 natp)
                            (width2 posp)
                            (offset2 natp))
  (if (<= (lnfix offset1) (lnfix offset2))
      (< (lnfix offset2) (+ (lposfix width1) (lnfix offset1)))
    (< (lnfix offset1) (+ (lposfix width2) (lnfix offset2))))
  ///
  (defthmd ranges-collide-p-symm
    (implies (ranges-collide-p width2 offset2 width1 offset1)
             (ranges-collide-p width1 offset1 width2 offset2))))

(define lhs-empty-range-p ((width posp)
                           (offset natp)
                           (lhs lhs-p))
  (lhs-range-all-zs width (lhs-rsh offset lhs))
  ///

  (defthm lhs-empty-range-p-of-lhs-cons
    (equal (lhs-empty-range-p width offset (lhs-cons x y))
           (lhs-empty-range-p width offset (cons x y)))
    :hints(("Goal" :in-theory (enable lhs-rsh))))

  (defthm lhs-empty-range-p-of-cons
    (equal (lhs-empty-range-p width offset (cons x y))
           (b* (((lhrange x)))
             (cond ((<= x.w (nfix offset))
                    (lhs-empty-range-p width (- (nfix offset) x.w) y))
                   ((<= (+ (nfix offset) (pos-fix width)) x.w)
                    (lhatom-case x.atom :z))
                   (t (and (lhatom-case x.atom :z)
                           (lhs-empty-range-p (- (+ (pos-fix width) (nfix offset)) x.w) 0 y))))))
    :hints(("Goal" :in-theory (enable lhs-rsh))))

  (defthm lhs-empty-range-p-of-lhs-norm
    (equal (lhs-empty-range-p width offset (lhs-norm lhs))
           (lhs-empty-range-p width offset lhs)))



  (defcong lhs-norm-equiv equal (lhs-empty-range-p width offset lhs) 3
    :hints (("goal" :use (lhs-empty-range-p-of-lhs-norm
                          (:instance lhs-empty-range-p-of-lhs-norm (lhs lhs-equiv)))
             :in-theory (disable lhs-empty-range-p-of-lhs-norm
                                 lhs-empty-range-p))))

  (defthm lhs-empty-range-p-of-lhs-concat
    (equal (lhs-empty-range-p width offset (lhs-concat w x y))
           (cond ((<= (nfix w) (nfix offset))
                  (lhs-empty-range-p width (- (nfix offset) (nfix w)) y))
                 ((<= (+ (nfix offset) (pos-fix width)) (nfix w))
                  (lhs-empty-range-p width offset x))
                 (t (and (lhs-empty-range-p (- (nfix w) (nfix offset)) offset x)
                         (lhs-empty-range-p (- (+ (pos-fix width) (nfix offset)) (nfix w)) 0 y)))))
    :hints(("Goal" :in-theory (enable lhs-rsh-of-lhs-concat-under-lhs-norm-equiv))))

  (defthm lhs-empty-range-p-of-lhs-rsh
    (equal (lhs-empty-range-p width offset (lhs-rsh sh x))
           (lhs-empty-range-p width (+ (nfix offset) (nfix sh)) x)))

  (defthmd lhs-empty-range-p-decomp
    (implies (and (posp w1) (posp w2))
             (equal (lhs-empty-range-p (+ w1 w2) offset lhs)
                    (and (lhs-empty-range-p w1 offset lhs)
                         (lhs-empty-range-p w2 (+ w1 (nfix offset)) lhs))))
    :hints (("goal" :use ((:instance lhs-range-all-zs-decomp
                           (lhs (lhs-rsh offset lhs)))))))

  (deffixequiv lhs-empty-range-p)

  (local (defthm pos-fix-equal-forward
           (implies (equal (pos-fix x) (pos-fix y))
                    (pos-equiv x y))
           :rule-classes :forward-chaining))

  (local (defthm nfix-equal-forward
           (implies (equal (nfix x) (nfix y))
                    (nat-equiv x y))
           :rule-classes :forward-chaining))


  (defthm lhs-empty-range-p-of-subrange
    (implies (and (lhs-empty-range-p width offset lhs)
                  (<= (nfix offset) (nfix offset1))
                  (<= (+ (nfix offset1) (pos-fix width1))
                      (+ (nfix offset) (pos-fix width))))
             (lhs-empty-range-p width1 offset1 lhs))
    :hints (("Goal" :use ((:instance lhs-empty-range-p-decomp
                           (w1 (- (nfix offset1) (nfix offset)))
                           (w2 (- (pos-fix width) (- (nfix offset1) (nfix offset)))))
                          (:instance lhs-empty-range-p-decomp
                           (offset offset1)
                           (w1 (pos-fix width1))
                           (w2 (- (pos-fix width) (+ (pos-fix width1) (- (nfix offset1) (nfix offset)))))))
             :in-theory (disable lhs-empty-range-p))))

  (defthm lhs-empty-range-p-when-lhs-covers-range-p-non-disjoint
    (implies (and (lhs-covers-range-p width1 offset1 lhs)
                  (ranges-collide-p width offset width1 offset1))
             (not (lhs-empty-range-p width offset lhs)))
    :hints(("Goal" :in-theory (enable lhs-covers-range-p
                                      ranges-collide-p)
            :use ((:instance lhs-range-no-zs-decomp
                   (w1 (- (nfix offset) (nfix offset1)))
                   (w2 (- (pos-fix width1) (- (nfix offset) (nfix offset1))))
                   (lhs (lhs-rsh offset1 lhs)))
                  (:instance lhs-range-all-zs-decomp
                   (w1 (- (nfix offset1) (nfix offset)))
                   (w2 (- (pos-fix width) (- (nfix offset1) (nfix offset))))
                   (lhs (lhs-rsh offset lhs))))
            :do-not-induct t))
    :otf-flg t)



  (defthm lhs-covers-range-p-when-lhs-empty-range-p-non-disjoint
    (implies (and (lhs-empty-range-p width offset lhs)
                  (ranges-collide-p width offset width1 offset1))
             (not (lhs-covers-range-p width1 offset1 lhs)))
    :hints(("Goal" :in-theory (disable lhs-empty-range-p))))

  (defthm lhs-empty-range-p-nil
    (lhs-empty-range-p width offset nil)
    :hints(("Goal" :in-theory (enable lhs-rsh)))))



(define lhs-varmask ((x lhs-p))
  (if (atom x)
      0
    (logapp (lhrange->w (car x))
            (- (bool->bit (lhatom-case (lhrange->atom (car x)) :var)))
            (lhs-varmask (cdr x))))
  ///
  (deffixequiv lhs-varmask)

  (defthm lhs-varmask-of-lhs-cons
    (equal (lhs-varmask (lhs-cons x1 x))
           (lhs-varmask (cons x1 x)))
    :hints(("Goal" :in-theory (enable lhs-cons bool->bit))))

  (defthm lhs-varmask-of-lhs-norm
    (equal (lhs-varmask (lhs-norm x))
           (lhs-varmask x))
    :hints(("Goal" :in-theory (enable lhs-norm))))

  (defcong lhs-norm-equiv equal (lhs-varmask x) 1
    :hints (("goal" :use ((:instance lhs-varmask-of-lhs-norm)
                          (:instance lhs-varmask-of-lhs-norm (x x-equiv)))
             :in-theory (disable lhs-varmask-of-lhs-norm))))

  (defthm lhs-varmask-of-lhs-concat
    (equal (lhs-varmask (lhs-concat w x y))
           (logapp w (lhs-varmask x) (lhs-varmask y)))
    :hints(("Goal" :in-theory (enable lhs-concat
                                      logapp-right-assoc-split))))

  (defthm lhs-varmask-of-lhs-rsh
    (equal (lhs-varmask (lhs-rsh sh x))
           (logtail sh (lhs-varmask x)))
    :hints(("Goal" :in-theory (enable lhs-rsh)))))


(define var-lhs-mask ((v svar-p)
                      (x lhs-p))
  ;; accumulates the mask of the parts of v that are used in lhs
  :returns (mask natp)
  (b* (((when (atom x)) 0)
       ((lhrange x1) (car x))
       ((when (lhatom-case x1.atom :z))
        (var-lhs-mask v (cdr x)))
       ((lhatom-var x1.atom))
       ((unless (equal x1.atom.name (svar-fix v)))
        (var-lhs-mask v (cdr x))))
    (bitops::part-install -1 (var-lhs-mask v (cdr x))
                          :width x1.w
                          :low x1.atom.rsh))
  ///
  (deffixequiv var-lhs-mask)

  (defthm var-lhs-mask-of-lhs-cons
    (equal (var-lhs-mask v (lhs-cons x1 x))
           (b* (((lhrange x1)))
             (if (and (lhatom-case x1.atom :var)
                      (equal (lhatom-var->name x1.atom) (svar-fix v)))
                 (bitops::part-install -1 (var-lhs-mask v x) :width x1.w :low (lhatom-var->rsh x1.atom))
               (var-lhs-mask v x))))
    :hints(("Goal" :in-theory (e/d (lhs-cons
                                    lhrange-nextbit
                                    bitops::part-install-in-terms-of-logapp
                                    logapp-right-assoc-split)
                                   (bitops::part-install)))))

  (defthm var-lhs-mask-of-lhs-norm
    (equal (var-lhs-mask v (lhs-norm x))
           (var-lhs-mask v x))
    :hints(("Goal" :in-theory (enable lhs-norm))))

  (defcong lhs-norm-equiv equal (var-lhs-mask v x) 2
    :hints (("goal" :use ((:instance var-lhs-mask-of-lhs-norm)
                          (:instance var-lhs-mask-of-lhs-norm (x x-equiv)))
             :in-theory (disable var-lhs-mask-of-lhs-norm)))))




(define lhs-add-name-lhs-map-inverse ((dom-range lhrange-p)
                                      (offset natp)
                                      (inverse-lhs lhs-p))
  ;; Inverse-lhs is an LHS.  We want to insert dom-range at the given offset.
  ;; But we also want to check that the range where we're inserting it is all
  ;; Z.
  :returns (mv (collision)
               (new-lhs lhs-p))
  (b* (((lhrange dom-range))
       (collision (and (not (lhs-empty-range-p dom-range.w offset inverse-lhs))
                       (list (lhrange-fix dom-range)
                             (lhs-concat dom-range.w (lhs-rsh offset inverse-lhs) nil)))))
    (mv collision
        (lhs-concat offset inverse-lhs
                    (lhs-cons dom-range (lhs-rsh (+ (lnfix offset) dom-range.w) inverse-lhs)))))
  ///

  (defret <fn>-eval
    (equal (lhs-eval new-lhs env)
           (4vec-part-install (2vec (nfix offset))
                              (2vec (lhrange->w dom-range))
                              (lhs-eval inverse-lhs env)
                              (lhrange-eval dom-range env)))
    :hints(("Goal" :in-theory (enable 4vec-part-install)
            :expand ((:free (x y) (lhs-eval (cons x y) env))))))

  (defret <fn>-eval-x
    (equal (lhs-eval-x new-lhs env)
           (4vec-part-install (2vec (nfix offset))
                              (2vec (lhrange->w dom-range))
                              (lhs-eval-x inverse-lhs env)
                              (lhatom-eval-x (lhrange->atom dom-range) env)))
    :hints(("Goal" :in-theory (enable 4vec-part-install)
            :expand ((:free (x y) (lhs-eval-x (cons x y) env))))))

  (defret collision-of-<fn>
    (iff collision
         (not (lhs-empty-range-p (lhrange->w dom-range) offset inverse-lhs))))

  (defret <fn>-of-lhs-norm-under-lhs-norm-equiv
    (b* (((mv collision1 new-lhs1) (lhs-add-name-lhs-map-inverse dom-range offset (lhs-norm inverse-lhs))))
      (and (iff collision1 collision)
           (lhs-norm-equiv new-lhs1 new-lhs))))

  (defret <fn>-preserves-lhs-covers-range-p
    (implies (and (lhatom-case (lhrange->atom dom-range) :var)
                  (lhs-covers-range-p w sh inverse-lhs))
             (lhs-covers-range-p w sh new-lhs)))

  (defret lhs-covers-range-p-of-<fn>
    (implies (and (lhatom-case (lhrange->atom dom-range) :var)
                  (<= (pos-fix w) (lhrange->w dom-range)))
             (lhs-covers-range-p w offset new-lhs)))

  (defret no-collision-implies-range-eval-preserved-of-<fn>
    (implies (and (not collision)
                  (lhs-covers-range-p (2vec->val w) (2vec->val sh) inverse-lhs)
                  (2vec-p w) (2vec-p sh)
                  (posp (2vec->val w)) (natp (2vec->val sh)))
             (equal (4vec-concat w (4vec-rsh sh (lhs-eval-x new-lhs env)) rst)
                    (4vec-concat w (4vec-rsh sh (lhs-eval-x inverse-lhs env)) rst)))
    :hints(("Goal" :in-theory (enable ranges-collide-p))))


  (defret lhs-empty-range-p-of-<fn>
    (implies (lhatom-case (lhrange->atom dom-range) :var)
             (equal (lhs-empty-range-p w rsh new-lhs)
                    (and (lhs-empty-range-p w rsh inverse-lhs)
                         (not (ranges-collide-p w rsh (lhrange->w dom-range) offset)))))
    :hints(("Goal" :in-theory (enable ranges-collide-p))))

  (defret lhs-varmask-of-<fn>
    (implies (lhatom-case (lhrange->atom dom-range) :var)
             (equal (lhs-varmask new-lhs)
                    (bitops::part-install -1 (lhs-varmask inverse-lhs)
                                          :width (lhrange->w dom-range)
                                          :low offset)))
    :hints(("Goal" :in-theory (e/d (bitops::part-install-in-terms-of-logapp
                                    lhs-varmask)
                                   (bitops::part-install)))))

  (defret lhs-vars-of-<fn>
    (implies (and (not (member-equal v (lhs-vars inverse-lhs)))
                  (not (member-equal v (lhatom-vars (lhrange->atom dom-range)))))
             (not (member-equal v (lhs-vars new-lhs))))
    :hints(("Goal" :in-theory (disable lhs-vars-when-consp))))


  (defret lhs-bitproj-of-<fn>
    (equal (lhs-bitproj n new-lhs)
           (if (and (<= (nfix offset) (nfix n))
                    (< (nfix n) (+ (nfix offset) (lhrange->w dom-range))))
               (lhatom-bitproj (- (nfix n) (nfix offset)) (lhrange->atom dom-range))
             (lhs-bitproj n inverse-lhs)))
    :hints(("Goal" :in-theory (enable lhrange-bitproj)))))




(define lhrange-collides-with-lhs-p ((x lhrange-p)
                                     (y lhs-p))

  (if (atom y)
      nil
    (or (b* (((lhrange x))
             ((unless (lhatom-case x.atom :var))
              nil)
             ((lhatom-var x.atom))
             ((lhrange y1) (car y)))
          (lhatom-case y1.atom
            :z nil
            :var (and (equal y1.atom.name x.atom.name)
                      (ranges-collide-p x.w x.atom.rsh y1.w y1.atom.rsh))))
        (lhrange-collides-with-lhs-p x (cdr y))))
  ///
  (deffixequiv lhrange-collides-with-lhs-p)

  (defthm lhrange-collides-with-lhs-p-of-lhs-cons
    (equal (lhrange-collides-with-lhs-p x (lhs-cons y1 y))
           (lhrange-collides-with-lhs-p x (cons y1 y)))
    :hints(("Goal" :in-theory (enable lhs-cons lhrange-nextbit
                                      ranges-collide-p))))

  (defthm lhrange-collides-with-lhs-p-of-lhs-norm
    (equal (lhrange-collides-with-lhs-p x (lhs-norm y))
           (lhrange-collides-with-lhs-p x y))
    :hints(("Goal" :in-theory (enable lhs-norm))))

  (defcong lhs-norm-equiv equal (lhrange-collides-with-lhs-p x y) 2
    :hints (("goal" :use (lhrange-collides-with-lhs-p-of-lhs-norm
                          (:instance lhrange-collides-with-lhs-p-of-lhs-norm
                           (y y-equiv)))
             :in-theory (disable lhrange-collides-with-lhs-p-of-lhs-norm))))

  (defthmd lhrange-collides-with-lhs-p-decomp
    (implies (and (posp w1) (posp w2))
             (equal (lhrange-collides-with-lhs-p (lhrange (+ w1 w2)
                                                          (lhatom-var name offset)) y)
                    (or (lhrange-collides-with-lhs-p (lhrange w1
                                                              (lhatom-var name offset)) y)
                        (lhrange-collides-with-lhs-p (lhrange w2
                                                              (lhatom-var name (+ w1 (nfix offset))))  y))))
    :hints(("Goal" :in-theory (enable ranges-collide-p))))

  (defthm lhrange-collides-with-lhs-p-when-atom
    (implies (atom y)
             (not (lhrange-collides-with-lhs-p x y))))

  (defthm lhrange-collides-with-lhs-p-nil
    (not (lhrange-collides-with-lhs-p x nil)))

  (defthm lhrange-collides-with-lhs-p-of-z
    (implies (not (lhatom-case (lhrange->atom x) :var))
             (not (lhrange-collides-with-lhs-p x y)))))

(define lhses-collide-p ((x lhs-p) (y lhs-p))
  (if (atom x)
      nil
    (or (lhrange-collides-with-lhs-p (car x) y)
        (lhses-collide-p (cdr x) y)))
  ///
  (deffixequiv lhses-collide-p)

  (defthm lhses-collide-p-of-lhs-norm-2
    (equal (lhses-collide-p x (lhs-norm y))
           (lhses-collide-p x y)))

  (defthm lhses-collide-p-of-lhs-cons
    (equal (lhses-collide-p (lhs-cons x1 x) y)
           (lhses-collide-p (cons x1 x) y))
    :hints(("Goal" :in-theory (enable lhs-cons lhrange-nextbit)
            :use ((:instance lhrange-collides-with-lhs-p-decomp
                   (w1 (lhrange->w x1)) (w2 (lhrange->w (car x)))
                   (offset (lhatom-var->rsh (lhrange->atom x1)))
                   (name (lhatom-var->name (lhrange->atom x1)))
                   (y y)))))
    :otf-flg t)

  (defthm lhses-collide-p-of-lhs-norm
    (equal (lhses-collide-p (lhs-norm x) y)
           (lhses-collide-p x y))
    :hints(("Goal" :in-theory (enable lhs-norm))))

  (defcong lhs-norm-equiv equal (lhses-collide-p x y) 1
    :hints (("goal" :use (lhses-collide-p-of-lhs-norm
                          (:instance lhses-collide-p-of-lhs-norm (x x-equiv)))
             :in-theory (disable lhses-collide-p-of-lhs-norm))))

  (defcong lhs-norm-equiv equal (lhses-collide-p x y) 2
    :hints (("goal" :use (lhses-collide-p-of-lhs-norm-2
                          (:instance lhses-collide-p-of-lhs-norm-2 (y y-equiv)))
             :in-theory (disable lhses-collide-p-of-lhs-norm-2))))


  (local (defthm lhses-collide-p-of-cons-right
           (equal (lhses-collide-p x (cons y1 y2))
                  (or (lhrange-collides-with-lhs-p y1 x)
                      (lhses-collide-p x y2)))
           :hints(("Goal" :in-theory (enable lhrange-collides-with-lhs-p
                                             ranges-collide-p)))))

  (defthm lhses-collide-p-of-atom-right
    (implies (atom y)
             (not (lhses-collide-p x y)))
    :hints(("Goal" :in-theory (enable lhses-collide-p))))

  (defthmd lhses-collide-p-open-right
    (equal (lhses-collide-p x y)
           (if (atom y)
               nil
             (or (lhrange-collides-with-lhs-p (car y) x)
                 (lhses-collide-p x (cdr y)))))
    :rule-classes ((:definition
                    :install-body nil
                    :controller-alist ((lhses-collide-p nil t)))))


  (defthm lhses-collide-p-symm
    (implies (lhses-collide-p y x)
             (lhses-collide-p x y))
    :hints (("goal"
             :expand ((:with lhses-collide-p-open-right (lhses-collide-p x y))
                      (:with lhses-collide-p (lhses-collide-p y x))))))

  (defthm lhses-collide-p-symm-not
    (implies (not (lhses-collide-p y x))
             (not (lhses-collide-p x y)))))

(define lhs-selfcollide-p ((x lhs-p))
  (if (atom x)
      nil
    (or (lhrange-collides-with-lhs-p (car x) (cdr x))
        (lhs-selfcollide-p (cdr x))))
  ///
  (deffixequiv lhs-selfcollide-p)

  (defthm lhs-selfcollide-p-of-lhs-cons
    (equal (lhs-selfcollide-p (lhs-cons x1 x))
           (lhs-selfcollide-p (cons x1 x)))
    :hints(("Goal" :in-theory (enable lhs-cons lhrange-nextbit
                                      ranges-collide-p)
            :use ((:instance lhrange-collides-with-lhs-p-decomp
                   (w1 (lhrange->w x1)) (w2 (lhrange->w (car x)))
                   (offset (lhatom-var->rsh (lhrange->atom x1)))
                   (name (lhatom-var->name (lhrange->atom x1)))
                   (y (cdr x))))
            :expand ((lhrange-collides-with-lhs-p x1 x))))
    :otf-flg t)

  (defthm lhs-selfcollide-p-of-lhs-norm
    (equal (lhs-selfcollide-p (lhs-norm x))
           (lhs-selfcollide-p x))
    :hints(("Goal" :in-theory (enable lhs-norm))))

  (defcong lhs-norm-equiv equal (lhs-selfcollide-p x) 1
    :hints (("goal" :use ((:instance lhs-selfcollide-p-of-lhs-norm)
                          (:instance lhs-selfcollide-p-of-lhs-norm (x x-equiv)))
             :in-theory (disable lhs-selfcollide-p-of-lhs-norm)))))


(define lhs-collides-with-svtv-name-lhs-map-p ((lhs lhs-p)
                                               (x svtv-name-lhs-map-p))
  (if (atom x)
      nil
    (or (and (mbt (and (consp (car x)) (svar-p (caar x))))
             (lhses-collide-p lhs (cdar x)))
        (lhs-collides-with-svtv-name-lhs-map-p lhs (cdr x))))
  ///
  (defthm lhs-collides-with-svtv-name-lhs-map-p-of-lhs-norm
    (equal (lhs-collides-with-svtv-name-lhs-map-p (lhs-norm lhs) x)
           (lhs-collides-with-svtv-name-lhs-map-p lhs x)))

  (defcong lhs-norm-equiv equal (lhs-collides-with-svtv-name-lhs-map-p lhs x) 1
    :hints (("goal" :use ((:instance lhs-collides-with-svtv-name-lhs-map-p-of-lhs-norm)
                          (:instance lhs-collides-with-svtv-name-lhs-map-p-of-lhs-norm
                           (lhs lhs-equiv)))
             :in-theory (disable lhs-collides-with-svtv-name-lhs-map-p-of-lhs-norm))))

  (local (in-theory (enable svtv-name-lhs-map-fix))))

(define svtv-name-lhs-map-selfcollide-p ((x svtv-name-lhs-map-p))
  (if (atom x)
      nil
    (or (and (mbt (and (consp (car x)) (svar-p (caar x))))
             (or (lhs-selfcollide-p (cdar x))
                 (lhs-collides-with-svtv-name-lhs-map-p (cdar x) (cdr x))))
        (svtv-name-lhs-map-selfcollide-p (cdr x))))
  ///
  (local (in-theory (enable svtv-name-lhs-map-fix))))






(define lhs-var-distribute-value ((val 4vec-p)
                                  (v svar-p)
                                  (x lhs-p)
                                  (prev 4vec-p))
  :returns (new-val 4vec-p)
  :verify-guards :after-returns
  (b* (((when (atom x))
        (4vec-fix prev))
       ((lhrange x1) (car x))
       ((when (lhatom-case x1.atom :z))
        (lhs-var-distribute-value (4vec-rsh (2vec x1.w) val) v (cdr x) prev))
       ((lhatom-var x1.atom))
       ((unless (equal x1.atom.name (svar-fix v)))
        (lhs-var-distribute-value (4vec-rsh (2vec x1.w) val) v (cdr x) prev)))
    (4vec-part-install (2vec x1.atom.rsh)
                       (2vec x1.w)
                       (lhs-var-distribute-value (4vec-rsh (2vec x1.w) val) v (cdr x) prev)
                       val))
  ///
  (deffixequiv lhs-var-distribute-value)


  (local (defthm logapp-of-logapp-tail
           (equal (logapp w1 x (logapp w2 (logtail w1 x) y))
                  (logapp (+ (nfix w1) (nfix w2)) x y))
           :hints((bitops::logbitp-reasoning))))

  (local (defthm 4vec-concat-of-4vec-concat-rsh
           (implies (and (natp w1) (natp w2))
                    (equal (4vec-concat (2vec w1) x (4vec-concat (2vec w2) (4vec-rsh (2vec w1) x) y))
                           (4vec-concat (2vec (+ w1 w2)) x y)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-rsh 4vec-shift-core)))))

  (defthm lhs-var-distribute-value-of-lhs-cons
    (equal (lhs-var-distribute-value val v (lhs-cons x1 x) prev)
           (b* (((lhrange x1))
                (rest (lhs-var-distribute-value (4vec-rsh (2vec x1.w) val) v x prev)))
             (if (and (lhatom-case x1.atom :var)
                      (equal (lhatom-var->name x1.atom) (svar-fix v)))
                 (4vec-part-install (2vec (lhatom-var->rsh x1.atom))
                                    (2vec x1.w)
                                    rest
                                    val)
               rest)))
    :hints(("Goal" :in-theory (e/d (lhs-cons
                                    lhrange-nextbit
                                    4vec-part-install)))))

  (defthm lhs-var-distribute-value-of-lhs-norm
    (equal (lhs-var-distribute-value val v (lhs-norm x) prev)
           (lhs-var-distribute-value val v x prev))
    :hints(("Goal" :in-theory (enable lhs-norm))))

  (defcong lhs-norm-equiv equal (lhs-var-distribute-value val v x prev) 3
    :hints (("goal" :use ((:instance lhs-var-distribute-value-of-lhs-norm)
                          (:instance lhs-var-distribute-value-of-lhs-norm (x x-equiv)))
             :in-theory (disable lhs-var-distribute-value-of-lhs-norm)))))







(define svtv-name-lhs-map-empty-lhs-p ((x lhs-p)
                                       (map svtv-name-lhs-map-p))
  :prepwork ((local (in-theory (disable hons-assoc-equal
                                        HONS-ASSOC-EQUAL-OF-SVTV-NAME-LHS-MAP-FIX))))
  (if (atom x)
      t
    (and (b* (((lhrange x1) (car x)))
           (lhatom-case x1.atom
             :z t
             :var (lhs-empty-range-p x1.w x1.atom.rsh
                                     (cdr (hons-get x1.atom.name (svtv-name-lhs-map-fix map))))))
         (svtv-name-lhs-map-empty-lhs-p (cdr x) map))))


(local (defthm 4vec-rsh-of-4vec-rsh
         (implies (and (2vec-p sh1) (2vec-p sh2)
                       (natp (2vec->val sh1))
                       (natp (2vec->val sh2)))
                  (equal (4vec-rsh sh1 (4vec-rsh sh2 x))
                         (4vec-rsh (2vec (+ (2vec->val sh1) (2vec->val sh2))) x)))
         :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core)))))






(local
 (defthm 4vec-rsh-of-4vec-bit?!
   (implies (and (2vec-p sh)
                 (<= 0 (2vec->val sh)))
            (equal (4vec-rsh sh (4vec-bit?! test x y))
                   (4vec-bit?! (4vec-rsh sh test)
                               (4vec-rsh sh x)
                               (4vec-rsh sh y))))
   :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core 4vec-bit?! 4vec-bitmux 4vec-1mask)))))

(local
 (defthm 4vec-rsh-of-2vec
   (implies (and (2vec-p sh)
                 (<= 0 (2vec->val sh)))
            (equal (4vec-rsh sh (2vec x))
                   (2vec (logtail (2vec->val sh) x))))
   :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core)))))

(local
 (defsection 4vec-lemmas

   (defthm logand-of-logapp
     (equal (logand (logapp w x y) z)
            (logapp w (logand x z)
                    (logand y (logtail w z))))
     :hints ((acl2::logbitp-reasoning)))

   (defthm logior-of-logapp
     (equal (logior (logapp w x y) z)
            (logapp w (logior x z)
                    (logior y (logtail w z))))
     :hints ((acl2::logbitp-reasoning)))

   (defthm logapp-of-logand-logapp-same
     (equal (logapp w (logand x (logapp w x1 y1)) z1)
            (logapp w (logand x x1) z1))
     :hints ((acl2::logbitp-reasoning)))

   (defthm logapp-of-logior-logapp-same
     (equal (logapp w (logior x (logapp w x1 y1)) z1)
            (logapp w (logior x x1) z1))
     :hints ((acl2::logbitp-reasoning)))

   (defthm lognot-of-logapp
     (equal (lognot (logapp w x y))
            (logapp w (lognot x) (lognot y)))
     :hints ((acl2::logbitp-reasoning)))

   (defthm 4vec-bit?!-0
     (equal (4vec-bit?! 0 x y)
            (4vec-fix y))
     :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bitmux))))

   (defthm 4vec-bit?!-neg1
     (equal (4vec-bit?! -1 x y)
            (4vec-fix x))
     :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bitmux))))


   ;;  (defthm 4vec-bitand-of-2vec-logapp
   ;;          (equal (4vec-bitand (2vec (logapp w x y)) z)
   ;;                 (4vec-concat (2vec (nfix w))
   ;;                              (4vec-bitand (2vec x) z)
   ;;                              (4vec-bitand (2vec y) (4vec-rsh (2vec (nfix w)) z))))
   ;;          :hints(("Goal" :in-theory (e/d (4vec-bitand 3vec-bitand 3vec-fix 4vec-concat 4vec-rsh 4vec-shift-core)
   ;;                                         (acl2::commutativity-of-logand
   ;;                                          acl2::commutativity-of-logior))))))

   ;; (local (defthm 4vec-bitand-0
   ;;          (equal (4vec-bitand 0 x) 0)
   ;;          :hints(("Goal" :in-theory (enable 4vec-bitand 3vec-bitand 3vec-fix)))))

   (defthm 4vec-bit?!-of-2vec-logapp
     (equal (4vec-bit?! (2vec (logapp w x y)) then else)
            (4vec-concat (2vec (nfix w))
                         (4vec-bit?! (2vec x) then else)
                         (4vec-bit?! (2vec y) (4vec-rsh (2vec (nfix w)) then) (4vec-rsh (2vec (nfix w)) else))))
     :hints(("Goal" :in-theory (e/d (4vec-bit?! 4vec-concat 4vec-rsh 4vec-shift-core 4vec-bitmux 4vec-1mask logite)
                                    (acl2::commutativity-of-logand
                                     acl2::commutativity-of-logior)))))))


(defthm lhs-width-of-lhs-cons-strong
  (equal (lhs-width (lhs-cons x y))
         (lhs-width (cons x y)))
  :hints(("Goal" :in-theory (enable lhs-width lhs-cons))))


(defthm lhs-width-of-lhs-rsh-strong
  (equal (lhs-width (lhs-rsh n x))
         (nfix (- (lhs-width x) (nfix n))))
  :hints(("Goal" :in-theory (enable lhs-rsh lhs-width))))


(define lhs-join ((x lhs-p)
                  (y lhs-p))
  ;; Returns a new lhs which has all of x's non-z ranges, and any of y's non-z ranges whereever x has zs.
  :returns (join lhs-p)
  :measure (+ (lhs-width x) (lhs-width y))
  :hints (("goal" :expand ((lhs-width x) (lhs-width y))))
  :verify-guards nil
  (b* (((when (atom x)) (lhs-fix y))
       ((when (atom y)) (lhs-fix x))
       ((lhrange x1) (car x))
       ((lhrange y1) (car y))
       (w (min x1.w y1.w))
       (atom (lhatom-case x1.atom
               :var x1.atom
               :z y1.atom)))
    (lhs-cons (lhrange w atom)
              (lhs-join (lhs-rsh w x)
                        (lhs-rsh w y))))
  ///
  (local (defthm 4vec-bit?!-of-4vec-concat
           (implies (natp w)
                    (equal (4vec-bit?! test (4vec-concat (2vec w) x y) z)
                           (4vec-concat (2vec w)
                                        (4vec-bit?! test x z)
                                        (4vec-bit?! (4vec-rsh (2vec w) test)
                                                    y
                                                    (4vec-rsh (2vec w) z)))))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-rsh 4vec-shift-core 4vec-bit?! 4vec-bitmux 4vec-1mask))
                  (bitops::logbitp-reasoning))))

  (local (defthm 4vec-concat-of-4vec-bit?!-ash
           (implies (natp w)
                    (equal (4vec-concat (2vec w)
                                        (4vec-bit?! (2vec (ash test w)) x y)
                                        z)
                           (4vec-concat (2vec w) y z)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-bit?! 4vec-bitmux 4vec-1mask))
                  (bitops::logbitp-reasoning))))

  ;; (local (defthm 4vec-rsh-of-x
  ;;          (implies (natp w)
  ;;                   (equal (4vec-rsh (2vec w) (4vec-x))
  ;;                          (4vec-x)))
  ;;          :hints(("Goal" :in-theory (enable 4vec-rsh 4vec-shift-core)))))

  (local (defthm 4vec-bit?!-varmask-eval
           (equal (4vec-bit?! (2vec (lhs-varmask x)) (lhs-eval-x x env) (4vec-x))
                  (lhs-eval-x x env))
           :hints(("Goal" :in-theory (enable lhs-eval-x lhs-varmask bool->bit lhatom-eval-x)))))

  (local (defthm 4vec-concat-rsh-of-4vec-concat-rsh
           (implies (and (natp w1) (natp w2) (natp sh))
                    (equal (4vec-concat (2vec w1)
                                        (4vec-rsh (2vec sh) x)
                                        (4vec-concat (2vec w2) (4vec-rsh (2vec (+ w1 sh)) x) y))
                           (4vec-concat (2vec (+ w1 w2)) (4vec-rsh (2vec sh) x) y)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-rsh 4vec-shift-core)))))

  (defret eval-of-lhs-join
    (equal (lhs-eval-x join env)
           (4vec-bit?! (2vec (lhs-varmask x)) (lhs-eval-x x env) (lhs-eval-x y env)))
    :hints(("Goal" :in-theory (enable lhs-eval-x bool->bit lhatom-eval-x)
            :induct <call>
            :expand ((lhs-eval-x x env)
                     (lhs-eval-x y env)
                     (lhs-varmask x)))))

  (verify-guards lhs-join))

;; (define lhs-invert-var ((v svar-p)
;;                         (target svar-p)
;;                         (offset natp)
;;                         (x lhs-p))
;;   ;; This inverts references to v within x, an LHS assumed equivalent to target at offset.
;;   ;; E.g., if x is { v[5:3], w[2:0], v[8:7] } then this returns { target[1:0], 1'bz, target[7:5], 3'bz }
;;   ;; -- because v[8:7] corresponds to target[1:0] and v[5:3] corresponds to target[7:5]
;;   ;; (systemverilog syntax above, so lsb-last).
;;   :returns (inv-lhs lhs-p)
;;   :verify-guards nil
;;   (b* (((when (atom x)) nil)
;;        ((lhrange x1) (car x))
;;        ((unless (and (lhatom-case x1.atom :var)
;;                      (equal (lhatom-var->name x1.atom) (svar-fix v))))
;;         (lhs-invert-var v target (+ (lnfix offset) x1.w) (cdr x)))
;;        (rest (lhs-invert-var v target (+ (lnfix offset) x1.w) (cdr x)))
;;        (rsh (lhatom-var->rsh x1.atom)))
;;     (lhs-concat rsh rest (lhs-cons (lhrange x1.w (lhatom-var target offset))
;;                                    (lhs-rsh (+ x1.w rsh) rest))))
;;   ///
;;   (verify-guards lhs-invert-var)

;;   (defret lhs-varmask-of-<fn>
;;     (equal (lhs-varmask inv-lhs)
;;            (var-lhs-mask v x))
;;     :hints(("Goal" :in-theory (e/d (lhs-varmask var-lhs-mask
;;                                                 bitops::part-install-in-terms-of-logapp)
;;                                    (bitops::part-install)))))

;;   (defret eval-of-<fn>
;;     (equal (lhs-eval-x inv-lhs env)
;;            (4vec-bit?! (2vec (var-lhs-mask v x))
;;                        (lhs-var-distribute-value
;;                         (4vec-rsh (2vec (nfix offset)) (svex-env-lookup target env))
;;                         v x)
;;                        (4vec-x)))
;;     :hints(("Goal" :in-theory (e/d (lhs-var-distribute-value
;;                                     var-lhs-mask
;;                                     lhs-eval-x
;;                                     4vec-part-install
;;                                     bitops::part-install-in-terms-of-logapp)
;;                                    (bitops::part-install))))))


(define lhs-var/idx-find ((var svar-p)
                          (idx natp)
                          (x lhs-p))
  :returns (var-index maybe-natp :rule-classes :type-prescription)
  ;; Finds the bit index of the given LHS that corresponds to bit idx of var.
  (b* (((when (atom x)) nil)
       ((lhrange x1) (car x))
       ((when (lhatom-case x1.atom
                  :var
                  (and (equal x1.atom.name (svar-fix var))
                       (<= x1.atom.rsh (lnfix idx))
                       (< (lnfix idx) (+ x1.atom.rsh x1.w)))
                  :z nil))
        (- (lnfix idx) (lhatom-var->rsh x1.atom)))
       (rest (lhs-var/idx-find var idx (cdr x)))
       ((unless rest) nil))
    (+ rest x1.w))
  ///
  (defret <fn>-correct
    (implies var-index
             (equal (lhs-bitproj var-index x)
                    (lhbit-var var idx)))
    :hints(("Goal" :in-theory (enable lhatom-bitproj)
            :induct <call>
            :expand ((:free (idx) (lhs-bitproj idx x))))))

  (defret <fn>-<-width
    (implies var-index
             (< var-index (lhs-width x)))
    :hints(("Goal" :in-theory (enable lhs-width)))
    :rule-classes :linear))





(define lhs-accumulate-name-lhs-map-inverse ((dom-var svar-p)
                                             (offset natp) ;; offset into domain var corrsponding to lhs
                                             (lhs lhs-p)
                                             (inverse-acc svtv-name-lhs-map-p))
  :returns (mv (collision)
               (new-inverse svtv-name-lhs-map-p))
  :verify-guards nil
  (b* ((inverse-acc (svtv-name-lhs-map-fix inverse-acc))
       ((when (atom lhs))
        (mv nil inverse-acc))
       ((lhrange l1) (car lhs)))
    (lhatom-case l1.atom
      :z (lhs-accumulate-name-lhs-map-inverse dom-var (+ (lnfix offset) l1.w) (cdr lhs) inverse-acc)
      :var (b* (((mv rest-collision rest-inverse)
                 (lhs-accumulate-name-lhs-map-inverse dom-var (+ (lnfix offset) l1.w) (cdr lhs) inverse-acc))
                (entry (cdr (hons-get l1.atom.name rest-inverse)))
                (range (make-lhrange :w l1.w :atom (make-lhatom-var :name dom-var :rsh offset)))
                ((mv collision new-entry) (lhs-add-name-lhs-map-inverse range l1.atom.rsh entry))
                (inverse-acc (hons-acons l1.atom.name new-entry rest-inverse)))
             (mv (or collision rest-collision) inverse-acc))))
  ///
  (verify-guards lhs-accumulate-name-lhs-map-inverse)

  (defret lhs-empty-range-p-of-<fn>
    (implies (svar-p name)
             (iff (lhs-empty-range-p w rsh (cdr (hons-assoc-equal name new-inverse)))
                  (and (lhs-empty-range-p w rsh (cdr (hons-assoc-equal name inverse-acc)))
                       (not (lhrange-collides-with-lhs-p
                             (lhrange w (lhatom-var name rsh)) lhs)))))
    :hints(("Goal" :in-theory (enable lhrange-collides-with-lhs-p))))

  (defret collision-of-<fn>
    (iff collision
         (or (lhs-selfcollide-p lhs)
             (not (svtv-name-lhs-map-empty-lhs-p lhs inverse-acc))))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-empty-lhs-p
                                      lhs-selfcollide-p))))

  (defret svtv-name-lhs-map-empty-lhs-p-of-<fn>
    (iff (svtv-name-lhs-map-empty-lhs-p lhs2 new-inverse)
         (and (svtv-name-lhs-map-empty-lhs-p lhs2 inverse-acc)
              (not (lhses-collide-p lhs2 lhs))))
    :hints(("Goal" :in-theory (enable (:i lhses-collide-p))
            :induct (lhses-collide-p lhs2 lhs)
            :expand ((lhses-collide-p lhs2 lhs)
                     (:free (map) (svtv-name-lhs-map-empty-lhs-p lhs2 map))))
           (and stable-under-simplificationp
                '(:cases ((lhatom-case (lhrange->atom (car lhs2)) :var))))))

  (local (defthm logand-of-logapp
           (equal (logand (logapp w x y) z)
                  (logapp w (logand x z)
                          (logand y (logtail w z))))
           :hints ((acl2::logbitp-reasoning))))

  (local (defthm logior-of-logapp
           (equal (logior (logapp w x y) z)
                  (logapp w (logior x z)
                          (logior y (logtail w z))))
           :hints ((acl2::logbitp-reasoning))))

  (local (defthm logapp-of-logand-logapp-same
           (equal (logapp w (logand x (logapp w x1 y1)) z1)
                  (logapp w (logand x x1) z1))
           :hints ((acl2::logbitp-reasoning))))

  (local (defthm logapp-of-logior-logapp-same
           (equal (logapp w (logior x (logapp w x1 y1)) z1)
                  (logapp w (logior x x1) z1))
           :hints ((acl2::logbitp-reasoning))))

  (local (defthm lognot-of-logapp
           (equal (lognot (logapp w x y))
                  (logapp w (lognot x) (lognot y)))
           :hints ((acl2::logbitp-reasoning))))

  (local (defthm 4vec-bit?!-0
           (equal (4vec-bit?! 0 x y)
                  (4vec-fix y))
           :hints(("Goal" :in-theory (enable 4vec-bit?!)))))

  (local (defthm 4vec-bit?!-neg1
           (equal (4vec-bit?! -1 x y)
                  (4vec-fix x))
           :hints(("Goal" :in-theory (enable 4vec-bit?!)))))


  ;; (local (defthm 4vec-bitand-of-2vec-logapp
  ;;          (equal (4vec-bitand (2vec (logapp w x y)) z)
  ;;                 (4vec-concat (2vec (nfix w))
  ;;                              (4vec-bitand (2vec x) z)
  ;;                              (4vec-bitand (2vec y) (4vec-rsh (2vec (nfix w)) z))))
  ;;          :hints(("Goal" :in-theory (e/d (4vec-bitand 3vec-bitand 3vec-fix 4vec-concat 4vec-rsh 4vec-shift-core)
  ;;                                         (acl2::commutativity-of-logand
  ;;                                          acl2::commutativity-of-logior))))))

  ;; (local (defthm 4vec-bitand-0
  ;;          (equal (4vec-bitand 0 x) 0)
  ;;          :hints(("Goal" :in-theory (enable 4vec-bitand 3vec-bitand 3vec-fix)))))

  (local (defthm 4vec-bit?!-of-2vec-logapp
           (equal (4vec-bit?! (2vec (logapp w x y)) then else)
                  (4vec-concat (2vec (nfix w))
                               (4vec-bit?! (2vec x) then else)
                               (4vec-bit?! (2vec y) (4vec-rsh (2vec (nfix w)) then) (4vec-rsh (2vec (nfix w)) else))))
           :hints(("Goal" :in-theory (e/d (4vec-bit?! 4vec-concat 4vec-rsh 4vec-shift-core)
                                          (acl2::commutativity-of-logand
                                           acl2::commutativity-of-logior))))))

  (local (defthm svex-env-lookup-cons
           (equal (svex-env-lookup v (cons (cons var val) rest))
                  (if (equal (svar-fix v) var)
                      (4vec-fix val)
                    (svex-env-lookup v rest)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))


  (local (defthm lhs-eval-x-of-non-colliding-acons-part-install-lemma
           (implies (and (not (lhrange-collides-with-lhs-p range lhs))
                         (lhatom-case (lhrange->atom range) :var))
                    (equal (lhs-eval-x lhs (Cons (cons (lhatom-var->name (lhrange->atom range))
                                                       (4vec-part-install (2vec (lhatom-var->rsh (lhrange->atom range)))
                                                                          (2vec (lhrange->w range))
                                                                          (svex-env-lookup
                                                                           (lhatom-var->name (lhrange->atom range))
                                                                           rest)
                                                                          new))
                                                 rest))
                           (lhs-eval-x lhs rest)))
           :hints(("Goal" :in-theory (enable (:i lhs-eval-x) lhatom-eval-x 4vec-part-install ranges-collide-p)
                   :induct (lhs-eval-x lhs rest)
                   :expand ((:free (env) (lhs-eval-x lhs env))
                            (lhrange-collides-with-lhs-p range lhs))))))

  (local (defthm lhs-eval-x-of-non-colliding-acons-part-install
           (implies (and (not (lhrange-collides-with-lhs-p range lhs))
                         (lhatom-case (lhrange->atom range) :var)
                         (equal prev (svex-env-lookup (lhatom-var->name (lhrange->atom range))
                                                      rest)))
                    (equal (lhs-eval-x lhs (Cons (cons (lhatom-var->name (lhrange->atom range))
                                                       (4vec-part-install (2vec (lhatom-var->rsh (lhrange->atom range)))
                                                                          (2vec (lhrange->w range))
                                                                          prev
                                                                          new))
                                                 rest))
                           (lhs-eval-x lhs rest)))
           :hints(("Goal" :in-theory (enable (:i lhs-eval-x) lhatom-eval-x 4vec-part-install ranges-collide-p)
                   :induct (lhs-eval-x lhs rest)
                   :expand ((:free (env) (lhs-eval-x lhs env))
                            (lhrange-collides-with-lhs-p range lhs))))))


  (local (defthm lhs-eval-x-of-nil
           (Equal (lhs-eval-x nil env) (4vec-x))
           :hints(("Goal" :in-theory (enable lhs-eval-x)))))

  (local (defthm svex-env-lookup-of-svtv-name-lhs-map-eval-x
           (equal (svex-env-lookup var (svtv-name-lhs-map-eval-x map env))
                  (lhs-eval-x (cdr (hons-assoc-equal (svar-fix var) map)) env))
           :hints(("Goal" :in-theory (enable svex-env-lookup
                                             svtv-name-lhs-map-eval-x)))))

  (defret eval-lhs-of-lhs-accumulate-name-lhs-map-inverse
    (implies (and (not (lhs-selfcollide-p lhs))
                  (svtv-name-lhs-map-empty-lhs-p lhs inverse-acc))
             (equal (lhs-eval-x lhs (svtv-name-lhs-map-eval-x new-inverse env))
                    (4vec-bit?! (2vec (lhs-varmask lhs))
                                (4vec-rsh (2vec (nfix offset)) (svex-env-lookup dom-var env))
                                (4vec-x))))
    :hints (("Goal" :induct <call>
             :in-theory (e/d (lhatom-eval-x)
                             (BITOPS::LOGAPP-OF-I-0))
             :expand (<call>
                      (:free (env) (lhs-eval-x lhs env))
                      (lhs-varmask lhs)
                      (lhs-selfcollide-p lhs)
                      (:free (inverse-acc) (svtv-name-lhs-map-empty-lhs-p lhs inverse-acc))
                      (:free (a b env) (svtv-name-lhs-map-eval-x (cons a b) env))))
            (and stable-under-simplificationp
                 '(:in-theory (enable 4vec-part-install)))))

  (defret eval-x-lookup-preserved-when-not-lhrange-collides-with-lhs-p
    (implies (and (not (lhrange-collides-with-lhs-p range lhs))
                  (lhatom-case (lhrange->atom range) :var))
             (equal (4vec-concat (2vec (lhrange->w range))
                                 (4vec-rsh (2vec (lhatom-var->rsh (lhrange->atom range)))
                                           (lhs-eval-x (cdr (hons-assoc-equal
                                                             (lhatom-var->name (lhrange->atom range))
                                                             new-inverse))
                                                       env))
                                 rest)
                    (4vec-concat (2vec (lhrange->w range))
                                 (4vec-rsh (2vec (lhatom-var->rsh (lhrange->atom range)))
                                           (lhs-eval-x (cdr (hons-assoc-equal
                                                             (lhatom-var->name (lhrange->atom range))
                                                             (svtv-name-lhs-map-fix inverse-acc)))
                                                       env))
                                 rest)))
    :hints(("Goal"
            :induct <call>
            :expand ((lhrange-collides-with-lhs-p range lhs))
            :in-theory (enable ranges-collide-p
                               4vec-part-install))))

  (defret eval-lhs-preserved-of-lhs-accumulate-name-lhs-map-inverse
    (implies (not (lhses-collide-p lhs2 lhs))
             (equal (lhs-eval-x lhs2 (svtv-name-lhs-map-eval-x new-inverse env))
                    (lhs-eval-x lhs2 (svtv-name-lhs-map-eval-x inverse-acc env))))
    :hints(("Goal" :induct (lhses-collide-p lhs2 lhs)
            :expand ((:Free (env) (lhs-eval-x lhs2 env))
                     (lhses-collide-p lhs2 lhs))
            :in-theory (enable (:i lhses-collide-p) lhatom-eval-x))))

  (defret eval-map-preserved-of-<fn>
    (implies (not (lhs-collides-with-svtv-name-lhs-map-p lhs map))
             (equal (svtv-name-lhs-map-eval-x map (svtv-name-lhs-map-eval-x new-inverse env))
                    (svtv-name-lhs-map-eval-x map (svtv-name-lhs-map-eval-x inverse-acc env))))
    :hints(("Goal" :induct (len map)
            :expand ((:free (env) (svtv-name-lhs-map-eval-x map env))
                     (lhs-collides-with-svtv-name-lhs-map-p lhs map)))))

  (defret keys-of-<fn>
    (equal (alist-keys new-inverse)
           (append (lhs-vars lhs) (alist-keys (svtv-name-lhs-map-fix inverse-acc))))
    :hints(("Goal" :in-theory (enable lhs-vars lhatom-vars alist-keys))))


  ;; (LHATOM-EVAL-X (LHATOM-VAR DOM-VAR OFFSET)
  ;;                ENV)
  ;; = (4VEC-RSH (2VEC (LHATOM-VAR->RSH (LHRANGE->ATOM (CAR LHS))))
  ;;             ???)

  (local (defthm logapp-logior-logand-logapp-lemma
           (equal (LOGAPP W
                          (LOGIOR a
                                  (LOGAND b c
                                          (LOGAPP W d e)))
                          f)
                  (LOGAPP W
                          (LOGIOR a
                                  (LOGAND b c d))
                          f))
           :hints ((bitops::logbitp-reasoning))))

  (local (defthm 4vec-concat-of-4vec-bit?!-concat-same
           (implies (natp w)
                    (equal (4vec-concat (2vec w) (4vec-bit?! test (4vec-concat (2vec w) x y) z1) z2)
                           (4vec-concat (2vec w) (4vec-bit?! test x z1) z2)))
           :hints(("Goal" :in-theory (enable 4vec-concat 4vec-bit?! 4vec-bitmux 4vec-1mask logite)))))

  (local
   (defthm 4vec-rsh-of-4vec-bit?!-free
     (implies (and (equal xx (4vec-bit?! test x y))
                   (2vec-p sh)
                   (<= 0 (2vec->val sh)))
              (equal (4vec-rsh sh xx)
                     (4vec-bit?! (4vec-rsh sh test)
                                 (4vec-rsh sh x)
                                 (4vec-rsh sh y))))))

  (defret lhs-eval-x-of-lookup-of-<fn>
    (implies (svar-p v)
             (equal (lhs-eval-x (cdr (hons-assoc-equal v new-inverse)) env)
                    ;; (4vec-bit?! (2vec (var-lhs-mask v lhs))
                    ;; (4vec-rsh (2vec (nfix offset)) (svex-env-lookup dom-var env))
                    (lhs-var-distribute-value (4vec-rsh (2vec (nfix offset)) (svex-env-lookup dom-var env))
                                              v lhs
                                              (lhs-eval-x (cdr (hons-assoc-equal v inverse-acc)) env))))
    :hints(("Goal" :in-theory (e/d (var-lhs-mask
                                    lhatom-eval-x
                                    lhs-var-distribute-value
                                    4vec-part-install
                                    bitops::part-install-in-terms-of-logapp)
                                   (bitops::part-install)))))


  (defret lhs-varmask-of-lookup-of-<fn>
    (implies (svar-p v)
             (equal (lhs-varmask (cdr (hons-assoc-equal v new-inverse)))
                    (logior (var-lhs-mask v lhs)
                            (lhs-varmask (cdr (hons-assoc-equal v inverse-acc))))))
    :hints(("Goal" :in-theory (e/d (var-lhs-mask
                                    bitops::part-install-in-terms-of-logapp)
                                   (bitops::part-install)))))


  (defret svtv-name-lhs-map-vars-of-<fn>
    (implies (and (not (member v (svtv-name-lhs-map-vars inverse-acc)))
                  (not (equal v (svar-fix dom-var))))
             (not (member v (svtv-name-lhs-map-vars new-inverse))))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-vars
                                      lhatom-vars))))

  (defret lhs-bitproj-of-<fn>
    (implies (svar-p v)
             (equal (lhs-bitproj n (cdr (hons-assoc-equal v new-inverse)))
                    (let ((idx (lhs-var/idx-find v n lhs)))
                      (if idx
                          (lhbit-var dom-var (+ (nfix offset) idx))
                        (lhs-bitproj n (cdr (hons-assoc-equal v inverse-acc)))))))
    :hints(("Goal" :in-theory (enable lhs-var/idx-find lhatom-bitproj)))))



(define svtv-name-lhs-map-var/idx-find ((var svar-p)
                                        (idx natp)
                                        (x svtv-name-lhs-map-p))
  :returns (lhbit lhbit-p)
  (if (atom x)
      (lhbit-z)
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (b* ((n (lhs-var/idx-find var idx (cdar x))))
          (if n
              (lhbit-var (caar x) n)
            (svtv-name-lhs-map-var/idx-find var idx (cdr x))))
      (svtv-name-lhs-map-var/idx-find var idx (cdr x))))
  ///
  (defret <fn>-lookup-lemma
    (implies (lhbit-case lhbit :var)
             (hons-assoc-equal (lhbit-var->name lhbit)
                               x))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix))))

  (defret <fn>-correct
    (implies (and (lhbit-case lhbit :var)
                  (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix x))))
             (equal (lhs-bitproj (lhbit-var->idx lhbit)
                                 (cdr (hons-assoc-equal (lhbit-var->name lhbit) x)))
                    (lhbit-var var idx)))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                      alist-keys))))

  (defret <fn>-lookup-consp
    (implies (and (lhbit-case lhbit :var)
                  (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix x))))
             (consp (cdr (hons-assoc-equal (lhbit-var->name lhbit) x))))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                      hons-assoc-equal
                                      alist-keys)
            :induct t)
           (and stable-under-simplificationp
                '(:expand ((lhs-var/idx-find var idx (cdr (car x))))))))

  (defret <fn>-lookup-width
    (implies (and (lhbit-case lhbit :var)
                  (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix x))))
             (< (lhbit-var->idx lhbit)
                (lhs-width (cdr (hons-assoc-equal (lhbit-var->name lhbit) x)))))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                      hons-assoc-equal
                                      alist-keys)))
    :rule-classes :linear)
  
  (local (in-theory (enable svtv-name-lhs-map-fix))))



(define svtv-name-lhs-map-extract-env ((x svtv-name-lhs-map-p)
                                       (env svex-env-p))
  :returns (new-env svex-env-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (cons (cons (caar x)
                    (4vec-bit?! (2vec (lhs-varmask (cdar x)))
                                (svex-env-lookup (caar x) env)
                                (4vec-x)))
              (svtv-name-lhs-map-extract-env (cdr x) env))
      (svtv-name-lhs-map-extract-env (cdr x) env)))
  ///
  (defret svex-env-lookup-of-<fn>
    (equal (svex-env-lookup k new-env)
           (b* ((look (hons-assoc-equal (svar-fix k) (svtv-name-lhs-map-fix x))))
             (if look
                 (4vec-bit?! (2vec (lhs-varmask (cdr look)))
                             (svex-env-lookup k env)
                             (4vec-x))
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup))))

  (local (in-theory (enable svtv-name-lhs-map-fix))))




(local
 (encapsulate nil

   (local
    (defthm 4vec-rsh-of-4vec-bit?!-free
      (implies (and (equal xx (4vec-bit?! test x y))
                    (2vec-p sh)
                    (<= 0 (2vec->val sh)))
               (equal (4vec-rsh sh xx)
                      (4vec-bit?! (4vec-rsh sh test)
                                  (4vec-rsh sh x)
                                  (4vec-rsh sh y))))))

   (defthm lhs-mask-distribute-value-of-lhs-eval-zx
     (Equal (lhs-var-distribute-value (lhs-eval-zx x env) v x prev)
            (4vec-bit?! (2vec (var-lhs-mask v x))
                        (svex-env-lookup v env)
                        prev))
         :hints (("goal" :expand ((var-lhs-mask v x)
                                  (lhs-eval-zx x env)
                                  (:free (val) (lhs-var-distribute-value val v x prev)))
                  :in-theory (e/d (bitops::part-install-in-terms-of-logapp
                                   4vec-part-install
                                   lhatom-eval-zero
                                   (:i var-lhs-mask))
                                  (bitops::part-install))
                  :induct (var-lhs-mask v x))))))

(define svtv-name-lhs-map-var-inverse-eval-x ((v svar-p)
                                              (x svtv-name-lhs-map-p)
                                              (env svex-env-p))
  :returns (val 4vec-p)
  :verify-guards nil
  (if (atom x)
      (4vec-x)
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (b* ((rest (svtv-name-lhs-map-var-inverse-eval-x v (cdr x) env)))
          (lhs-var-distribute-value (svex-env-lookup (caar x) env)
                                            v (cdar x) rest))
      (svtv-name-lhs-map-var-inverse-eval-x v (cdr x) env)))
  ///
  (verify-guards svtv-name-lhs-map-var-inverse-eval-x)

  (local (in-theory (enable svtv-name-lhs-map-fix))))


(define svtv-name-lhs-map-inverse ((x svtv-name-lhs-map-p))
  :returns (mv collision
               (inverse svtv-name-lhs-map-p))
  (if (Atom x)
      (mv nil nil)
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (b* (((mv rest-collision rest)
              (svtv-name-lhs-map-inverse (cdr x)))
             ((mv collision1 inverse)
              (lhs-accumulate-name-lhs-map-inverse
               (caar x) 0 (cdar x)
               rest)))
          (mv (or collision1 rest-collision) inverse))
      (svtv-name-lhs-map-inverse (cdr x))))
  ///
  (deffixequiv svtv-name-lhs-map-inverse
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix))))

  (defret svtv-name-lhs-map-empty-lhs-p-of-<fn>
    (iff (svtv-name-lhs-map-empty-lhs-p lhs inverse)
         (not (lhs-collides-with-svtv-name-lhs-map-p lhs x)))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-empty-lhs-p
                                      lhs-collides-with-svtv-name-lhs-map-p))))

  (defret collision-of-<fn>
    (iff collision
         (svtv-name-lhs-map-selfcollide-p x))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-selfcollide-p))))

  (defret eval-of-x-under-<fn>
    (implies (not (svtv-name-lhs-map-selfcollide-p x))
             (equal (svtv-name-lhs-map-eval-x x (svtv-name-lhs-map-eval-x inverse env))
                    (svtv-name-lhs-map-extract-env x env)))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-extract-env
                                      svtv-name-lhs-map-selfcollide-p
                                      svtv-name-lhs-map-eval-x))))

  (defret keys-of-<fn>
    (equal (alist-keys inverse)
           (svtv-name-lhs-map-vars x))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-vars))))


  (defret vars-of-<fn>
    (implies (not (hons-assoc-equal v (svtv-name-lhs-map-fix x)))
             (not (member v (svtv-name-lhs-map-vars inverse))))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-fix
                                      svtv-name-lhs-map-vars))))

  (local (defret svtv-name-lhs-map-eval-x-of-cons-env
           (implies (not (hons-assoc-equal var (svtv-name-lhs-map-fix x)))
                    (equal (svtv-name-lhs-map-eval-x inverse (cons (cons var val) env))
                           (svtv-name-lhs-map-eval-x inverse env)))))


  (local (defthmd lookup-in-svtv-name-lhs-map-when-not-svar-p
           (implies (and (not (svar-p v))
                         (svtv-name-lhs-map-p x))
                    (not (hons-assoc-equal v x)))))

  (local (defret lhs-eval-x-lookup-of-cons-env
           (implies (not (hons-assoc-equal var (svtv-name-lhs-map-fix x)))
                    (equal (lhs-eval-x (cdr (hons-assoc-equal v inverse)) (cons (cons var val) env))
                           (lhs-eval-x (cdr (hons-assoc-equal v inverse)) env)))
           :hints-sub-returnnames t
           :hints (("goal" :use ((:instance svex-env-lookupp-of-svtv-name-lhs-map-eval-x
                                  (var v)
                                  (x inverse)
                                  (env env))
                                 (:instance svex-env-lookupp-of-svtv-name-lhs-map-eval-x
                                  (var v)
                                  (x inverse)
                                  (env (cons (cons var val) env))))
                    :in-theory (e/d (lookup-in-svtv-name-lhs-map-when-not-svar-p)
                                    (svex-env-lookupp-of-svtv-name-lhs-map-eval-x <fn>))
                    :cases ((svar-p v))
                    :do-not-induct t))))


  (local (defthm svex-env-lookup-of-cons
           (equal (svex-env-lookup v1 (cons (cons v2 val) x))
                  (if (equal (svar-fix v1) v2)
                      (4vec-fix val)
                    (svex-env-lookup v1 x)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))


  ;; (defret lhs-varmask-lookup-of-<fn>
  ;;   (equal (lhs-varmask (cdr (hons-assoc-equal v inverse)))

  (local (defthm 4vec-bit?!-0
           (equal (4vec-bit?! 0 x y) (4vec-fix y))
           :hints(("Goal" :in-theory (enable 4vec-bit?!)))))


  (local (defthm 4vec-bit?!-of-4vec-bit?!-same
           (equal (4vec-bit?! mask (4vec-bit?! mask x y) z)
                  (4vec-bit?! mask x z))
           :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bitmux))
                  (bitops::logbitp-reasoning)
                  (and stable-under-simplificationp
                       '(:in-theory (enable b-ite))))))


  (local (defthm 4vec-bit?!-of-else-4vec-bit?!-same-thm
           (equal (4vec-bit?! (2vec test1) then (4vec-bit?! (2vec test2) then else))
                  (4vec-bit?! (2vec (logior test1 test2)) then else))
           :hints(("Goal" :in-theory (enable 4vec-bit?! 4vec-bitmux 4vec-1mask))
                  (bitops::logbitp-reasoning)
                  (and stable-under-simplificationp
                       '(:in-theory (enable b-ite))))))

  (defret eval-<fn>-of-lookup
    (implies (and (not (svtv-name-lhs-map-selfcollide-p x))
                  (svar-p v)
                  (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix x))))
             (equal (lhs-eval-x (cdr (hons-assoc-equal v inverse)) (svtv-name-lhs-map-eval x env))
                    (4vec-bit?! (2vec (lhs-varmask (cdr (hons-assoc-equal v inverse))))
                                (svex-env-lookup v env)
                                (4vec-x))))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-extract-env
                                      svtv-name-lhs-map-fix
                                      alist-keys
                                      svtv-name-lhs-map-selfcollide-p
                                      svtv-name-lhs-map-eval-x
                                      svtv-name-lhs-map-eval)
            :induct t)
           (and stable-under-simplificationp
                (eq (caar (last clause)) 'svex-envs-similar)
                `(:expand (,(car (last clause)))))))


  (defret eval-<fn>-of-eval
    (implies (and (not (svtv-name-lhs-map-selfcollide-p x))
                  (no-duplicatesp-equal (alist-keys (svtv-name-lhs-map-fix x))))
             (svex-envs-similar (svtv-name-lhs-map-eval-x inverse (svtv-name-lhs-map-eval x env))
                                (svtv-name-lhs-map-extract-env inverse env)))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-extract-env
                                      svtv-name-lhs-map-fix
                                      alist-keys
                                      svtv-name-lhs-map-selfcollide-p
                                      svtv-name-lhs-map-eval-x
                                      svtv-name-lhs-map-eval)
            :induct t)
           (and stable-under-simplificationp
                (eq (caar (last clause)) 'svex-envs-similar)
                `(:expand (,(car (last clause)))))))


  (defret eval-<fn>-of-lookup-gen
    (implies (svar-p v)
             (equal (lhs-eval-x (cdr (hons-assoc-equal v inverse)) env)
                    (svtv-name-lhs-map-var-inverse-eval-x v x env)))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-var-inverse-eval-x
                                      lhs-eval-x))))


  (defret lhs-bitproj-of-<fn>-lookup
    (implies (svar-p v)
             (equal (lhs-bitproj n (cdr (hons-assoc-equal v inverse)))
                    (svtv-name-lhs-map-var/idx-find v n x)))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-var/idx-find)
            :induct <call>
            :expand ((lhs-bitproj n nil))))))


;; Mapping between SVTV (pipeline) inputs and phase FSM inputs has some
;; subtleties.  The basic operation we want is to take an SVTV input alist and
;; produce a list of fsm input alists.  The first step of this is to
;; transform a flat alist of inputs into svtv-fsm inputs: a list of
;; input/override-value alists (one for each phase) and a list of override-test
;; alists.  The subtle part is the second step: mapping these svtv-fsm inputs
;; to fsm inputs using the namemap.  (There's also the step of mapping
;; cycle fsm inputs to phase fsm inputs -- this could be either before the
;; svtv-fsm -> base fsm step, translating cycle svtv-fsm inputs to phase
;; svtv-fsm-inputs, or after that step, translate cycle fsm inputs to
;; phase fsm inputs.  Probably the latter, but either way this doesn't
;; seem as hard.)

;; The namemap maps svtv-fsm input variables (domain) to LHSes in terms of the
;; fsm input variables.  (It may be that we can assume these LHSes free of
;; Zs.)  To create fsm inputs from svtv-fsm inputs we essentially reverse
;; the map, assigning the parts of the fsm variables used in the LHSes to
;; the corresponding parts of the svtv-fsm inputs according to their position
;; in the LHS.  To be most general, any parts of fsm input variables that
;; aren't used in the namemap should be set to Xes.  Additionally, we need to
;; decide what to do about collisions: probably the logical story should be
;; that the first range mentioned shadows the other, but that we check for
;; collisions at opportune times and don't allow them in practice. This seems
;; fine as far as just running the hardware and getting the right values to the
;; right places.

;; Where it gets complicated:

;; We want to prove lemmas about the SVTV and extrapolate from these lemmas
;; facts about the underlying fsm (or an idealized version of it),
;; preferably automatically.  In the SVTV lemma, we'll have various hypotheses
;; about values of the SVTV variables, which we'll need to translate to
;; hypotheses about the svtv-fsm inputs -- there may be some subtleties here
;; about what happens when the same input variable is used in multiple places
;; but we'll deal with those elsewhere.  The tricky part is translating the
;; hypotheses about the svtv-fsm inputs to hypotheses about the fsm
;; inputs.  Suppose we have an assumption

;; (assum-p (svex-env-lookup 'myvar (nth 5 svtv-fsm-inputs)))

;; Then to be most general, what we'd have to assume about the base fsm inputs
;; would be something like:

;; (implies (and (env-matches-parts (cdr (hons-get 'myvar *svtv-fsm/fsm-input-mapping*))
;;                                  myvar (nth 5 fsm-inputs))
;;               (assum-p myvar)
;;               ...)
;;          ...)

;; But that's not great as a rewrite rule: myvar won't be mentioned in the LHS
;; of the rule, so it's a free variable and the value it needs to be bound to
;; depends on assum-p as well as the mapping.  E.g., if assum-p is
;; (unsigned-byte-p 5 myvar), and the mapping maps its 5 lowest bits, then we
;; need to extend those 5 mapped bits with 0. OTOH if assum-p is (signed-byte-p
;; 5 myvar), then we need to sign-extend those mapped bits, etc.  Maybe we can
;; come up with a way to have it work for these simple cases.

;;  We'd like to be able to get rid of the free variable.  E.g.

;; (let ((myvar (extract-from-env (cdr (hons-get 'myvar *svtv-fsm/fsm-input-mapping*))
;;                                (nth 5 fsm-inputs))))
;;   (implies (and (assum-p myvar)
;;                 ...)
;;            ...))

;; For the unsigned-byte-p case, maybe this could be OK if extract-from-env put
;; 0s in the unmapped parts (i.e. lhs-eval-zx). But then for the signed-byte-p case, that hyp
;; would be unsatisfiable and we'd actually have a vacuous theorem.

;; Can we somehow check that this is OK?  Note it's not enough to just check
;; that the hyps are satisfiable; what we really want to show is that each
;; value assigned to myvar in the svtv-fsm theorem has a corresponding value
;; fsm theorem where the hyps are satisfied.  That is:

;; (implies (and (assum-p myvar)
;;               (4vec-p myvar))
;;          (exists fsm-env
;;                  (let ((myvar2 (lhs-eval-zx ... fsm-env)))
;;                    (and (assum-p myvar2)
;;                         (equal (relevant-parts myvar) (relevant-parts myvar2))))))

;; Assuming no collisions in the LHS (so that the non-Z parts are basically
;; free), this is bascially just:

;; (implies (and (assum-p myvar)
;;               (4vec-p myvar))
;;          (exists myvar2
;;                    (and (zero-under-mask lhs-mask myvar2)
;;                         (assum-p myvar2)
;;                         (equal (relevant-parts myvar) (relevant-parts myvar2))))))

;; And considering relevant-parts is basically logand under the mask, this would be the same as:

;; (implies (and (assum-p myvar)
;;               (4vec-p myvar))
;;          (let ((myvar2 (4vec-bitand lhsmask myvar)))
;;             (assum-p myvar2)))

;; This looks good for the case of unsigned-byte-p when the lhsmask is as mask
;; of the same width -- if assum-p has other assumptions besides
;; unsigned-byte-p, those can be solved by showing myvar2 = myvar.  If assum-p
;; is something more general (integerp or 4vec-p), this is even easiser.

;; If assum-p were instead signed-byte-p or something like that, then we ought
;; to use a different sort of lhs-eval as the extraction function and replace
;; the 4vec-bitand as the fixing function -- the fixing function could be a
;; function of the lhs mask and width, e.g., to accommodate signed-byte-p.

;; So it seems this leads to a system where the user can specify the extraction
;; and fixing function on a per-variable basis.  We can provide the
;; lhs-eval-zx/4vec-bitand version as a default and maybe one supporting
;; signed-byte-p.  For truly weird and specific hypotheses -- e.g., (equal
;; (logtail 8 myvar) 135) when only 5 bits of myvar are actually relevant --
;; well, users probably shouldn't do that, or if they have a really good reason
;; they can do the work of coming up with an extra extraction function, fixing
;; function, and lemmas to support the non-vacuity proof.

;; Example of this kind of generalization.

;; (defsvtv my-svtv
;;   :design (my-design)
;;   :phases
;;   ((:label cycle0
;;     :inputs (("clk" 0 :toggle t)
;;              ("opcode" #xfeed)
;;              ("a" ain)
;;              ("{ bpartouter[3:0], bpartmid[2:0], bpartouter[7:5] }" bin)))
;;    (:label cycle1 :delay 2
;;     :overrides (("q" qovr :cond qovr-ovr :output qovr)
;;                 ("{rh[2:0], rl[5:3]}" rovr :cond rovr-ovr :output rovr)))
;;    (:label cycle2 :delay 2
;;     :outputs (("c" cout)
;;               ("{ dh[4:3], dl[3:2] }" dout)))))

;; ;; The namemap then looks like this ...
;; (defconst *my-svtv-namemap*
;;   (("clk" "clk")            ;; width 1
;;    ("opcode" (16 . "opcode")) ;; width 16
;;    ("a"      (5 . "a"))       ;; width 5
;;    ("{ bpartouter[3:0], bpartmid[2:0], bpartouter[7:5] }"
;;     (3 "bpartouter" . 5) ;; rsh 5, width 3
;;     (3 . "bpartmid")     ;; width 3
;;     (4 . "bpartouter"))  ;; width 4
;;    ("q" (5 . "q"))       ;; width 5
;;    ("{rh[2:0], rl[5:3]}"
;;     (3 "rl" . 3) ;; rsh 3, width 3
;;     (3 . "rh"))  ;; width 3
;;    ("c" (4 . "c")) ;; width 4
;;    ("{ dh[4:3], dl[3:2] }"
;;     (2 "dl" . 2) ;; rsh 2, width 2
;;     (2 "dh" . 3))) ;; rsh 3, width 2
;;   )
;; ;; Inverted namemap --
;; (defconst *my-svtv-inverted-namemap*
;;   '(("dh" (3 . :Z)
;;      (2 "{ dh[4:3], dl[3:2] }" . 2))
;;     ("dl" (2 . :Z)
;;      (2 . "{ dh[4:3], dl[3:2] }"))
;;     ("c" (4 . "c"))
;;     ("rh" (3 "{rh[2:0], rl[5:3]}" . 3))
;;     ("rl" (3 . :Z)
;;      (3 . "{rh[2:0], rl[5:3]}"))
;;     ("q" (5 . "q"))
;;     ("bpartmid" (3 "{ bpartouter[3:0], bpartmid[2:0], bpartouter[7:5] }"
;;                    . 3))
;;     ("bpartouter" (4 "{ bpartouter[3:0], bpartmid[2:0], bpartouter[7:5] }"
;;                      . 6)
;;      :Z (3 .
;;            "{ bpartouter[3:0], bpartmid[2:0], bpartouter[7:5] }"))
;;     ("a" (5 . "a"))
;;     ("opcode" (16 . "opcode"))
;;     ("clk" "clk")))

;; ;; svtv-fsm inputs:
;; (defconst *my-svtv-svtv-fsm-inputs*
;;   '((("clk" . 0)
;;      ("opcode" . #xfeed)
;;      ("a" . ain)
;;      ("{ bpartouter[3:0], bpartmid[2:0], bpartouter[7:5] }" . bin))
;;     (("clk" . 1))
;;     (("clk" . 0)
;;      ("q" . qovr)
;;      ("{rh[2:0], rl[5:3]}" . rovr))
;;     (("clk" . 1))
;;     (("clk" . 0))))

;; ;; svtv-fsm override-tests:
;; (defconst *my-svtv-svtv-fsm-overrides*
;;   '(nil
;;     nil
;;     (("q" . qovr-ovr)
;;      ("{rh[2:0], rl[5:3]}" . rovr-ovr))
;;     nil
;;     nil))

;; ;; probes:
;; (defconst *my-svtv-probes*
;;   '((cout "c" . 4)
;;     (dout "{ dh[4:3], dl[3:2] }" . 4)))


;; (def-svtv-fancy-fsm-thm my-thmname
;;   :inputs (ain bin)
;;   :overrides (qovr rovr)
;;   :outputs (cout dout)
;;   :hyp (inputs-and-overrides-hyp ain bin qovr rovr)
;;   :concl (outputs-correct cout dout ain bin qovr rovr)
;;   :svtv (my-svtv)

;;   :fsm-extraction-functions ((bin lhs-eval-zx-signext)
;;                                   (rovr lhs-eval-with-weird-upper-bits)))

;; ;; SVTV lemma:

;; (defthm my-thmname-lemma
;;   (implies (inputs-and-overrides-hyp ain bin qovr rovr)
;;            (b* (((svassocs cout dout)
;;                  (svtv-run (my-svtv)
;;                            `((ain . ,ain)
;;                              (bin . ,bin)
;;                              (qovr . ,qovr)
;;                              (rovr . ,rovr)
;;                              ;; conditional override test vars
;;                              (qovr-ovr . -1)
;;                              (rovr-ovr . -1)))))
;;              (outputs-correct cout dout ain bin qovr rovr))))

;; ;; Idealized fsm theorem:
;; (defthm my-thmname
;;   (b* ((outenvs (fsm-eval inenvs initst (my-svtv-fsm)))
;;        (ain (lhs-eval-zx '((5 . "a")) (nth 0 inenvs))) ;; entry for "a" in the namemap
;;        (bin (lhs-eval-zx-signext '((3 "bpartouter" . 5) ;; entry for "b" in the namemap
;;                                        (3 . "bpartmid")
;;                                        (4 . "bpartouter"))
;;                                      (nth 0 inenvs)))
;;        (qovr (lhs-eval-zx '((5 . "q")) (nth 1 outenvs)))
;;        (rovr (lhs-eval-with-weird-upper-bits '((3 "rl" . 3)
;;                                                (3 . "rh")) (nth 1 outenvs))))
;;     (implies (and (lhs-eval-matches-const '("clk") 0 (nth 0 inenvs))
;;                   (lhs-eval-matches-const '((16 . "opcode")) #xfeed (nth 0 inenvs))
;;                   (inputs-and-overrides-hyp ain bin qovr rovr))
;;              (b* ((cout (lhs-eval-zx '((4 . "c")) (nth 2 outenvs)))
;;                   (dout (lhs-eval-zx '((2 "dl" . 2) ;; rsh 2, width 2
;;                                                      (2 "dh" . 3))
;;                                                    (nth 2 outenvs))))
;;                (outputs-correct cout dout ain bin qovr rovr)))))

;; Somewhere in some table we have this mapping
;;   ((lhs-eval-zx . (4vec-bitand mask x))
;;    (lhs-eval-zx-signext . (4vec-sign-extend width (4vec-bitand mask x)))
;;    (lhs-eval-with-weird-upper-bits . (4vec-concat width (4vec-bit?! mask x (4vec-z)) #xabc)))


;; Non-vacuity check:
;; (implies (and (inputs-and-overrides-hyp ain bin qovr rovr)
;;               (4vec-p ain) (4vec-p bin) (4vec-p qovr) (4vec-p rovr))
;;          (let ((ain (4vec-bitand #x1f ain))
;;                (bin (4vec-signx 10 (4vec-bitand #x3ff bin)))
;;                (qovr (4vec-bitand #x1f qovr))
;;                (rovr (4vec-concat 6 (4vec-bit?! #x3f rovr (4vec-z)) #xabc)))
;;             (inputs-and-overrides-hyp ain bin qovr rovr)))



;; Question: Should we even support alternative extraction/fixing functions
;; besides the lhs-eval-zx/bitand version that supports unsigned-byte hyps?
;; We're not (at least currently) offering an option for how outputs should be
;; extracted -- they use lhs-eval-zx, basically -- so for composition to work
;; smoothly arguably the inputs and especially overrides should be conceived
;; the same ways.

;; For now we'll build in the assumption that lhs-eval-zx is what we're
;; using; if we need others they can be added later.



(define svtv-name-lhs-map-keys-change-override ((map svtv-name-lhs-map-p)
                                                (type svar-overridetype-p))
  :returns (new-map svtv-name-lhs-map-p)
  (if (atom map)
      nil
    (if (mbt (and (consp (car map)) (svar-p (caar map))))
        (b* (((cons var val) (car map)))
          (cons (cons (svar-change-override var type)
                      (lhs-fix val))
                (svtv-name-lhs-map-keys-change-override (cdr map) type)))
      (svtv-name-lhs-map-keys-change-override (cdr map) type)))
  ///
  (local (in-theory (enable svtv-name-lhs-map-fix)))

  ;; (defret lookup-of-<fn>-when-wrong-override-val
  ;;   (implies (not (iff (svar->override-val v) override-val))
  ;;            (not (hons-assoc-equal v new-map))))

  ;; (defret lookup-of-<fn>-when-wrong-override-test
  ;;   (implies (not (iff (svar->override-test v) override-test))
  ;;            (not (hons-assoc-equal v new-map))))

    (local (in-theory (disable iff)))

  (local (in-theory (enable equal-of-svar-change-override)))

  (local (defret lookup-of-<fn>-when-overrides-uniform-lemma
           (implies (and (svarlist-override-p (alist-keys (svtv-name-lhs-map-fix map))
                                              prev-type)
                         (svar-override-p v type)
                         (svar-p v))
                    (equal (hons-assoc-equal v new-map)
                           (b* ((old-v (svar-change-override v prev-type))
                                (look (hons-assoc-equal old-v (svtv-name-lhs-map-fix map))))
                             (and look (cons v (cdr look))))))
           :hints(("Goal" :in-theory (enable alist-keys
                                             svarlist-override-p
                                             ;; svar-override-p
                                             )))))

  (defret lookup-of-<fn>-when-overrides-uniform
    (implies (and (equal mapf (svtv-name-lhs-map-fix map))
                  (equal keys (alist-keys mapf))
                  (bind-free (case-match keys
                               (('binary-append a &) `((keys1 . ,a)))
                               (& `((keys1 . ,keys))))
                             (keys1))
                  ;; (syntaxp (or (cw "keys1: ~x0~%" keys1) t))
                  (svarlist-override-p keys1 prev-type)
                  (svarlist-override-p keys prev-type)
                  (svar-override-p v type)
                  (svar-p v))
             (equal (hons-assoc-equal v new-map)
                    (b* ((old-v (svar-change-override v prev-type))
                         (look (hons-assoc-equal old-v mapf)))
                      (and look (cons v (cdr look))))))
    :hints (("goal" :use lookup-of-<fn>-when-overrides-uniform-lemma
             :in-theory (disable lookup-of-<fn>-when-overrides-uniform-lemma))))

  (defret svarlist-override-p-keys-of-<fn>
    (svarlist-override-p (alist-keys new-map) type)
    :hints(("Goal" :in-theory (enable svarlist-override-p svar-override-p alist-keys)))))

(define lhatom-change-override ((x lhatom-p)
                                (type svar-overridetype-p))
  :returns (new-x lhatom-p)
  (lhatom-case x
    :z (lhatom-fix x)
    :var (change-lhatom-var x :name (svar-change-override x.name type))))



(define lhs-change-override ((x lhs-p)
                             (type svar-overridetype-p))
  :returns (new-x lhs-p)
  (if (atom x)
      nil
    (cons (b* (((lhrange x1) (car x)))
            (change-lhrange x1 :atom (lhatom-change-override x1.atom type)))
          (lhs-change-override (cdr x) type)))

  ///
  (local (in-theory (disable iff not)))

  (defthm svtv-name-lhs-map-keys-change-override-of-lhs-accumulate-name-lhs-map
    (b* (((mv ?collision inv) (lhs-accumulate-name-lhs-map-inverse dom-var offset lhs inverse-acc))
         ((mv ?collision2 renamed-inv)
          (lhs-accumulate-name-lhs-map-inverse
           dom-var offset
           (lhs-change-override lhs type)
           (svtv-name-lhs-map-keys-change-override inverse-acc type))))
      (implies (and (svarlist-override-p (lhs-vars lhs) prev-type)
                    (svarlist-override-p (alist-keys (svtv-name-lhs-map-fix inverse-acc)) prev-type))
               (equal (svtv-name-lhs-map-keys-change-override inv type)
                      renamed-inv)))
    :hints(("Goal" :in-theory (enable lhs-accumulate-name-lhs-map-inverse
                                      lhatom-change-override
                                      svtv-name-lhs-map-keys-change-override
                                      lhatom-vars
                                      svarlist-override-p
                                      alist-keys)))))

(define svtv-name-lhs-map-vals-change-override ((x svtv-name-lhs-map-p)
                                                (type svar-overridetype-p))
  :returns (new-x svtv-name-lhs-map-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x))
                  (svar-p (caar x))))
        (cons (cons (caar x) (lhs-change-override (cdar x) type))
              (svtv-name-lhs-map-vals-change-override (cdr x) type))
      (svtv-name-lhs-map-vals-change-override (cdr x) type)))
  ///
  (local (in-theory (enable svtv-name-lhs-map-fix)))

  (defthm svtv-name-lhs-map-keys-change-override-of-inverse
    (b* (((mv ?collision inv) (svtv-name-lhs-map-inverse x))
         ((mv ?collision2 renamed-inv)
          (svtv-name-lhs-map-inverse
           (svtv-name-lhs-map-vals-change-override x type))))
      (implies (svarlist-override-p (svtv-name-lhs-map-vars x) prev-type)
               (equal (svtv-name-lhs-map-keys-change-override
                       inv type)
                      renamed-inv)))
    :hints(("Goal" :in-theory (enable svtv-name-lhs-map-inverse)
            :induct t
            :expand ((SVTV-NAME-LHS-MAP-KEYS-CHANGE-OVERRIDE NIL TYPE)
                     (svtv-name-lhs-map-vars x))))))



(defsection svtv-name-lhs-map-p-of-fal-extract
  (local (defthm lookup-when-not-svar-p-of-svtv-name-lhs-map
           (implies (and (svtv-name-lhs-map-p x)
                         (not (svar-p k)))
                    (not (hons-assoc-equal k x)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))
  (local (defthm car-of-hons-assoc-equal
           (equal (car (hons-assoc-equal k x))
                  (and (hons-assoc-equal k x) k))))
  (defthm svtv-name-lhs-map-p-of-fal-extract
    (implies (svtv-name-lhs-map-p x)
             (svtv-name-lhs-map-p (fal-extract keys x)))
    :hints(("Goal" :in-theory (enable fal-extract svtv-name-lhs-map-p)))))
