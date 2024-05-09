; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "add-primitives")
(include-book "primitives-stub")
(include-book "bfr-arithmetic")
(include-book "def-fgl-rewrite")
(include-book "checks")
(include-book "congruence-rules")
(local (include-book "primitive-lemmas"))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable w)))


(def-formula-checks checks-formula-checks
  (check-true
   check-integerp
   check-natp
   check-int-endp
   check-bitp
   check-signed-byte-p
   check-unsigned-byte-p
   check-int-sign
   check-non-integerp
   check-consp
   check-non-consp
   check-booleanp
   check-non-booleanp
   check-equal
   integer-length-bound
   ifix
   symbolic-t
   symbolic-nil
   alist-const-pairs))

;; (local (defthm equal-of-len
;;          (implies (syntaxp (quotep n))
;;                   (equal (equal (len x) n)
;;                          (cond ((equal n 0) (atom x))
;;                                ((zp n) nil)
;;                                ((consp x) (equal (len (cdr x)) (1- n)))
;;                                (t nil))))))

(local (defthm fgl-ev-context-equv-forall-extensions-trivial
         (implies (acl2::rewriting-negative-literal
                   `(fgl-ev-context-equiv-forall-extensions ,contexts ,obj ,term ,eval-alist))
                  (iff (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)
                       (and 
                        (equal (fgl-ev-context-fix contexts (fgl-ev term eval-alist))
                               (fgl-ev-context-fix contexts obj))
                        (hide (fgl-ev-context-equiv-forall-extensions contexts obj term eval-alist)))))
         :hints (("goal" :expand ((:free (x) (hide x)))
                  :use ((:instance fgl-ev-context-equiv-forall-extensions-necc
                         (ext eval-alist)))
                  :in-theory (disable fgl-ev-context-equiv-forall-extensions-necc)))))

(local (in-theory (disable fgl-ev-context-equiv-forall-extensions)))

;; (local (defthm fgl-object-bindings-eval-nil
;;          (equal (fgl-object-bindings-eval-

(local (defthm fgl-object-eval-when-booleanp
         (implies (booleanp x)
                  (equal (fgl-object-eval x env) x))
         :hints(("Goal" :in-theory (enable fgl-object-eval fgl-object-kind g-concrete->val)))))


(local (defthm fgl-object-alist-eval-when-atom
         (implies (atom x)
                  (equal (fgl-object-alist-eval x env logicman)
                         x))
         :hints(("Goal" :in-theory (enable fgl-object-alist-eval)))))

(local (in-theory (disable member-equal
                           equal-of-booleans-rewrite)))

(add-fgl-congruence iff-implies-equal-check-true-2)

(def-fgl-binder-meta check-true-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete arg.val
          :g-integer t
          :g-boolean (eq arg.bool t)
          :g-cons t
          :g-map arg.alist
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :prepwork ((local (in-theory (enable check-true)))
             (local (defthm fgl-object-alist-eval-under-iff
                      (iff (fgl-object-alist-eval x env)
                           (fgl-object-alist-fix x))
                      :hints (("goal" :expand ((fgl-object-alist-eval x env)
                                               (fgl-object-alist-fix x))
                               :in-theory (enable (:i len))
                               :induct (len x))))))
  :origfn check-true :formals (arg))

(def-fgl-binder-meta check-integerp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (integerp arg.val)
          :g-integer t
          :g-apply (or (and (eq arg.fn 'ifix) (eql (len arg.args) 1))
                       (eq arg.fn 'intcdr)
                       (eq arg.fn 'intcons))
          :g-map (integerp arg.alist)
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :prepwork ((local (in-theory (enable check-integerp))))
  :origfn check-integerp :formals (arg))


(def-fgl-binder-meta check-natp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (natp arg.val)
          :g-integer (eq (car (last arg.bits)) nil)
          :g-map (natp arg.alist)
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-natp :formals (arg)
  :prepwork ((local (in-theory (enable check-natp)))
             (local (defthm bools->int-less-than-0
                      (iff (< (bools->int x) 0)
                           (car (last x)))
                      :hints(("Goal" :in-theory (enable bools->int)))))
             (local (defthm car-last-of-gobj-bfr-list-eval
                      (implies (not (car (last x)))
                               (not (car (last (gobj-bfr-list-eval x env)))))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))))




(local (defthm int-endp-of-fgl-object-alist-eval
         (implies (and (fgl-object-alist-p x)
                       (int-endp x))
                  (int-endp (fgl-object-alist-eval x env logicman)))
         :hints(("Goal" :expand ((fgl-object-alist-eval x env logicman))
                 :in-theory (enable int-endp)))))

(def-fgl-binder-meta check-int-endp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (or (not (integerp arg.val))
                          (int-endp arg.val))
          :g-integer (or (atom arg.bits)
                         (atom (cdr arg.bits)))
          :g-boolean t
          :g-cons t
          :g-map (or (not (integerp arg.alist))
                     (int-endp arg.alist))
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-int-endp :formals (arg)
  :prepwork ((local (in-theory (enable check-int-endp)))
             (local (defthm int-endp-of-bools->int
                      (implies (atom (cdr x))
                               (int-endp (bools->int x)))
                      :hints(("Goal" :in-theory (enable bools->int int-endp)))))
             (local (defthm consp-cdr-of-gobj-bfr-list-eval
                      (iff (consp (cdr (gobj-bfr-list-eval x env)))
                           (consp (cdr x)))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))
             (local (defthm int-endp-when-not-integerp
                      (implies (not (integerp x))
                               (int-endp x))
                      :hints(("Goal" :in-theory (enable int-endp)))))))


(def-fgl-binder-meta check-bitp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (bitp arg.val)
          :g-integer (or (endp arg.bits)
                         (and (endp (cdr arg.bits))
                              (not (car arg.bits)))
                         (and (consp (cdr arg.bits))
                              (endp (cddr arg.bits))
                              (not (cadr arg.bits))))
          :g-map (bitp arg.alist)
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-bitp :formals (arg)
  :prepwork ((local (in-theory (enable check-bitp)))
             (local (defthm bitp-of-bools->int
                      (implies (or (atom x)
                                   (and (atom (cdr x))
                                        (not (car x)))
                                   (and (consp (cdr x))
                                        (atom (cddr x))
                                        (not (cadr x))))
                               (bitp (bools->int x)))
                      :hints(("Goal" :in-theory (enable bools->int bitp)))))
             (local (defthm consp-cdr-of-gobj-bfr-list-eval
                      (iff (consp (cdr (gobj-bfr-list-eval x env)))
                           (consp (cdr x)))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))
             (local (defthm consp-cddr-of-gobj-bfr-list-eval
                      (iff (consp (cddr (gobj-bfr-list-eval x env)))
                           (consp (cddr x)))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))
             (local (defthm not-cadr-of-gobj-bfr-list-eval
                      (implies (not (cadr x))
                               (not (cadr (gobj-bfr-list-eval x env))))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))))



(def-fgl-binder-meta check-signed-byte-p-binder
  (b* (((unless (fgl-object-case len :g-concrete))
        (mv nil nil nil nil interp-st state))
       (len (g-concrete->val len))
       ((unless (posp len))
        (mv t 'ans '((ans . nil)) nil interp-st state))
       (ans
        (fgl-object-case arg
          :g-concrete (signed-byte-p len arg.val)
          :g-integer (<= (len arg.bits) len)
          :g-map (and (integerp arg.alist)
                      (signed-byte-p len arg.alist))
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-signed-byte-p :formals (len arg)
  :prepwork ((local (in-theory (enable check-signed-byte-p)))
             (local (defun signed-byte-p-of-bools->int-ind (n x)
                      (if (or (zp n) (eql n 1))
                          x
                        (signed-byte-p-of-bools->int-ind (1- n) (cdr x)))))

             (local (defthm signed-byte-p-of-bools->int
                      (implies (and (posp n)
                                    (<= (len x) n))
                               (signed-byte-p n (bools->int x)))
                      :hints(("Goal" :in-theory (e/d (bools->int len bool->bit)
                                                     (signed-byte-p
                                                      bitops::signed-byte-p-of-logcdr))
                              :induct (signed-byte-p-of-bools->int-ind n x)
                              :expand ((:with bitops::signed-byte-p** (:free (x) (signed-byte-p n x))))))))
             (local (defthm len-of-gobj-bfr-list-eval
                      (equal (len (gobj-bfr-list-eval x env))
                             (len x))))))


(def-fgl-binder-meta check-unsigned-byte-p-binder
  (b* (((unless (fgl-object-case len :g-concrete))
        (mv nil nil nil nil interp-st state))
       (len (g-concrete->val len))
       ((unless (natp len))
        (mv t 'ans '((ans . nil)) nil interp-st state))
       (ans
        (fgl-object-case arg
          :g-concrete (unsigned-byte-p len arg.val)
          :g-integer (and (<= (len arg.bits) (+ 1 len))
                          (not (car (last arg.bits))))
          :g-map (and (integerp arg.alist)
                      (unsigned-byte-p len arg.alist))
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-unsigned-byte-p :formals (len arg)
  :prepwork ((local (in-theory (e/d (check-unsigned-byte-p)
                                    (unsigned-byte-p))))
             (local (defun unsigned-byte-p-of-bools->int-ind (n x)
                      (if (zp n)
                          x
                        (unsigned-byte-p-of-bools->int-ind (1- n) (cdr x)))))

             (local (defthm unsigned-byte-p-of-bools->int
                      (implies (and (natp n)
                                    (<= (len x) (+ 1 n))
                                    (not (car (last x))))
                               (unsigned-byte-p n (bools->int x)))
                      :hints(("Goal" :in-theory (e/d (bools->int len last bool->bit)
                                                     (unsigned-byte-p))
                              :induct (unsigned-byte-p-of-bools->int-ind n x)
                              :expand ((:with bitops::unsigned-byte-p** (:free (x) (unsigned-byte-p n x))))))))
             (local (defthm car-last-of-gobj-bfr-list-eval
                      (implies (not (car (last x)))
                               (not (car (last (gobj-bfr-list-eval x env)))))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))))))


(local (defthm negp-of-fgl-object-alist-eval
         (implies (fgl-object-alist-p x)
                  (iff (acl2::negp (fgl-object-alist-eval x env logicman))
                       (acl2::negp x)))
         :hints(("Goal" :expand ((fgl-object-alist-eval x env logicman))
                 :in-theory (enable acl2::negp)))))

(def-fgl-binder-meta check-int-sign-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (if (< (ifix arg.val) 0) -1 0)
          :g-integer (b* ((lastbit (car (last arg.bits))))
                       (cond ((eq lastbit nil) 0)
                             ((eq lastbit t) -1)
                             (t nil)))
          :g-map (if (< (ifix arg.alist) 0) -1 0)
          :g-boolean 0
          :g-cons 0
          :otherwise nil)))
    (mv t (kwote ans) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-int-sign :formals (arg)
  :prepwork ((local (in-theory (enable check-int-sign)))
             (local (defthm car-last-of-gobj-bfr-list-eval
                      (and (implies (not (car (last x)))
                                    (<= 0 (bools->int (gobj-bfr-list-eval x env))))
                           (implies (equal (car (last x)) t)
                                    (< (bools->int (gobj-bfr-list-eval x env)) 0)))
                      :hints(("Goal" :in-theory (enable gobj-bfr-list-eval)))
                      :rule-classes :linear))))


(local (defthm not-integerp-of-fgl-object-alist-eval
         (implies (and (fgl-object-alist-p x)
                       (not (integerp x)))
                  (not (integerp (fgl-object-alist-eval x env logicman))))
         :hints(("Goal" :expand ((fgl-object-alist-eval x env logicman))))))


(def-fgl-binder-meta check-non-integerp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (not (integerp arg.val))
          :g-integer nil
          :g-boolean t
          :g-cons t
          :g-map (not (integerp arg.alist))
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-non-integerp :formals (arg)
  :prepwork ((local (in-theory (enable check-non-integerp)))))


(local (defthm consp-of-fgl-object-alist-eval
         (implies (and (fgl-object-alist-p x)
                       (consp x))
                  (consp (fgl-object-alist-eval x env logicman)))
         :hints(("Goal" :expand ((fgl-object-alist-eval x env logicman))))))




(def-fgl-binder-meta check-consp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (consp arg.val)
          :g-integer nil
          :g-boolean nil
          :g-cons t
          :g-apply (eq arg.fn 'cons)
          :g-map (consp arg.alist)
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-consp :formals (arg)
  :prepwork ((local (in-theory (enable check-consp)))))

(def-fgl-binder-meta check-non-consp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (not (consp arg.val))
          :g-integer t
          :g-boolean t
          :g-map (not (consp arg.alist))
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-non-consp :formals (arg)
  :prepwork ((local (in-theory (enable check-non-consp)))))


(def-fgl-binder-meta check-booleanp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (booleanp arg.val)
          :g-boolean t
          :g-apply (or (eq arg.fn 'equal)
                       (eq arg.fn 'intcar)
                       (eq arg.fn 'integerp))
          :g-map (booleanp arg.alist)
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-booleanp :formals (arg)
  :prepwork ((local (in-theory (enable check-booleanp)))))

(local (defthm not-booleanp-of-fgl-object-alist-eval
         (implies (and (fgl-object-alist-p x)
                       (not (booleanp x)))
                  (not (booleanp (fgl-object-alist-eval x env logicman))))
         :hints(("Goal" :expand ((fgl-object-alist-eval x env logicman))))))

(def-fgl-binder-meta check-non-booleanp-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (not (booleanp arg.val))
          :g-integer t
          :g-cons t
          :g-map (not (booleanp arg.alist))
          :otherwise nil)))
    (mv t (if ans ''t ''nil) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn check-non-booleanp :formals (arg)
  :prepwork ((local (in-theory (enable check-non-booleanp)))))

(local (in-theory (enable fgl-object-p-when-integerp)))

(def-fgl-binder-meta integer-length-bound-binder
  (b* ((ans
        (fgl-object-case arg
          :g-concrete (integer-length (ifix arg.val))
          :g-boolean 0
          :g-cons 0
          :g-integer (max 0 (1- (len arg.bits)))
          :g-map (if (integerp arg.alist)
                     (integer-length arg.alist)
                   0)
          :otherwise nil)))
    (mv t (kwote ans) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn integer-length-bound :formals (arg)
  :prepwork ((local (in-theory (enable integer-length-bound
                                       fgl-object-p-when-integerp
                                       fgl-object-kind-when-integerp
                                       g-concrete->val-when-integerp)))
             (local (defthm integer-length-when-zip
                      (implies (zip x)
                               (equal (integer-length x) 0))))
             (local (defthm integer-length-of-bools->int
                      (<= (integer-length (bools->int x)) (max 0 (+ -1 (len x))))
                      :hints(("Goal" :in-theory (enable bools->int
                                                        bool->bit
                                                        bitops::integer-length**)))
                      :rule-classes ((:linear :trigger-terms ((integer-length (bools->int x)))))))))



(local (defthm cdr-of-fgl-objectlist-fix
         (equal (cdr (fgl-objectlist-fix x))
                (fgl-objectlist-fix (cdr x)))))

(def-fgl-binder-meta check-equal-binder
  (mv t  (if (equal (fgl-object-fix x)
                    (fgl-object-fix y))
             ''t ''nil)
      nil nil interp-st state)
  :formula-check checks-formula-checks
  :origfn check-equal :formals (x y)
  :prepwork ((local (in-theory (enable check-equal)))))

(def-fgl-primitive symbolic-t ()
  (g-boolean t)
  :formula-check checks-formula-checks
  :returns ans)

(def-fgl-primitive symbolic-nil ()
  (g-boolean nil)
  :formula-check checks-formula-checks
  :returns ans)

(fgl::disable-execution symbolic-t)
(fgl::disable-execution symbolic-nil)



(define alist-const-pairs-map ((x fgl-object-alist-p)
                               acc
                               nonconst-acc)
  :measure (len x)
  :hooks ((:fix :hints (("goal" :induct (alist-const-pairs-map x acc nonconst-acc)
                         :expand ((fgl-object-alist-fix x))))))
  (b* (((when (atom x)) (prog2$ (fast-alist-free nonconst-acc) acc))
       ((unless (mbt (consp (car x))))
        (alist-const-pairs-map (cdr x) acc nonconst-acc))
       ((cons key val) (car x))
       (boundp (or (hons-get key acc)
                   (hons-get key nonconst-acc)))
       ((when boundp) (alist-const-pairs-map (cdr x) acc nonconst-acc))
       ((unless (fgl-object-case val :g-concrete))
        (alist-const-pairs-map (cdr x) acc (hons-acons key t nonconst-acc))))
    (alist-const-pairs-map (cdr x) (hons-acons key (g-concrete->val val) acc) nonconst-acc))
  ///
  (defthm lookup-in-alist-const-pairs-map
    (b* ((map-pair (hons-assoc-equal k (alist-const-pairs-map x acc nonconst-acc))))
      (and (implies (hons-assoc-equal k acc)
                    (equal map-pair (hons-assoc-equal k acc)))
           (implies (and (not (hons-assoc-equal k acc))
                         (hons-assoc-equal k nonconst-acc))
                    (equal map-pair nil))
           (implies (and (not (hons-assoc-equal k acc))
                         map-pair
                         (bind-free '((env . env) (logicman . logicman)) (env logicman)))
                    (Equal map-pair
                           (hons-assoc-equal k (fgl-object-alist-eval x env))))))
                    
    :hints (("goal" :induct (alist-const-pairs-map x acc nonconst-acc)
             :expand ((:free (x) (hide x))
                      (fgl-object-alist-eval x env))))))
    

(define alist-const-pairs-rec ((x fgl-object-p)
                               acc
                               nonconst-acc)
  :measure (fgl-object-count x)
  (fgl-object-case x
    :g-map (alist-const-pairs-map x.alist acc nonconst-acc)
    :g-cons (fgl-object-case x.car
              :g-concrete (b* (((mv acc nonconst-acc)
                                (b* (((unless (consp x.car.val))
                                      (mv acc nonconst-acc))
                                     ((cons key val) x.car.val)
                                     ((when (or (hons-get key acc)
                                                (hons-get key nonconst-acc)))
                                      (mv acc nonconst-acc)))
                                  (mv (hons-acons key val acc) nonconst-acc))))
                            (alist-const-pairs-rec x.cdr acc nonconst-acc))
              :g-cons (b* (((unless (fgl-object-case x.car.car :g-concrete))
                            ;; We can't determine what this key evaluates
                            ;; to, so we can only return keys already
                            ;; bound before it.
                            (prog2$ (fast-alist-free nonconst-acc)
                                    acc))
                           ((mv acc nonconst-acc)
                            (b* ((key (g-concrete->val x.car.car))
                                 ((when (or (hons-get key acc)
                                            (hons-get key nonconst-acc)))
                                  (mv acc nonconst-acc))
                                 ((unless (fgl-object-case x.car.cdr :g-concrete))
                                  (mv acc (hons-acons key t nonconst-acc))))
                              (mv (hons-acons key (g-concrete->val x.car.cdr) acc)
                                  nonconst-acc))))
                        (alist-const-pairs-rec x.cdr acc nonconst-acc))
              ;; skip known atoms
              :g-boolean (alist-const-pairs-rec x.cdr acc nonconst-acc)
              :g-integer (alist-const-pairs-rec x.cdr acc nonconst-acc)
              :otherwise (prog2$ (fast-alist-free nonconst-acc)
                                 acc))
    :otherwise (prog2$ (fast-alist-free nonconst-acc)
                       acc))
  ///
  (defthm lookup-in-alist-const-pairs-rec
    (b* ((map-pair (hons-assoc-equal k (alist-const-pairs-rec x acc nonconst-acc))))
      (and (implies (hons-assoc-equal k acc)
                    (equal map-pair (hons-assoc-equal k acc)))
           (implies (and (not (hons-assoc-equal k acc))
                         (hons-assoc-equal k nonconst-acc))
                    (equal map-pair nil))
           (implies (and (not (hons-assoc-equal k acc))
                         map-pair
                         (bind-free '((env . env) (logicman . logicman)) (env logicman)))
                    (Equal map-pair
                           (hons-assoc-equal k (fgl-object-eval x env))))))
    :hints (("goal" :induct (alist-const-pairs-rec x acc nonconst-acc)
             :expand ((alist-const-pairs-rec x acc nonconst-acc))
             :in-theory (disable (:d alist-const-pairs-rec)))))

  (defthm sub-alistp-of-alist-const-pairs-rec
    (acl2::sub-alistp (alist-const-pairs-rec x nil nil)
                      (fgl-object-eval x env))
    :hints(("Goal" :in-theory (enable acl2::sub-alistp-iff-witness)))))



(def-fgl-binder-meta alist-const-pairs-binder
  (b* ((ans (alist-const-pairs-rec x nil nil)))
    (mv t (kwote ans) nil nil interp-st state))
  :formula-check checks-formula-checks
  :origfn alist-const-pairs :formals (x)
  :prepwork ((local (in-theory (enable alist-const-pairs)))
             (local (defthm sub-alistp-of-alist-const-pairs-rec-rw
                      (implies (equal (alist-const-pairs-rec x nil nil) alist)
                               (acl2::sub-alistp alist (fgl-object-eval x env)))))))



