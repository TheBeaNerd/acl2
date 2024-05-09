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

(include-book "svtv-stobj-export")
(include-book "svtv-stobj-cycle")
(include-book "../svex/compose-theory-monotonicity")
(local (include-book "../svex/alist-thms"))
(local (include-book "std/lists/sets" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :System))
(local (std::add-default-post-define-hook :fix))
#||
(include-book
 "svtv-stobj-defsvtv")

(include-book
 "svtv-stobj-pipeline-thm")

(include-book
 "svtv-stobj-export")

(local
 (defconst *my-design*
   (make-design
    :top "my-mod"
    :modalist (list
               (cons "my-mod"
                     (make-module
                      :wires (list (make-wire :name "in"
                                              :width 5
                                              :low-idx 0)
                                   (make-wire :name "mid"
                                              :width 5
                                              :low-idx 0)
                                   (make-wire :name "out"
                                              :width 5
                                              :low-idx 0))
                      :assigns (list (cons
                                      (list (make-lhrange
                                             :w 5
                                             :atom
                                             (make-lhatom-var
                                              :name "out"
                                              :rsh 0)))
                                      (make-driver
                                       :value (svcall bitnot
                                                      (svcall zerox 5 "mid"))))
                                     (cons
                                      (list (make-lhrange
                                             :w 5
                                             :atom
                                             (make-lhatom-var
                                              :name "mid"
                                              :rsh 0)))
                                      (make-driver
                                       :value (svcall bitnot
                                                      (svcall zerox 5 "in")))))))))))

(defsvtv$-phasewise my-svtv
   :design *my-design*
   :phases
   ((:label the-phase
     :inputs (("in" in))
     :overrides (("mid" (mid mid-ovr)))
     :outputs (("out" out)))
    (:label the-next-phase
     :inputs (("in" in2))
     :overrides (("mid" (mid2 mid2-ovr)))
     :outputs (("out" out2)))))

(def-svtv-data-export my-svtv-data)

(def-svtv-partial-monotonic my-svtv :export my-svtv-data)

(encapsulate nil
  (local (defthm my-svtv-data-obj-pipeline-is-my-svtv-outexprs
           (equal (svtv-data-obj->pipeline (my-svtv-data))
                  (svtv->outexprs (my-svtv)))
           :hints(("Goal" :in-theory (enable (my-svtv) (my-svtv-data))))))
  (local (defthm my-svtv-data-mono-conditions
           (let ((obj (my-svtv-data)))
             (and (svtv-data-obj->flatnorm-validp obj)
                  (svtv-data-obj->flatten-validp obj)
                  (svtv-data-obj->phase-fsm-validp obj)
                  (svtv-data-obj->cycle-fsm-validp obj)
                  (svtv-data-obj->pipeline-validp obj)
                  (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup obj))
                  (svex-alist-check-monotonic (pipeline-setup->initst (svtv-data-obj->pipeline-setup obj)))
                  (svex-alistlist-check-monotonic (svtv-data-obj-pipeline-substs obj))))
           :hints(("Goal" :in-theory (enable (my-svtv-data))))))

  (local (defthm override-vars-of-my-svtv-data
           (equal (svtv-input-substs-extract-override-vars
                   (svtv-data-obj-pipeline-substs (my-svtv-data)))
                  '(mid-ovr mid2-ovr))
           :hints(("Goal" :in-theory (enable (my-svtv-data))))))

  (defthm my-svtv-partial-monotonic
    (svex-alist-partial-monotonic '(mid-ovr mid2-ovr)
                                  (svtv->outexprs (my-svtv)))
    :hints (("goal" :use ((:instance svtv-data-obj-pipeline-partial-monotonic-p (obj (my-svtv-data))))))))


(defsvtv$-phasewise my-svtv2
   :design *my-design*
   :phases
   ((:label the-phase
     :inputs (("in" i))
     :overrides (("mid" (mid mid-ovr)))
     :outputs (("out" o)))
    (:label the-next-phase
     :inputs (("in" i2))
     :overrides (("mid" (mid2 mid2-ovr)))
     :outputs (("out" o2)))))


(def-svtv-partial-monotonic my-svtv2)           

||#


(defthmd svtv-data$ap-when-flatnorm-validp
  (implies (and (svtv-data$ap x)
                (svtv-data$c->flatnorm-validp x))
           (svtv-data$c-flatnorm-okp x (svtv-data$c->flatnorm x)))
  :hints(("Goal" :in-theory (disable svtv-data$c-flatnorm-okp))))


(local (defthm svex-alist-monotonic-p-of-cons
         (implies (and (svex-alist-monotonic-p x)
                       (svex-monotonic-p val))
                  (svex-alist-monotonic-p (cons (cons key val) x)))
         :hints (("goal" :expand ((:with svex-alist-monotonic-in-terms-of-lookup
                                   (svex-alist-monotonic-p (cons (cons key val) x))))
                  :in-theory (enable svex-lookup-of-cons)))))


(defthm svex-alist-monotonic-p-of-pairlis$
  (implies (svexlist-monotonic-p vals)
           (svex-alist-monotonic-p (pairlis$ keys vals)))
  :hints(("Goal" :in-theory (enable pairlis$))))

(defthm svexlist-monotonic-p-of-svexlist-monotonify
  (svexlist-monotonic-p (Svexlist-monotonify x))
  :hints(("Goal" :in-theory (enable svexlist-monotonic-p))))

(defthm svex-alist-monotonic-p-of-svex-alist-monotonify
  (svex-alist-monotonic-p (svex-alist-monotonify x))
  :hints(("Goal" :in-theory (enable svex-alist-monotonic-p))))

(local
 (defthm svex-alist-monotonic-p-of-svex-alist-monotonify-equiv
   (implies (svex-alist-eval-equiv! y (svex-alist-monotonify x))
            (svex-alist-monotonic-p y))))

(defthm svtv-data-obj-ok-implies-flatnorm-assigns-monotonic
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                (svtv-data-obj->flatnorm-validp obj)
                (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup obj)))
           (svex-alist-monotonic-p (flatnorm-res->assigns (svtv-data-obj->flatnorm obj))))
  :hints(("goal" :in-theory (enable svtv-normalize-assigns)
          :use ((:instance svtv-data$ap-implies-flatnorm-okp
                 (x (svtv-data-obj-to-stobj-logic obj)))))))


;; phase-fsm-validp-of-svtv-data-obj
;; (defthm svtv-data-obj-ok-implies-phase-fsm-composition-p
;;   (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
;;                 (svtv-data-obj->phase-fsm-validp obj))
;;            (phase-fsm-composition-p (svtv-data-obj->phase-fsm obj)
;;                                     (svtv-data-obj->flatnorm obj)
;;                                     (svtv-data-obj->phase-fsm-setup obj)))
;;   :hints (("goal" :use ((:instance svtv-data$ap-implies-phase-fsm-okp
;;                          (x (svtv-data-obj-to-stobj-logic obj)))))))






(defthm svex-alist-partial-monotonic-of-nil
  (svex-alist-partial-monotonic params nil)
  :hints(("Goal" :in-theory (enable svex-alist-partial-monotonic
                                    svex-alist-compose))))

(defthm svex-alist-partial-monotonic-of-cons
  (implies (and (svex-partial-monotonic params val)
                (svex-alist-partial-monotonic params x))
           (svex-alist-partial-monotonic params (cons (cons var val) x)))
  :hints (("goal" :expand ((svex-alist-partial-monotonic params (cons (cons var val) x)))
           :in-theory (enable svex-alist-compose svex-acons
                              svex-partial-monotonic-necc
                              svex-alist-partial-monotonic-necc))))


(defthm svex-alist-partial-monotonic-of-cons-params
  (implies (svex-alist-partial-monotonic params x)
           (svex-alist-partial-monotonic (cons var params) x))
  :hints (("goal" :expand ((svex-alist-partial-monotonic (cons var params) x))
           :in-theory (enable svex-alist-compose svex-acons
                              svex-partial-monotonic-necc
                              svex-alist-partial-monotonic-necc))))


(local (defthmd svex-eval-of-svex-var
         (equal (svex-eval (svex-var x) env)
                (svex-env-lookup x env))
         :hints(("Goal" :in-theory (enable svex-eval)))))

(local (defthmd svex-lookup-when-member-svex-alist-keys
         (implies (member-equal (svar-fix k) (svex-alist-keys x))
                  (svex-lookup k x))
         :hints(("Goal" :in-theory (enable svex-lookup)))))

(defthm svex-partial-monotonic-of-override-ite
  (implies (member-equal (svar-fix override-test) (svarlist-fix params))
           (svex-partial-monotonic
            params
            (sv::svcall bit?! (svex-var override-test)
                        (svex-var override-val)
                        (svex-var val))))
  :hints(("Goal" :in-theory (enable svex-partial-monotonic
                                    svex-monotonic-p
                                    svex-apply
                                    svex-eval-of-svex-var
                                    svex-alist-eval-when-svex-alist-constantp
                                    svex-lookup-when-member-svex-alist-keys)
          :do-not-induct t)))

;; (defthm svex-alist-partial-monotonic-of-svarlist-to-override-alist
;;   (implies (svarlist-non-override-test-p x)
;;            (svex-alist-partial-monotonic
;;             (svarlist->override-tests x)
;;             (svarlist-to-override-alist x)))
;;   :hints(("Goal" :in-theory (enable svarlist-to-override-alist
;;                                     svarlist->override-tests
;;                                     svarlist-non-override-test-p))))

(defthm svex-alist-partial-monotonic-of-svarlist-to-override-alist
  (svex-alist-partial-monotonic
   (svarlist-change-override x :test)
   (svarlist-to-override-alist x))
  :hints(("Goal" :in-theory (enable svarlist-to-override-alist
                                    svarlist-change-override
                                    svarlist-override-p))))

(local (defthmd loghead-0-when-loghead-0
         (implies (and (equal (loghead n x) 0)
                       (< (nfix m) (nfix n)))
                  (equal (equal (loghead m x) 0)
                         t))
         :hints (("goal" :in-theory (enable* bitops::ihsext-inductions
                                             bitops::ihsext-recursive-redefs)))))

(defthm svarlist-override-p-when-svarlist-addr-p
    (implies (svarlist-addr-p x)
             (svarlist-override-p x nil))
    :hints(("Goal" :in-theory (enable svarlist-override-p
                                      svarlist-addr-p
                                      svar-override-p
                                      svar-addr-p
                                      svar->override-val
                                      svar->override-test
                                      loghead-0-when-loghead-0))))

         


(defthm svtv-data-obj-ok-implies-svarlist-addr-p-of-flatnorm-delays
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                (svtv-data-obj->flatnorm-validp obj)
                (svtv-data-obj->flatten-validp obj))
           (and (svarlist-addr-p (svex-alist-vars (flatnorm-res->delays (svtv-data-obj->flatnorm obj))))
                (svarlist-addr-p (svex-alist-keys (flatnorm-res->delays (svtv-data-obj->flatnorm obj))))))
  :hints (("Goal" :use ((:instance svtv-data$ap-implies-flatnorm-okp
                         (x (svtv-data-obj-to-stobj-logic obj)) )
                        (:instance svtv-data$ap-implies-flatten-okp
                         (x (svtv-data-obj-to-stobj-logic obj)) ))
           :in-theory (enable svtv-data$c-flatnorm-okp
                              svtv-data$c-flatten-okp
                              svtv-normalize-assigns
                              svtv-design-flatten))))








(defthmd svarlist-override-p-when-subsetp
  (implies (and (subsetp-equal x y)
                (svarlist-override-p y type))
           (svarlist-override-p x type))
  :hints (("Goal" :use ((:instance (:functional-instance acl2::element-list-p-when-subsetp-equal-non-true-list
                                    (acl2::element-list-p (lambda (x) (svarlist-override-p x type)))
                                    (acl2::element-list-final-cdr-p (lambda (x) t))
                                    (acl2::element-p (lambda (x) (svar-override-p x type)))
                                    (acl2::element-example (lambda () (svar-change-override nil type))))
                         (x x) (y y)))
           :in-theory (enable svarlist-override-p))))

(local (defthm subsetp-of-set-diff
         (subsetp-equal (set-difference-equal x y) x)))

(local (defthm subsetp-of-intersect
         (subsetp-equal (intersection-equal x y) x)))

(defthm svarlist-override-p-of-svtv-assigns-override-vars
  (implies (svarlist-override-p (svex-alist-keys assigns) type)
           (svarlist-override-p (svtv-assigns-override-vars assigns config) type))
  :hints(("Goal" :in-theory (enable svtv-assigns-override-vars)
          :use ((:instance svarlist-override-p-when-subsetp
                 (x (svtv-assigns-override-vars assigns config))
                 (y (svex-alist-keys assigns))
                 (type type))))))

(local (defthm member-of-svarlist-change-override-when-other-override-p
         (implies (and (svar-override-p x type2)
                       (not (equal (svar-overridetype-fix type2)
                                   (svar-overridetype-fix type))))
                  (not (member-equal x (svarlist-change-override y type))))
         :hints(("Goal" :in-theory (enable svarlist-change-override)))))

(local (defthm intersectp-of-change-override-when-not-override-p
         (implies (and (svarlist-override-p x type2)
                       (not (equal (svar-overridetype-fix type2)
                                   (svar-overridetype-fix type))))
                  (not (intersectp-equal x (svarlist-change-override y type))))
         :hints(("Goal" :in-theory (enable svarlist-change-override
                                           svarlist-override-p
                                           intersectp-equal)))))

(local (defthm intersectp-of-change-override-when-override-p-nil
         (implies (and (svarlist-override-p x nil)
                       (svar-overridetype-fix type))
                  (not (intersectp-equal x (svarlist-change-override y type))))
         :hints(("Goal" :in-theory (enable svarlist-change-override
                                           svarlist-override-p
                                           intersectp-equal)))))



(defthm svex-alist-partial-monotonic-of-svtv-flatnorm-apply-overrides
  (implies (and (svarlist-override-p (svex-alist-keys (flatnorm-res->assigns flatnorm)) nil)
                (svex-alist-monotonic-p (flatnorm-res->assigns flatnorm)))
           (svex-alist-partial-monotonic
            (svarlist-change-override
             (svtv-assigns-override-vars (flatnorm-res->assigns flatnorm) config)
             :test)
            (mv-nth 0 (svtv-flatnorm-apply-overrides flatnorm config))))
  :hints(("Goal" :in-theory (enable svtv-flatnorm-apply-overrides))))








(defthmd phase-fsm-composition-p-implies-values-keys
  (implies (phase-fsm-composition-p phase-fsm flatnorm config)
           (b* (((phase-fsm-config config))
                ((mv overridden-assigns ?overridden-delays)
                 (svtv-flatnorm-apply-overrides
                  flatnorm config.override-config))
                ((fsm phase-fsm)))
             (set-equiv (svex-alist-keys phase-fsm.values)
                        (Svex-alist-keys overridden-assigns))))
  :hints(("Goal" :in-theory (enable phase-fsm-composition-p))))

(defthmd phase-fsm-composition-p-implies-nextstate
  (implies (phase-fsm-composition-p phase-fsm flatnorm config)
           (b* (((phase-fsm-config config))
                ((mv ?overridden-assigns overridden-delays)
                 (svtv-flatnorm-apply-overrides
                  flatnorm config.override-config))
                ((fsm phase-fsm)))
             (svex-alist-eval-equiv!
              phase-fsm.nextstate
              (svex-alist-compose overridden-delays phase-fsm.values))))
  :hints(("Goal" :in-theory (enable phase-fsm-composition-p))))


(defthmd phase-fsm-composition-p-implies-netevalcomp-p
  (implies (phase-fsm-composition-p phase-fsm flatnorm config)
           (b* (((phase-fsm-config config))
                ((mv overridden-assigns ?overridden-delays)
                 (svtv-flatnorm-apply-overrides flatnorm config.override-config))
                ((fsm phase-fsm)))
             (netevalcomp-p phase-fsm.values overridden-assigns)))
  :hints (("goal" :in-theory (enable phase-fsm-composition-p))))


(defthm svtv-data-obj-ok-implies-svex-alist-partial-monotonic-of-phase-fsm-values
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                (svtv-data-obj->flatnorm-validp obj)
                (svtv-data-obj->flatten-validp obj)
                (svtv-data-obj->phase-fsm-validp obj)
                (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup obj)))
           (svex-alist-partial-monotonic
            (svarlist-change-override
             (svtv-assigns-override-vars (flatnorm-res->assigns
                                          (svtv-data-obj->flatnorm obj))
                                         (phase-fsm-config->override-config
                                          (svtv-data-obj->phase-fsm-setup obj)))
             :test)
            (fsm->values (svtv-data-obj->phase-fsm obj))))
  :hints (("Goal" :use ((:instance phase-fsm-validp-of-svtv-data-obj (x obj) )
                        (:instance phase-fsm-composition-p-implies-netevalcomp-p
                         (config (svtv-data-obj->phase-fsm-setup obj))
                         (phase-fsm (svtv-data-obj->phase-fsm obj))
                         (flatnorm (svtv-data-obj->flatnorm obj))))
           :in-theory (e/d (svex-alist-partial-monotonic-when-netevalcomp-p)
                           (phase-fsm-validp-of-svtv-data-obj
                            phase-fsm-composition-p-implies-netevalcomp-p
                            flatnorm-of-svtv-data-obj)))))





(defthm svtv-data-obj-ok-implies-svarlist-addr-keys-of-phase-fsm-values
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                (svtv-data-obj->flatnorm-validp obj)
                (svtv-data-obj->flatten-validp obj)
                (svtv-data-obj->phase-fsm-validp obj))
           (svarlist-addr-p
                 (svex-alist-keys (fsm->values (svtv-data-obj->phase-fsm obj)))))
  :hints (("Goal" :use ((:instance phase-fsm-validp-of-svtv-data-obj (x obj) ))
           :in-theory (e/d (svex-alist-partial-monotonic-when-netevalcomp-p
                            phase-fsm-composition-p-implies-values-keys)
                           (phase-fsm-validp-of-svtv-data-obj
                            phase-fsm-composition-p-implies-netevalcomp-p
                            flatnorm-of-svtv-data-obj)))))


(local (include-book "std/alists/fast-alist-clean" :dir :system))

(local (defthm alist-keys-of-fast-alist-clean-under-set-equiv
         (set-equiv (alist-keys (fast-alist-clean x))
                    (alist-keys x))
         :hints(("Goal" :in-theory (e/d (acl2::set-unequal-witness-correct)
                                        (fast-alist-clean))))))

(local (defthm svex-alist-keys-of-fast-alist-clean-under-set-equiv
         (set-equiv (svex-alist-keys (fast-alist-clean x))
                    (svex-alist-keys x))
         :hints(("Goal" :in-theory (e/d (acl2::set-unequal-witness-correct
                                         svex-lookup)
                                        (fast-alist-clean))))))



;; (local (defthm svarlist-addr-p-of-alist-keys-when-svarlist-addr-p-of-svar-map-vars
;;          (implies (and (svar-map-p x)
;;                        (svarlist-addr-p (svar-map-vars x)))
;;                   (svarlist-addr-p (alist-keys x)))
;;          :hints(("Goal" :in-theory (enable alist-keys svar-map-vars)))))



(defthm svtv-data-obj-ok-implies-svarlist-addr-keys-of-phase-fsm-nextstate
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                (svtv-data-obj->flatnorm-validp obj)
                (svtv-data-obj->flatten-validp obj)
                (svtv-data-obj->phase-fsm-validp obj))
           (svarlist-addr-p
            (svex-alist-keys (fsm->nextstate (svtv-data-obj->phase-fsm obj)))))
  :hints (("Goal" :use ((:instance phase-fsm-validp-of-svtv-data-obj (x obj) ))
           :in-theory (e/d (svex-alist-partial-monotonic-when-netevalcomp-p
                            phase-fsm-composition-p-implies-nextstate)
                           (phase-fsm-validp-of-svtv-data-obj
                            phase-fsm-composition-p-implies-netevalcomp-p
                            flatnorm-of-svtv-data-obj
                            fast-alist-clean)))))


(defthm svtv-data-obj-ok-implies-no-override-keys-of-phase-fsm-values
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                (svtv-data-obj->flatnorm-validp obj)
                (svtv-data-obj->flatten-validp obj)
                (svtv-data-obj->phase-fsm-validp obj)
                (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup obj)))
           (not (intersectp-equal
                 (svarlist-change-override
                  (svtv-assigns-override-vars (flatnorm-res->assigns
                                               (svtv-data-obj->flatnorm obj))
                                              (phase-fsm-config->override-config
                                               (svtv-data-obj->phase-fsm-setup obj)))
                  :test)
                 (svex-alist-keys (fsm->values (svtv-data-obj->phase-fsm obj))))))
  :hints (("Goal" :use ((:instance phase-fsm-validp-of-svtv-data-obj (x obj) )
                        (:instance phase-fsm-composition-p-implies-netevalcomp-p
                         (config (svtv-data-obj->phase-fsm-setup obj))
                         (phase-fsm (svtv-data-obj->phase-fsm obj))
                         (flatnorm (svtv-data-obj->flatnorm obj))))
           :in-theory (e/d ()
                           (phase-fsm-validp-of-svtv-data-obj
                            phase-fsm-composition-p-implies-netevalcomp-p
                            flatnorm-of-svtv-data-obj)))))

(defthm svtv-data-obj-ok-implies-no-override-keys-of-phase-fsm-nextstate
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                (svtv-data-obj->flatnorm-validp obj)
                (svtv-data-obj->flatten-validp obj)
                (svtv-data-obj->phase-fsm-validp obj)
                (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup obj)))
           (not (intersectp-equal
                 (svarlist-change-override
                  (svtv-assigns-override-vars (flatnorm-res->assigns
                                               (svtv-data-obj->flatnorm obj))
                                              (phase-fsm-config->override-config
                                               (svtv-data-obj->phase-fsm-setup obj)))
                  :test)
                 (svex-alist-keys (fsm->nextstate (svtv-data-obj->phase-fsm obj))))))
  :hints (("Goal" :use ((:instance phase-fsm-validp-of-svtv-data-obj (x obj) )
                        (:instance phase-fsm-composition-p-implies-nextstate
                         (config (svtv-data-obj->phase-fsm-setup obj))
                         (phase-fsm (svtv-data-obj->phase-fsm obj))
                         (flatnorm (svtv-data-obj->flatnorm obj))))
           :in-theory (e/d ()
                           (phase-fsm-validp-of-svtv-data-obj
                            phase-fsm-composition-p-implies-nextstate
                            flatnorm-of-svtv-data-obj)))))














(local
 (defthm svex-alist-compose-preserves-partial-monotonic-equiv!
   (implies (and (svex-alist-eval-equiv! y (svex-alist-compose x a))
                 (svex-alist-partial-monotonic params x)
                 (svex-alist-partial-monotonic params a)
                 (svex-compose-alist-selfbound-keys-p params a))
            (svex-alist-partial-monotonic params y))
   :hints (("goal" :use ((:instance svex-alist-compose-preserves-svex-alist-partial-monotonic
                          (params2 params)))))))

(defthm svex-looup-of-fast-alist-clean
  (Equal (svex-lookup k (fast-alist-clean x))
         (svex-lookup k x))
  :hints(("Goal" :in-theory (e/d (svex-lookup) (fast-alist-clean)))))


(defthm svex-alist-monotonic-p-of-fast-alist-clean
  (implies (svex-alist-monotonic-p x)
           (svex-alist-monotonic-p (fast-alist-clean x)))
  :hints(("Goal" :expand ((:with svex-alist-monotonic-in-terms-of-lookup
                           (svex-alist-monotonic-p (fast-alist-clean x))))
          :in-theory (e/d ()
                          (fast-alist-clean)))))

(defthm svtv-flatnorm-apply-overrides-delays-monotonic
  (implies (and (svarlist-override-p (svex-alist-keys (flatnorm-res->assigns flatnorm)) nil)
                (svex-alist-monotonic-p (flatnorm-res->delays flatnorm)))
           (svex-alist-partial-monotonic
            (svarlist-change-override
             (svtv-assigns-override-vars (flatnorm-res->assigns flatnorm) config)
             :test)
            (mv-nth 1 (svtv-flatnorm-apply-overrides flatnorm config))))
  :hints(("Goal" :in-theory (e/d (svtv-flatnorm-apply-overrides)
                                 (fast-alist-clean)))))



(local
 (defthm svex-alist-compose-preserves-partial-monotonic-same-params
   (implies (and (svex-alist-partial-monotonic params x)
                 (svex-alist-partial-monotonic params a)
                 (svex-compose-alist-selfbound-keys-p params a))
            (svex-alist-partial-monotonic params (svex-alist-compose x a)))
   :hints (("goal" :use ((:instance svex-alist-compose-preserves-svex-alist-partial-monotonic
                          (params2 params)))))))

(local (defthm svex-monotonic-p-of-zerox-var
         (svex-monotonic-p (svcall zerox (svex-quote w) (svex-var name)))
         :hints(("Goal" :in-theory (enable svex-monotonic-p
                                           svex-apply svex-eval)))))

(local
 (defthm svex-alist-monotonic-p-of-svar-map-truncate-by-var-decls
   (implies (svex-alist-monotonic-p acc)
            (svex-alist-monotonic-p (svar-map-truncate-by-var-decls map decls acc)))
   :hints(("Goal" :in-theory (enable svar-map-truncate-by-var-decls)))))

(defthm svex-alist-monotonic-p-nil
  (svex-alist-monotonic-p nil)
  :hints(("Goal" :in-theory (enable svex-alist-monotonic-p))))

(local
 (defret svex-alist-monotonic-p-of-svtv-normalize-assigns-delays
   (svex-alist-monotonic-p (flatnorm-res->delays res))
   :hints(("Goal" :in-theory (e/d (svtv-normalize-assigns
                                   svex-normalize-assigns)
                                  (fast-alist-clean))
           :do-not-induct t))
   :fn svtv-normalize-assigns))

(defthm delays-monotonic-of-svtv-data-obj->flatnorm
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic x))
                (svtv-data-obj->flatnorm-validp x)
                (svtv-data-obj->flatten-validp x))
           (svex-alist-monotonic-p (flatnorm-res->delays (svtv-data-obj->flatnorm x)))))


(defthm svtv-data-obj-ok-implies-svex-alist-partial-monotonic-of-phase-fsm-nextstate
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                (svtv-data-obj->flatnorm-validp obj)
                (svtv-data-obj->flatten-validp obj)
                (svtv-data-obj->phase-fsm-validp obj)
                (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup obj)))
           (svex-alist-partial-monotonic
            (svarlist-change-override
             (svtv-assigns-override-vars (flatnorm-res->assigns
                                          (svtv-data-obj->flatnorm obj))
                                         (phase-fsm-config->override-config
                                          (svtv-data-obj->phase-fsm-setup obj)))
             :test)
            (fsm->nextstate (svtv-data-obj->phase-fsm obj))))
  :hints (("Goal" :use ((:instance phase-fsm-validp-of-svtv-data-obj (x obj) )
                        (:instance phase-fsm-composition-p-implies-nextstate
                         (config (svtv-data-obj->phase-fsm-setup obj))
                         (phase-fsm (svtv-data-obj->phase-fsm obj))
                         (flatnorm (svtv-data-obj->flatnorm obj))))
           :in-theory (e/d (svex-alist-partial-monotonic-when-netevalcomp-p)
                           (phase-fsm-validp-of-svtv-data-obj
                            phase-fsm-composition-p-implies-netevalcomp-p
                            flatnorm-of-svtv-data-obj)))))

(defthm svex-alist-compose-rw-under-svex-alist-eval-equiv
  (svex-alist-eval-equiv (svex-alist-compose-rw x subst)
                         (svex-alist-compose x (svex-substconfig->alist subst)))
  :hints(("Goal" :in-theory (enable svex-envs-equivalent-implies-alist-eval-equiv))))



(defthm svex-alist-monotonic-p-of-extract
  (implies (svex-alist-monotonic-p a)
           (svex-alist-monotonic-p (svex-alist-extract keys a)))
  :hints (("goal" :expand ((:with svex-alist-monotonic-in-terms-of-lookup
                            (svex-alist-monotonic-p (svex-alist-extract keys a))))
           :in-theory (enable svex-monotonic-p-of-const))))


(local (defthmd svex-alist-compose-of-extract
         (equal (svex-alist-compose (svex-alist-extract keys a) b)
                (svex-alist-extract keys (svex-alist-compose a b)))
         :hints(("Goal" :in-theory (enable svex-alist-compose svex-alist-extract
                                           svex-acons)
                 :expand ((Svex-compose '(-1 . 0) b))))))

(defthm svex-alist-partial-monotonic-of-extract
  (implies (And (svex-alist-partial-monotonic params a))
           (svex-alist-partial-monotonic params (svex-alist-extract keys a)))
  :hints (("goal" :expand ((svex-alist-partial-monotonic params (svex-alist-extract keys a)))
           :in-theory (enable svex-alist-partial-monotonic-necc
                              svex-alist-compose-of-extract))))


(defthm svex-alist-monotonic-p-of-svex-env-to-subst
  (svex-alist-monotonic-p (Svex-env-to-subst x))
  :hints(("Goal" :in-theory (enable svex-alist-monotonic-p))))

(defthm svex-alist-keys-of-svex-alist-extract
  (equal (svex-alist-keys (svex-alist-extract keys x))
         (svarlist-fix keys))
  :hints(("Goal" :in-theory (enable svex-alist-extract svex-alist-keys))))




;; (defthm svtv-cyclephaselist-constant-keys ((x svtv-cyclephaselist-p))
;;   :returns (keys svarlist-p)
;;   (if (atom x)
;;       nil
;;     (append (alist-keys (svtv-cyclephase->constants (car x)))
;;             (svtv-cyclephaselist-constant-keys

(local (defthm svex-env-extract-when-not-intersectp-first
         (implies (not (intersectp-equal (svarlist-fix keys) (alist-keys (svex-env-fix env1))))
                  (equal (svex-env-extract keys (append env1 env2))
                         (svex-env-extract keys env2)))
         :hints(("Goal" :in-theory (enable svex-env-extract intersectp-equal svarlist-fix
                                           svex-env-boundp)))))


(local (defthm equal-of-svex-env-extracts-lemman
         (implies (equal (svex-env-extract keys b)
                         (svex-env-extract keys c))
                  (equal (equal (svex-env-extract keys (append a b))
                                (svex-env-extract keys (append a c)))
                         t))
         :hints(("Goal" :in-theory (enable svex-env-extract)))))


(defthm svex-alist-partial-monotonic-of-compose-append-with-consts
  (implies (and (svex-alist-partial-monotonic params x)
                (svex-alist-partial-monotonic params y)
                (not (intersectp-equal (svarlist-fix params) (svex-alist-keys y)))
                (svex-alist-constantp z))
           (svex-alist-partial-monotonic params (svex-alist-compose x (append y z))))
  :hints (("goal" :expand ((:with svex-alist-partial-monotonic-by-eval
                            (svex-alist-partial-monotonic params (svex-alist-compose x (append y z)))))
           :in-theory (enable svex-alist-eval-when-svex-alist-constantp)
           :do-not-induct t)))

(local (defthm svex-alist-subst-rw-under-svex-alist-eval-equiv
         (svex-alist-eval-equiv (svex-alist-subst-rw x conf)
                                (svex-alist-subst x (svex-substconfig->alist conf)))
         :hints(("Goal" :in-theory (enable svex-alist-eval-equiv-in-terms-of-envs-equivalent)))))


(defthm svex-alist-partial-monotonic-of-subst-append-with-consts
  (implies (and (svex-alist-partial-monotonic params x)
                (svex-alist-partial-monotonic params y)
                (not (intersectp-equal (svarlist-fix params) (svex-alist-keys y)))
                (svex-alist-constantp z))
           (svex-alist-partial-monotonic params (svex-alist-subst x (append y z))))
  :hints (("goal" :expand ((:with svex-alist-partial-monotonic-by-eval
                            (svex-alist-partial-monotonic params (svex-alist-subst x (append y z)))))
           :in-theory (enable svex-alist-eval-when-svex-alist-constantp)
           :do-not-induct t)))


(defthm svex-alist-keys-of-svex-alist-subst
  (equal (svex-alist-keys (svex-alist-subst x a))
         (svex-alist-keys x))
  :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-subst))))


(defthm svex-alist-partial-monotonic-of-cycle-compile
  (implies (and (svex-alist-partial-monotonic params
                                              (fsm->values phase-fsm))
                (svex-alist-partial-monotonic params
                                              (fsm->nextstate phase-fsm))
                (svex-alist-partial-monotonic params prev-st)
                (not (intersectp-equal (svarlist-fix params) (svex-alist-keys (fsm->values phase-fsm))))
                (not (intersectp-equal (svarlist-fix params) (svex-alist-keys prev-st)))
                (not (intersectp-equal (svarlist-fix params) (svex-alist-keys (fsm->nextstate phase-fsm)))))
           (b* (((mv outs nextst) (svtv-cycle-compile prev-st phases phase-fsm simp)))
             (and (svex-alist-partial-monotonic params outs)
                  (svex-alist-partial-monotonic params nextst))))
  :hints(("Goal" :in-theory (enable svtv-cycle-compile
                                    svtv-cycle-step-phase-exprs
                                    fsm-step-subst))))


(defthm svex-alist-monotonic-p-of-identity-subst
  (svex-alist-monotonic-p (svex-identity-subst x))
  :hints(("Goal" :in-theory (enable svex-alist-monotonic-in-terms-of-lookup
                                    svex-monotonic-p-of-const))))


(defthm not-intersectp-override-tests-when-svarlist-addr-p
  (implies (and (svarlist-addr-p y)
                (svar-overridetype-fix type))
           (not (intersectp-equal (svarlist-change-override x type) y))))

(defthm cycle-fsm-okp-implies-values-partial-monotonic
  (implies (and (svtv-data$c-cycle-fsm-okp svtv-data cycle-fsm)
                (svex-alist-partial-monotonic (svarlist-change-override keys :test)
                                              (fsm->values (svtv-data$c->phase-fsm svtv-data)))
                (svex-alist-partial-monotonic (svarlist-change-override keys :test)
                                              (fsm->nextstate (svtv-data$c->phase-fsm svtv-data)))
                (svarlist-addr-p (svex-alist-keys (fsm->values (svtv-data$c->phase-fsm svtv-data))))
                (svarlist-addr-p (svex-alist-keys (fsm->nextstate (svtv-data$c->phase-fsm svtv-data)))))
           (and (svex-alist-partial-monotonic (svarlist-change-override keys :test)
                                              (fsm->values cycle-fsm))
                (svex-alist-partial-monotonic (svarlist-change-override keys :test)
                                              (fsm->nextstate cycle-fsm))))
  :hints(("Goal" :use ((:instance cycle-fsm-okp-implies-cycle-compile-values-equiv)))))



             


(defthm svtv-data-obj-ok-implies-svex-alist-partial-monotonic-of-cycle-fsm-values
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                (svtv-data-obj->flatnorm-validp obj)
                (svtv-data-obj->flatten-validp obj)
                (svtv-data-obj->phase-fsm-validp obj)
                (svtv-data-obj->cycle-fsm-validp obj)
                (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup obj)))
           (svex-alist-partial-monotonic
            (svarlist-change-override
             (svtv-assigns-override-vars (flatnorm-res->assigns
                                          (svtv-data-obj->flatnorm obj))
                                         (phase-fsm-config->override-config
                                          (svtv-data-obj->phase-fsm-setup obj)))
             :test)
            (fsm->values (svtv-data-obj->cycle-fsm obj))))
  :hints (("goal" :use ((:instance svtv-data$ap-implies-cycle-fsm-okp
                         (x (svtv-data-obj-to-stobj-logic obj)))))))

(defthm svtv-data-obj-ok-implies-svex-alist-partial-monotonic-of-cycle-fsm-nextstate
  (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                (svtv-data-obj->flatnorm-validp obj)
                (svtv-data-obj->flatten-validp obj)
                (svtv-data-obj->phase-fsm-validp obj)
                (svtv-data-obj->cycle-fsm-validp obj)
                (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup obj)))
           (svex-alist-partial-monotonic
            (svarlist-change-override
             (svtv-assigns-override-vars (flatnorm-res->assigns
                                          (svtv-data-obj->flatnorm obj))
                                         (phase-fsm-config->override-config
                                          (svtv-data-obj->phase-fsm-setup obj)))
             :test)
            (fsm->nextstate (svtv-data-obj->cycle-fsm obj))))
  :hints (("goal" :use ((:instance svtv-data$ap-implies-cycle-fsm-okp
                         (x (svtv-data-obj-to-stobj-logic obj)))))))


(define svex-alistlist-partial-monotonic ((params svarlist-p)
                                          (x svex-alistlist-p))
  (if (Atom x)
      t
    (and (ec-call (svex-alist-partial-monotonic params (car X)))
         (svex-alistlist-partial-monotonic params (Cdr x)))))


(define svex-envlists-agree ((keys svarlist-p)
                             (x svex-envlist-p)
                             (y svex-envlist-p))
  :measure (max (len x) (len y))
  (if (and (atom x) (atom y))
      t
    (and (equal (svex-env-extract keys (car x))
                (svex-env-extract keys (car y)))
         (svex-envlists-agree keys (cdr x) (cdr y)))))





(defthm svex-env-<<=-of-append-extract
  (implies (and (svex-env-<<= a b)
                (svex-env-<<= c d))
           (svex-env-<<= (append (svex-env-extract keys a) c)
                         (append (svex-env-extract keys b) d)))
  :hints(("Goal" :in-theory (enable svex-env-<<=))))

(encapsulate nil
  (local
   (defun fsm-eval-mono-ind (ins1 ins2 prev-st1 prev-st2 x)
     (if (atom ins1)
         (list ins2 prev-st1 prev-st2)
       (fsm-eval-mono-ind (cdr ins1)
                               (cdr ins2)
                               (fsm-step (car ins1) prev-st1 (fsm->nextstate x))
                               (fsm-step (car ins2) prev-st2 (fsm->nextstate x))
                               x))))

  (defthm partial-monotonicity-of-fsm-eval
    (implies (and (svex-alist-partial-monotonic params (fsm->values x))
                  (svex-alist-partial-monotonic params (fsm->nextstate x))
                  (svex-env-<<= prev-st1 prev-st2)
                  (svex-envlist-<<= ins1 ins2)
                  (svex-envlists-agree params ins1 ins2)
                  (equal (len ins1) (len ins2))
                  (not (intersectp-equal (svarlist-fix params) (svex-alist-keys (fsm->nextstate x)))))
             (svex-envlist-<<= (fsm-eval ins1 prev-st1 x)
                               (fsm-eval ins2 prev-st2 x)))
    :hints(("Goal" :in-theory (enable fsm-eval
                                      fsm-step-outs
                                      fsm-step
                                      fsm-step-env)
            :expand ((fsm-eval ins1 prev-st1 x)
                     (fsm-eval ins2 prev-st2 x)
                     (svex-envlist-<<= ins1 ins2)
                     (svex-envlists-agree params ins1 ins2)
                     (:free (a b c) (svex-envlist-<<= (cons a b) c)))
            :induct (fsm-eval-mono-ind ins1 ins2 prev-st1 prev-st2 x)))))





(defthm svex-env-<<=-of-extract
  (implies (svex-env-<<= a b)
           (svex-env-<<= (svex-env-extract keys a)
                         (svex-env-extract keys b)))
  :hints(("Goal" :expand ((svex-env-<<= (svex-env-extract keys a)
                                        (svex-env-extract keys b))))))

(defthm svex-envlist-<<=-of-extract
  (implies (svex-envlist-<<= a b)
           (svex-envlist-<<= (svex-envlist-extract signals a)
                             (svex-envlist-extract signals b)))
  :hints(("Goal" :in-theory (enable svex-envlist-extract svex-envlist-<<=))))

(defthm svex-env-<<=-of-svtv-probealist-extract
  (implies (svex-envlist-<<= a b)
           (svex-env-<<= (svtv-probealist-extract probes a)
                         (svtv-probealist-extract probes b)))
  :hints(("Goal" :in-theory (enable svtv-probealist-extract))))


(local (defthm len-of-svex-env-extract
         (equal (len (svex-env-extract keys x))
                (len keys))
         :hints(("Goal" :in-theory (enable svex-env-extract)))))

(local
 (defsection equal-of-append
   (local (defun append-ind (a c)
            (if (atom a)
                c
              (append-ind (cdr a) (cdr c)))))
     
   (defthm equal-of-append
     (implies (equal (len a) (len c))
              (equal (equal (append a b) (append c d))
                     (and (equal (true-list-fix a) (true-list-fix c))
                          (equal b d))))
     :hints(("Goal" :in-theory (enable true-list-fix)
             :induct (append-ind a c))))))


(define svtv-input-subst-extract-override-vars ((x svex-alist-p))
  (if (atom x)
      nil
    (append (and (mbt (and (consp x) (svar-p (caar x))))
                 (svar-override-p (caar x) :test)
                 (svex-vars (cdar x)))
            (svtv-input-subst-extract-override-vars (cdr x))))
  ///
  
  (defthm svtv-input-subst-extract-override-vars-lookup-correct
    (b* ((vars (svtv-input-subst-extract-override-vars x)))
      (implies (equal (svex-env-extract vars env1)
                      (svex-env-extract vars env2))
               (Equal (equal (svex-eval (svex-lookup (svar-change-override var :test)
                                                     x)
                                        env1)
                             (svex-eval (svex-lookup (svar-change-override var :test)
                                                     x)
                                        env2))
                      t)))
    :hints(("Goal" :in-theory (enable svex-lookup hons-assoc-equal
                                      svex-eval-equal-when-extract-vars-similar))))
  
  (defthm svtv-input-subst-extract-override-vars-correct
    (b* ((vars (svtv-input-subst-extract-override-vars x)))
      (implies (equal (svex-env-extract vars env1)
                      (svex-env-extract vars env2))
               (Equal (equal (svex-env-extract (svarlist-change-override keys :test)
                                               (svex-alist-eval x env1))
                             (svex-env-extract (svarlist-change-override keys :test)
                                               (svex-alist-eval x env2)))
                      t)))
    :hints(("Goal" :in-theory (enable svarlist-change-override
                                      svex-env-extract)
            :induct (svarlist-change-override keys :test))))

  (local (in-theory (enable svex-alist-fix))))

(define svtv-input-substs-extract-override-vars ((x svex-alistlist-p))
  (if (atom x)
      nil
    (append (svtv-input-subst-extract-override-vars (car x))
            (svtv-input-substs-extract-override-vars (cdr x))))
  ///
  (defthm svtv-input-substs-extract-override-vars-correct
    (b* ((vars (svtv-input-substs-extract-override-vars x)))
      (implies (equal (svex-env-extract vars env1)
                      (svex-env-extract vars env2))
               (svex-envlists-agree (svarlist-change-override keys :test)
                                    (svex-alistlist-eval x env1)
                                    (svex-alistlist-eval x env2))))
    :hints(("Goal" :in-theory (enable svex-envlists-agree
                                      svex-alistlist-eval)))))



(define svtv-data-obj-pipeline-substs ((obj svtv-data-obj-p))
  :returns (substs svex-alistlist-p)
  (b* (((pipeline-setup setup) (svtv-data-obj->pipeline-setup obj))
       (outvars (svtv-probealist-outvars setup.probes)))
    (svtv-fsm-to-fsm-inputsubsts (take (len outvars) setup.inputs)
                                      setup.override-vals setup.override-tests
                                      (svtv-data-obj->namemap obj))))




(defthm lhatom-subst-zero-partial-monotonic
  (implies (svex-alist-partial-monotonic params subst)
           (svex-partial-monotonic params (lhatom-subst-zero x subst)))
  :hints(("Goal" :in-theory (e/d (lhatom-subst-zero
                                  svex-apply)
                                 (LOOKUP-WHEN-SVEX-ALIST-PARTIAL-MONOTONIC))
          :use ((:instance LOOKUP-WHEN-SVEX-ALIST-PARTIAL-MONOTONIC
                 (x subst) (param-keys params) (k (lhatom-var->name x)))))
         (and stable-under-simplificationp
              `(:expand ((:with svex-partial-monotonic-by-eval
                          ,(car (last clause)))
                         (:free (x env) (svex-eval (svex-var x) env)))))))

(defthm lhs-subst-zero-partial-monotonic
  (implies (svex-alist-partial-monotonic params subst)
           (svex-partial-monotonic params (lhs-subst-zero x subst)))
  :hints(("Goal" :in-theory (enable lhs-subst-zero)
          :induct t)
         (and stable-under-simplificationp
              `(:expand ((:with svex-partial-monotonic-by-eval
                          ,(car (last clause))))
                :use ((:instance lhatom-subst-zero-partial-monotonic
                       (x (lhrange->atom (car x)))))
                :in-theory (e/d (svex-apply)
                                (lhatom-subst-zero-partial-monotonic
                                 eval-of-lhatom-subst-zero
                                 eval-of-lhs-subst-zero))))))


(defthm svtv-name-lhs-map-subst-partial-monotonic
  (implies (svex-alist-partial-monotonic params subst)
           (svex-alist-partial-monotonic params (svtv-name-lhs-map-subst x subst)))
  :hints(("Goal" :in-theory (enable svtv-name-lhs-map-subst))))




(encapsulate nil
  (local (defthm partial-monotonicity-of-fsm-eval-bind
           (implies (and (bind-free '((params . (SVARLIST-CHANGE-OVERRIDE
                                                 (SVTV-ASSIGNS-OVERRIDE-VARS
                                                  (FLATNORM-RES->ASSIGNS$INLINE (SVTV-DATA-OBJ->FLATNORM$INLINE OBJ))
                                                  (PHASE-FSM-CONFIG->OVERRIDE-CONFIG$INLINE
                                                   (SVTV-DATA-OBJ->PHASE-FSM-SETUP$INLINE OBJ)))
                                                 ':test)))
                                    (params))
                         (svex-alist-partial-monotonic params (fsm->values x))
                         (svex-alist-partial-monotonic params (fsm->nextstate x))
                         (svex-env-<<= prev-st1 prev-st2)
                         (svex-envlist-<<= ins1 ins2)
                         (svex-envlists-agree params ins1 ins2)
                         (equal (len ins1) (len ins2))
                         (not (intersectp-equal (svarlist-fix params) (svex-alist-keys (fsm->nextstate x)))))
                    (svex-envlist-<<= (fsm-eval ins1 prev-st1 x)
                                      (fsm-eval ins2 prev-st2 x)))))
  (local (defthm svex-alistlist-eval-of-take
           (equal (svex-alistlist-eval (take n x) env)
                  (take n (svex-alistlist-eval x env)))
           :hints(("Goal" :in-theory (e/d (take svex-alistlist-eval)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))
                   :induct (take n x)
                   :expand ((svex-alist-eval nil env))))))
  
  (local (defthm my-svtv-fsm-run-is-fsm-run
           (equal (svtv-fsm-run (svex-alistlist-eval ins env)
                                prev-st x outvars
                                :override-vals (svex-alistlist-eval override-vals env)
                                :override-tests (svex-alistlist-eval override-tests env))
                  (fsm-run
                   (svex-alistlist-eval (svtv-fsm-to-fsm-inputsubsts
                                         (take (len outvars) ins)
                                         override-vals override-tests
                                         (svtv-fsm->namemap x))
                                        env)
                   prev-st
                   (svtv-fsm->renamed-fsm x)
                   outvars))
           :hints(("Goal" :in-theory (enable svtv-fsm-run-is-fsm-run)
                   :do-not-induct t))))

  (local (defun take-n-x-y-ind (n x y)
           (if (zp n)
               (list x y)
             (take-n-x-y-ind (1- n) (cdr x) (cdr y)))))
  
  (local (defthm svex-envlist-<=-of-take
           (implies (svex-envlist-<<= x y)
                    (svex-envlist-<<= (take n x) (take n y)))
           :hints(("Goal" :in-theory (e/d (svex-envlist-<<= take)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))
                   :induct (take-n-x-y-ind n x y)))))

  (local (defthm svex-envlists-agree-of-take
           (implies (svex-envlists-agree keys x y)
                    (svex-envlists-agree keys (take n x) (take n y)))
           :hints(("Goal" :in-theory (e/d (svex-envlists-agree take)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))
                   :induct (take-n-x-y-ind n x y)))))

  (local (defthm len-of-take
           (equal (len (take n x)) (nfix n))
           :hints(("Goal" :in-theory (enable take)))))
  
  (defthm svtv-data-obj-pipeline-partial-monotonic-p
    (implies (and (svtv-data$ap (svtv-data-obj-to-stobj-logic obj))
                  (svtv-data-obj->flatnorm-validp obj)
                  (svtv-data-obj->flatten-validp obj)
                  (svtv-data-obj->phase-fsm-validp obj)
                  (svtv-data-obj->cycle-fsm-validp obj)
                  (svtv-data-obj->pipeline-validp obj)
                  (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup obj))
                  (svex-alist-check-monotonic (pipeline-setup->initst (svtv-data-obj->pipeline-setup obj)))
                  (svex-alistlist-check-monotonic (svtv-data-obj-pipeline-substs obj)))
             (svex-alist-partial-monotonic
              (svtv-input-substs-extract-override-vars
               (svtv-data-obj-pipeline-substs obj))
              (svtv-data-obj->pipeline obj)))
    :hints (("goal"
             :in-theory (e/d ;; svtv-fsm-run-is-fsm-run
                         (fsm-run
                          svtv-data-obj-pipeline-substs
                          svtv-fsm->renamed-fsm)
                         (eval-of-svtv-fsm-to-fsm-inputsubsts)))
            (and stable-under-simplificationp
                 `(:expand ((:with svex-alist-partial-monotonic-by-eval
                             ,(car (last clause)))))))))
                



(defthmd svex-envs-agree-is-equal-of-extract
  (equal (svex-envs-agree vars x y)
         (equal (svex-env-extract vars x)
                (svex-env-extract vars y)))
  :hints(("Goal" :in-theory (enable svex-env-extract
                                    svex-envs-agree))))



;; Macro to apply the above theorem to prove a theorem like
;; my-svtv-partial-monotonic, in comment at top

(defconst *svtv-partial-monotonic-from-export-template*
  '(encapsulate nil
     (local (defthm <export>-pipeline-is-<svtv>-outexprs
              (equal (svtv-data-obj->pipeline (<export>))
                     (svtv->outexprs (<svtv>)))
              :hints(("Goal" :in-theory (enable (<svtv>) (<export>))))))
     (local (defthm <export>-mono-conditions
              (let ((obj (<export>)))
                (and (svtv-data-obj->flatnorm-validp obj)
                     (svtv-data-obj->flatten-validp obj)
                     (svtv-data-obj->phase-fsm-validp obj)
                     (svtv-data-obj->cycle-fsm-validp obj)
                     (svtv-data-obj->pipeline-validp obj)
                     (flatnorm-setup->monotonify (svtv-data-obj->flatnorm-setup obj))
                     (svex-alist-check-monotonic (pipeline-setup->initst (svtv-data-obj->pipeline-setup obj)))
                     (svex-alistlist-check-monotonic (svtv-data-obj-pipeline-substs obj))))
              :hints(("Goal" :in-theory (enable (<export>))))))

     (make-event
      `(defconst *<svtv>-override-test-vars*
         ',(svtv-input-substs-extract-override-vars
            (svtv-data-obj-pipeline-substs (<export>)))))

     (make-event
      `(define <svtv>-override-test-vars ()
         :returns (vars svarlist-p)
         ',*<svtv>-override-test-vars*))
     
     (local (defthm override-vars-of-<export>
              (equal (svtv-input-substs-extract-override-vars
                      (svtv-data-obj-pipeline-substs (<export>)))
                     (<svtv>-override-test-vars))
              :hints(("Goal" :in-theory (enable (<export>) (<svtv>-override-test-vars))))))

     (defthm <svtv>-partial-monotonic
       (svex-alist-partial-monotonic (<svtv>-override-test-vars)
                                     (svtv->outexprs (<svtv>)))
       :hints (("goal" :use ((:instance svtv-data-obj-pipeline-partial-monotonic-p (obj (<export>)))))))

     (defthmd <svtv>-monotonicity
       (implies (and (svex-envs-agree (<svtv>-override-test-vars) env1 env2)
                     (svex-env-<<= env1 env2))
                (svex-env-<<= (svtv-run (<svtv>) env1)
                              (svtv-run (<svtv>) env2)))
       :hints (("goal" :use <svtv>-partial-monotonic
                :in-theory '(svtv-run
                             make-fast-alist
                             svex-envs-agree-is-equal-of-extract
                             eval-when-svex-alist-partial-monotonic
                             return-type-of-svex-alist-eval-for-symbolic
                             SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-EXTRACT-2
                             SVEX-ENV-FIX-UNDER-SVEX-ENV-EQUIV
                             SVEX-ALIST-EVAL-OF-SVEX-ALIST-FIX-X
                             SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-1
                             SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ENV-<<=-2
                             svex-env-equiv-refines-svex-envs-similar
                             SVEX-ENV-EXTRACT-SVEX-ENV-EQUIV-CONGRUENCE-ON-ENV
                             svex-env-equiv-is-an-equivalence
                             SVEX-ALIST-EVAL-SVEX-ENV-EQUIV-CONGRUENCE-ON-ENV))))))

(define svtv-data-partial-monotonic-errmsg ((svtv svtv-p) svtv-data)
  (b* (((unless (svtv-data->flatten-validp svtv-data))
        "Flatten not valid")
       ((unless (svtv-data->flatnorm-validp svtv-data))
        "Flatnorm not valid")
       ((unless (svtv-data->phase-fsm-validp svtv-data))
        "Phase-fsm not valid")
       ((unless (svtv-data->cycle-fsm-validp svtv-data))
        "Cycle-fsm not valid")
       ((unless (svtv-data->pipeline-validp svtv-data))
        "Pipeline not valid")
       ((unless (flatnorm-setup->monotonify (svtv-data->flatnorm-setup svtv-data)))
        "Monotonify not set in flatnorm-setup")
       ((unless (hons-equal (svtv->outexprs svtv)
                            (svtv-data->pipeline svtv-data)))
        "Svtv->outexprs doesn't match svtv-data->pipeline"))
    nil))

(defun def-svtv-partial-monotonic-fn (svtv-name export-name pkg-sym)
  (declare (xargs :mode :program))
  (acl2::template-subst *svtv-partial-monotonic-from-export-template*
                        :atom-alist `((<svtv> . ,svtv-name)
                                      (<export> . ,export-name))
                        :str-alist `(("<SVTV>" . ,(symbol-name svtv-name))
                                     ("<EXPORT>" . ,(symbol-name export-name)))
                        :pkg-sym (or pkg-sym svtv-name)))


(defmacro def-svtv-partial-monotonic (svtv export &key pkg-sym)
  (def-svtv-partial-monotonic-fn svtv export pkg-sym))
    
(defxdoc def-svtv-partial-monotonic
  :parents (svtv-data)
  :short "Prove that an SVTV is monotonic in all variables except override tests."
  :long "
<p>Usage:</p>
@({
 (def-svtv-partial-monotonic <svtv-name> <export-name>)
 })

<p>Prerequisite: The SVTV must be defined with @(see defsvtv$) or @(see
defsvtv$-phasewise) (or otherwise result from populating a @(see svtv-data)
stobj), and the contents of the stobj thus populated must be exported into a
regular object @('<export-name>') using @('def-svtv-data-export').
Additionally, the setting for the @('monotonify') argument of the defsvtv$ form
must have been @('t') (the default).</p>

<p>This proves two theorems about the SVTV:</p>

@({
 (svex-alist-partial-monotonic (<svtv>-override-test-vars)
                               (svtv->outexprs (<svtv>)))
 })

<p>and a direct consequence:</p>

@({
 (implies (and (svex-envs-agree (<svtv>-override-test-vars) env1 env2)
               (svex-env-<<= env1 env2))
          (svex-env-<<= (svtv-run (<svtv>) env1)
                        (svtv-run (<svtv>) env2)))
 })

<p>This is useful for overrides; see @(see def-svtv-overrides-correct).</p>")

