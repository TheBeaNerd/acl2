; Centaur SV Hardware Verification
; Copyright (C) 2016 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "SV")

(include-book "../mods/compile")
(include-book "fsm-base")
(include-book "expand")
(include-book "../svex/monotonify")
(include-book "../svex/override-types")
(local (include-book "../svex/alist-thms"))

(local (include-book "std/lists/sets" :dir :system))

(local (std::add-default-post-define-hook :fix))


(define svtv-wires->lhses! ((x string-listp)
                            (modidx natp)
                            (moddb moddb-ok)
                            aliases)
  :guard (svtv-mod-alias-guard modidx moddb aliases)
  :returns (mv errs (lhses lhslist-p))
  (b* (((when (atom x))
        (mv nil nil))
       ((mv err lhs) (svtv-wire->lhs! (car x) modidx moddb aliases))
       ((mv errs lhses) (svtv-wires->lhses! (cdr x) modidx moddb aliases)))
    (mv (append-without-guard err errs) (cons lhs lhses))))
    


(local (include-book "std/osets/element-list" :dir :system))
(local (deflist svarlist
         :elt-type svar
         :true-listp t
         :elementp-of-nil nil))

(defprod flatten-res
  ((assigns assigns)
   (fixups assigns)
   (constraints constraintlist)
   (var-decl-map var-decl-map-p)))

(defprod flatnorm-res
  ((assigns svex-alist)
   (delays svex-alist)
   (constraints constraintlist)))

(define flatten-res-vars ((x flatten-res-p))
  (b* (((flatten-res x)))
    (append (assigns-vars x.assigns)
            (assigns-vars x.fixups)
            (constraintlist-vars x.constraints))))


;; simple wrapper for svex-design-flatten that wraps the result into a flatten-res
(define svtv-design-flatten ((x design-p)
                             &key
                             ((moddb "overwritten") 'moddb)
                             ((aliases "overwritten") 'aliases))
  :guard (svarlist-addr-p (modalist-vars (design->modalist x)))
  :returns (mv err
               (res flatten-res-p)
               new-moddb new-aliases)
  :guard-hints (("goal" :in-theory (enable modscope-okp modscope-local-bound modscope->modidx)))
  (b* (((mv err assigns fixups constraints moddb aliases) (svex-design-flatten x))
       ((mv aliases var-decl-map)
        (if err
            (mv aliases nil)
          (time$ (aliases-indexed->named aliases (make-modscope-top
                                                  :modidx (moddb-modname-get-index
                                                           (design->top x) moddb))
                                         moddb)
                 :msg "; aliases renamed: ~st sec, ~sa bytes.~%"))))
    (mv err
        (make-flatten-res :assigns assigns :fixups fixups :constraints constraints
                          :var-decl-map var-decl-map)
        moddb aliases))
  ///
  (defretd normalize-stobjs-of-<fn>
    (implies (syntaxp (not (and (equal aliases ''nil)
                                (equal moddb ''nil))))
             (equal <call>
                    (let ((moddb nil) (aliases nil)) <call>)))
    :hints(("Goal" :in-theory (enable normalize-stobjs-of-svex-design-flatten))))

  (defret moddb-okp-of-<fn>
    (implies (not err)
             (and (moddb-mods-ok new-moddb)
                  (moddb-basics-ok new-moddb))))

  (defret modname-of-<fn>
    (implies (not err)
             (moddb-modname-get-index (design->top x) new-moddb)))

  ;; (defret modidx-of-<fn>
  ;;   (implies (not err)
  ;;            (< (moddb-modname-get-index (design->top x) new-moddb)
  ;;               (nfix (nth *moddb->nmods1* new-moddb))))
  ;;   :rule-classes :linear)

  (defret totalwires-of-<fn>
    (implies (not err)
             (<= (moddb-mod-totalwires
                  (moddb-modname-get-index (design->top x) new-moddb) new-moddb)
                 (len new-aliases)))
    :rule-classes :linear)

  (defret svarlist-addr-p-aliases-vars-of-<fn>
    (implies (not err)
             (svarlist-addr-p (aliases-vars new-aliases)))))


(defprod flatnorm-setup
  ((monotonify booleanp)))

(define svtv-normalize-assigns ((flatten flatten-res-p) aliases
                                (setup flatnorm-setup-p))
  :returns (res flatnorm-res-p)
  :guard (svarlist-boundedp (flatten-res-vars flatten) (aliass-length aliases))
  :guard-hints (("goal" :in-theory (enable flatten-res-vars)))
  (b* (((flatten-res flatten))
       ((mv assigns delays constraints)
        (svex-normalize-assigns flatten.assigns flatten.fixups flatten.constraints flatten.var-decl-map aliases))
       ((flatnorm-setup setup))
       (assigns (if setup.monotonify
                    (svex-alist-monotonify assigns)
                  assigns)))
    (make-flatnorm-res :assigns assigns :delays delays :constraints constraints))
  ///
  (defret svarlist-addr-p-assigns-vars-of-<fn>
    (b* (((flatnorm-res res)))
      (implies (svarlist-addr-p (aliases-vars aliases))
               (svarlist-addr-p (svex-alist-vars res.assigns)))))

  (defret svarlist-addr-p-assigns-keys-of-<fn>
    (b* (((flatnorm-res res)))
      (implies (svarlist-addr-p (aliases-vars aliases))
               (svarlist-addr-p (svex-alist-keys res.assigns)))))

  (defret svarlist-addr-p-delay-vars-of-<fn>
    (b* (((flatnorm-res res)))
      (implies (svarlist-addr-p (aliases-vars aliases))
               (svarlist-addr-p (svex-alist-vars res.delays)))))

  (defret svarlist-addr-p-delay-keys-of-<fn>
    (b* (((flatnorm-res res)))
      (implies (svarlist-addr-p (aliases-vars aliases))
               (svarlist-addr-p (svex-alist-keys res.delays)))))

  (defret svarlist-addr-p-constraint-vars-of-<fn>
    (b* (((flatnorm-res res)))
      (implies (svarlist-addr-p (aliases-vars aliases))
               (svarlist-addr-p (constraintlist-vars res.constraints)))))

  (defret no-duplicate-assigns-keys-of-<fn>
    (b* (((flatnorm-res res)))
      (no-duplicatesp-equal (svex-alist-keys res.assigns))))

  (defret no-duplicate-delay-keys-of-<fn>
    (b* (((flatnorm-res res)))
      (no-duplicatesp-equal (svex-alist-keys res.delays)))))


(defsection no-duplicate-svex-alist-keys-of-fast-alist-clean
  (local (include-book "std/alists/fast-alist-clean" :dir :system))
  (local (in-theory (enable fast-alist-clean)))
  (defthm svex-alist-p-of-fast-alist-fork
    (implies (and (svex-alist-p x)
                  (svex-alist-p y))
             (svex-alist-p (fast-alist-fork x y))))
  (local
   (progn
     (defthm cdr-last-of-svex-alist-p
       (implies (svex-alist-p x)
                (equal (cdr (last x)) nil)))))

  (defthm svex-alist-p-of-fast-alist-clean
     (implies (svex-alist-p x)
              (svex-alist-p (fast-alist-clean x))))

   (local
    (progn
      (defthm no-duplicate-svex-alist-keys-of-fast-alist-fork
        (implies  (no-duplicatesp-equal (svex-alist-keys y))
                  (no-duplicatesp-equal (svex-alist-keys (fast-alist-fork x y))))
        :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup))))
      (defthm svex-alist-keys-of-cdr-last
        (equal (svex-alist-keys (cdr (last x))) nil)
        :hints(("Goal" :in-theory (enable svex-alist-keys))))))

   (defthm no-duplicate-svex-alist-keys-of-fast-alist-clean
     (no-duplicatesp-equal (svex-alist-keys (fast-alist-clean x)))
     :hints(("Goal" :in-theory (enable svex-alist-keys))))

   (defthm svar-map-p-of-fast-alist-fork
     (implies (and (svar-map-p x)
                   (svar-map-p y))
              (svar-map-p (fast-alist-fork x y))))
   (defthm svar-map-p-of-fast-alist-clean
     (implies (svar-map-p x)
              (svar-map-p (fast-alist-clean x)))
     :hints(("Goal" :in-theory (enable fast-alist-clean))))

   (defthm no-duplicate-keys-of-fast-alist-fork
     (implies (no-duplicatesp-equal (alist-keys y))
              (no-duplicatesp-equal (alist-keys (fast-alist-fork x y)))))

   (defthm no-duplicate-keys-of-fast-alist-clean
     (no-duplicatesp-equal (alist-keys (fast-alist-clean x))))

   (in-theory (disable fast-alist-clean)))

(deftagsum svtv-assigns-override-config
  (:omit ((vars svarlist-p)))
  (:include ((vars svarlist-p)))
  :layout :list)


(local (defthm subsetp-intersection
         (subsetp-equal (intersection-equal a b) a)))

(local (defthm subsetp-set-diff
         (subsetp-equal (set-difference-equal a b) a)))

(define svtv-assigns-override-vars ((assigns svex-alist-p)
                                    (config svtv-assigns-override-config-p))
  :returns (override-vars svarlist-p)
  (svtv-assigns-override-config-case config
    :omit (acl2::hons-set-diff (svex-alist-keys assigns) config.vars)
    :include (acl2::hons-intersection (svex-alist-keys assigns) config.vars))
  ///
  (defret <fn>-subset-of-keys
    (subsetp-equal override-vars (svex-alist-keys assigns))))


       

(defprod phase-fsm-config
  ((override-config svtv-assigns-override-config-p))
  :layout :list)

(local (defthm svex-alist-keys-of-svex-alist-compose
         (Equal (svex-alist-keys (svex-alist-compose x a))
                (svex-alist-keys x))
         :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-compose)))))

(define svtv-flatnorm-apply-overrides ((flatnorm flatnorm-res-p)
                                       (config svtv-assigns-override-config-p))
  :returns (mv (assign-alist svex-alist-p)
               (delay-alist svex-alist-p))
  (b* (((flatnorm-res flatnorm))
       (override-alist (svarlist-to-override-alist
                        (svtv-assigns-override-vars flatnorm.assigns config)))
       ((acl2::with-fast override-alist))
       (overridden-assigns (svex-alist-compose flatnorm.assigns override-alist))
       (overridden-delays (svex-alist-compose flatnorm.delays
                                              override-alist)))
    (mv overridden-assigns overridden-delays))
  ///
  (defret svex-alist-keys-of-<fn>-assigns
    (equal (svex-alist-keys assign-alist)
           (svex-alist-keys (flatnorm-res->assigns flatnorm))))

  (defret svex-alist-keys-of-<fn>-delays
    (equal (svex-alist-keys delay-alist)
           (svex-alist-keys (flatnorm-res->delays flatnorm)))))

(local (defthm append-subset-under-set-equiv
           (implies (subsetp a b)
                    (set-equiv (append b a) b))))

(define phase-fsm-composition-p ((phase-fsm fsm-p)
                                 (flatnorm flatnorm-res-p)
                                 (config phase-fsm-config-p))
  (b* (((phase-fsm-config config))
       ((mv overridden-assigns overridden-delays)
        (svtv-flatnorm-apply-overrides flatnorm config.override-config))
       ((fsm phase-fsm)))
    (and (ec-call (netevalcomp-p phase-fsm.values overridden-assigns))
         ;; Need this because if we have signals that are in the
         ;; original assigns (therefore in the overridden assigns)
         ;; but not in the updates, then a delayed version of such a
         ;; signal would be bound to the signal itself in the
         ;; nextstates, effectively creating a new primary input. It
         ;; is always OK to bind unneeded signals to X in the
         ;; updates.
         (set-equiv (svex-alist-keys phase-fsm.values) (svex-alist-keys overridden-assigns))
         ;; Eventually weaken this to allow for sequential
         ;; equivalence under some initial state/initial primary
         ;; input assumption.
         (ec-call
          (svex-alist-eval-equiv! phase-fsm.nextstate
                                  (svex-alist-compose overridden-delays phase-fsm.values)))))
  ///
  (defcong fsm-eval-equiv equal (phase-fsm-composition-p phase-fsm flatnorm config) 1
    :hints(("Goal" :in-theory (enable fsm-eval-equiv))))

  (defcong flatnorm-res-equiv equal (phase-fsm-composition-p phase-fsm flatnorm config) 2)

  (defthm phase-fsm-composition-p-implies-no-duplicate-nextstate-keys
    (implies (and (phase-fsm-composition-p phase-fsm flatnorm config)
                  (no-duplicatesp-equal (svex-alist-keys (flatnorm-res->delays flatnorm))))
             (no-duplicatesp-equal (svex-alist-keys (fsm->nextstate phase-fsm))))))





(defprod phase-fsm-params
  ((scc-selfcompose-limit maybe-natp
                          "Limit on the number of times to self-compose a set
of signals that form a strongly connnected component in the dependency graph,
i.e. they all depend on each other.  By default this is NIL, which means that
we will compose together such an SCC N times where N is the size of the SCC --
this is the theoretical limit on how many iterations are needed to come to a
fixed point (assuming the expressions are X-monotonic).  But since this
behavior can cause a blowup in the size of the expressions, setting the limit
to a small number is usually practical if there is such a problem.")
   (rewrite booleanp "Apply some rewriting during the composition process -- default T."
            :default t)))

(define svtv-compose-assigns/delays ((flatnorm flatnorm-res-p)
                                     (config phase-fsm-config-p)
                                     (params phase-fsm-params-p))
  :returns (fsm fsm-p)
  (b* (((flatnorm-res flatnorm))
       ((phase-fsm-config config))
       ((phase-fsm-params params))
       (override-alist (svarlist-to-override-alist
                        (svtv-assigns-override-vars flatnorm.assigns config.override-config)))
       (overridden-assigns (with-fast-alist override-alist
                             (svex-alist-compose flatnorm.assigns override-alist)))
       (updates1 (make-fast-alist
                  (with-fast-alist overridden-assigns
                    (svex-assigns-compose overridden-assigns
                                          :rewrite params.rewrite
                                          :scc-selfcompose-limit params.scc-selfcompose-limit))))
       (updates2 (fast-alist-fork updates1 (make-fast-alist (svex-alist-compose override-alist updates1))))
       (nextstates (make-fast-alist (svex-alist-compose flatnorm.delays updates2))))
    (fast-alist-free updates2)
    (make-fsm :values updates1 :nextstate nextstates))
  ///
  (defret no-duplicate-nextstates-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys (flatnorm-res->delays flatnorm)))
             (no-duplicatesp-equal (svex-alist-keys (fsm->nextstate fsm)))))

  (local (defthmd svex-alist-keys-when-svex-alist-p
           (implies (svex-alist-p x)
                    (equal (svex-alist-keys x)
                           (alist-keys x)))
           :hints(("Goal" :in-theory (enable svex-alist-p svex-alist-keys alist-keys)))))

  (local (defthmd hons-assoc-equal-iff-member-alist-keys
           (iff (hons-assoc-equal k a)
                (member-equal k (alist-keys a)))
           :hints(("Goal" :in-theory (enable alist-keys hons-assoc-equal)))))

  (local (defthm svex-alist-keys-of-fast-alist-fork-under-set-equiv
           (implies (and (svex-alist-p b)
                         (svex-alist-p a))
                    (set-equiv (svex-alist-keys (fast-alist-fork a b))
                               (append (svex-alist-keys a) (svex-alist-keys b))))
           :hints(("Goal" :in-theory (e/d (svex-alist-keys
                                           alist-keys
                                           svex-alist-keys-when-svex-alist-p
                                           hons-assoc-equal-iff-member-alist-keys)
                                          (member-svex-alist-keys))))))
  
  

  (local (defthm hons-assoc-equal-of-append
           (equal (hons-assoc-equal k (append a b))
                  (or (hons-assoc-equal k a)
                      (hons-assoc-equal k b)))))

  (local (defthm hons-assoc-equal-of-fast-alist-fork
           (Equal (hons-assoc-equal k (fast-alist-fork a b))
                  (hons-assoc-equal k (append b a)))
           :hints(("Goal" :in-theory (enable fast-alist-fork)
                   :induct (fast-alist-fork a b)))))

  (local (defthm cdr-hons-assoc-equal-when-svex-alist-p
           (implies (svex-alist-p x)
                    (iff (cdr (hons-assoc-equal k x))
                         (hons-assoc-equal k x)))))

  (local (Defthm fast-alist-fork-under-svex-alist-eval-equiv
           (implies (and (Svex-alist-p x)
                         (svex-alist-p y))
                    (svex-alist-eval-equiv (fast-alist-fork x y)
                                           (Append y x)))
           :hints(("Goal" :in-theory (enable svex-alist-eval-equiv
                                             svex-lookup)
                   :do-not-induct t))))

  (defret phase-fsm-composition-p-of-<fn>
    (phase-fsm-composition-p fsm flatnorm config)
    :hints (("goal" 
             :in-theory (enable svtv-flatnorm-apply-overrides
                                phase-fsm-composition-p
                                fsm-eval-equiv)))))


;; BOZO this could probably be broken into a few parts.
(define svtv-design-to-fsm ((x design-p)
                            &key
                            ((moddb "overwritten") 'moddb)
                            ((aliases "overwritten") 'aliases)
                            (override-all 't)
                            ((overrides string-listp) 'nil)
                            ((selfcompose-limit maybe-natp) 'nil)
                            (rewrite 't))
  :prepwork ((local (include-book "std/alists/fast-alist-clean" :dir :system))
             (local (defthm svex-alist-p-of-fast-alist-fork
                      (implies (and (svex-alist-p x)
                                    (svex-alist-p y))
                               (svex-alist-p (fast-alist-fork x y)))))
             (local (defthm cdr-last-of-svex-alist-p
                      (implies (svex-alist-p x)
                               (equal (cdr (last x)) nil))))
             (local (defthm svex-alist-p-of-fast-alist-clean
                      (implies (svex-alist-p x)
                               (svex-alist-p (fast-alist-clean x)))))

             (local (defthm no-duplicate-svex-alist-keys-of-fast-alist-fork
                      (implies  (no-duplicatesp-equal (svex-alist-keys y))
                                (no-duplicatesp-equal (svex-alist-keys (fast-alist-fork x y))))
                      :hints(("Goal" :in-theory (enable svex-alist-keys svex-lookup)))))
             (local (defthm svex-alist-keys-of-cdr-last
                      (equal (svex-alist-keys (cdr (last x))) nil)
                      :hints(("Goal" :in-theory (enable svex-alist-keys)))))
             (local (defthm no-duplicate-svex-alist-keys-of-fast-alist-clean
                      (no-duplicatesp-equal (svex-alist-keys (fast-alist-clean x)))
                      :hints(("Goal" :in-theory (enable svex-alist-keys)))))
             (local (in-theory (disable fast-alist-clean))))
  
  :returns (mv err
               (fsm (implies (not err)
                             (fsm-p fsm)))
               (new-moddb moddb-basics-ok) new-aliases)
  :guard (modalist-addr-p (design->modalist x))
  (b* (((mv err assigns delays & moddb aliases)
        (svex-design-flatten-and-normalize x))
       ((when err)
        (mv err nil moddb aliases))
       (modidx (moddb-modname-get-index (design->top x) moddb))
       ((mv err override-vars)
        (if override-all
            (mv nil (svex-alist-keys assigns))
          (b* (((mv errs lhses) (svtv-wires->lhses! overrides modidx moddb aliases))
               ((when errs)
                (mv (msg-list errs) nil)))
            (mv nil (set::intersect (set::mergesort (svex-alist-keys assigns))
                                    (set::mergesort (lhslist-vars lhses)))))))
       ((when err)
        (mv err nil moddb aliases))
       (override-alist (svarlist-to-override-alist override-vars))
       (overridden-assigns (with-fast-alist override-alist
                             (svex-alist-compose assigns override-alist)))
       (updates1 (make-fast-alist
                  (with-fast-alist overridden-assigns
                    (svex-assigns-compose overridden-assigns :rewrite rewrite
                                          :scc-selfcompose-limit selfcompose-limit))))
       (updates2 (svex-alist-compose override-alist updates1))
       (nextstates (with-fast-alist updates2 (svex-alist-compose delays updates2))))
    (mv nil
        (make-fsm :values updates1
                       :nextstate (fast-alist-clean nextstates))
        moddb aliases))
  ///
  (defret no-duplicate-nextstates-of-<fn>
    (implies (not err)
             (no-duplicatesp-equal (svex-alist-keys (fsm->nextstate fsm)))))

  (defret <fn>-normalize-stobjs
    (implies (syntaxp (and (not (equal moddb ''nil))
                           (not (equal aliases ''nil))))
             (equal <call>
                    (let ((moddb nil) (aliases nil)) <call>)))
    :hints(("Goal" :in-theory (enable normalize-stobjs-of-svex-design-flatten-and-normalize))))

  (defret moddb-mods-ok-of-<fn>
    (moddb-mods-ok new-moddb))

  (defret alias-length-of-<fn>
    (implies (not err)
             (equal (len new-aliases)
                    (moddb-mod-totalwires
                     (moddb-modname-get-index (design->top x) new-moddb)
                     new-moddb))))

  (defret modidx-of-<fn>
    (implies (not err)
             (moddb-modname-get-index (design->top x) new-moddb))
    :rule-classes (:rewrite
                   (:type-prescription :corollary
                    (implies (not err)
                             (natp (moddb-modname-get-index (design->top x) new-moddb)))))))
