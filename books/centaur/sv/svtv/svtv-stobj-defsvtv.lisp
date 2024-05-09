; Centaur SV Hardware Verification Tutorial
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

(include-book "svtv-stobj-pipeline")
(include-book "svtv-stobj-defcycle")
(include-book "process")
(include-book "centaur/misc/hons-remove-dups" :dir :System)
(include-book "preprocess")

(local (defthm svar-p-when-stringp
         (implies (stringp x)
                  (svar-p x))
         :hints(("Goal" :in-theory (enable svar-p)))))



(define defsvtv-compute-user-namemap ((ins true-list-listp)
                                      (overrides true-list-listp)
                                      (outs true-list-listp))
  :prepwork ((local (defthm svarlist-p-when-string-listp
                      (implies (string-listp x)
                               (svarlist-p x))
                      :hints(("Goal" :in-theory (enable svarlist-p)))))
             (local (defthm svtv-namemap-p-of-pairlis
                      (implies (and (string-listp y)
                                    (svarlist-p x)
                                    (equal (len x) (len y)))
                               (svtv-namemap-p (pairlis$ x y)))
                      :hints(("Goal" :in-theory (enable svtv-namemap-p pairlis$)))))
             (local (defthm string-listp-of-remove-dups
                      (implies (string-listp x)
                               (string-listp (remove-duplicates-equal x)))
                      :hints(("Goal" :in-theory (enable remove-duplicates-equal))))))
  :returns (user-names svtv-namemap-p)
  (b* ((strings (acl2::hons-remove-dups
                 (ec-call
                  (str::string-list-fix (append (strip-cars (alist-fix ins))
                                                (strip-cars (alist-fix overrides))
                                                (strip-cars (alist-fix outs))))))))
    (pairlis$ strings strings)))


(define defsvtv-probes-for-phases ((phase natp) (phases true-listp) (signal svar-p))
  :returns (probes svtv-probealist-p)
  (b* (((when (atom phases)) nil)
       (ent (car phases))
       ((when (svtv-dontcare-p ent))
        (defsvtv-probes-for-phases (1+ (lnfix phase)) (cdr phases) signal))
       ((unless (svar-p ent))
        (raise "Bad output entry: ~x0~%" ent)
        (defsvtv-probes-for-phases (1+ (lnfix phase)) (cdr phases) signal)))
    (cons (cons ent (make-svtv-probe :signal signal :time phase))
          (defsvtv-probes-for-phases (1+ (lnfix phase)) (cdr phases) signal))))

(local (defthm probealist-p-of-append
         (implies (and (svtv-probealist-p x)
                       (svtv-probealist-p y))
                  (svtv-probealist-p (append x y)))))

(define defsvtv-compute-probes ((outs true-list-listp))
  :returns (probes svtv-probealist-p)
  (if (atom outs)
      nil
    (if (atom (car outs))
        (defsvtv-compute-probes (cdr outs))
      (append (defsvtv-probes-for-phases 0 (cdar outs) (str-fix (caar outs)))
              (defsvtv-compute-probes (cdr outs))))))


(define phase-compute-input-alist ((phase natp) (ins true-list-listp))
  :returns (alist svex-alist-p)
  (b* (((when (atom ins)) nil)
       ((unless (consp (car ins)))
        (phase-compute-input-alist phase (cdr ins)))
       (signal (str-fix (caar ins)))
       (ent (nth phase (cdar ins)))
       ((when (svtv-dontcare-p ent))
        (phase-compute-input-alist phase (cdr ins)))
       ((unless (svtv-baseentry-p ent))
        (if (svtv-entry-p ent)
            (raise "SVTV entries such as ~x0 are only allowed in overrides." ent)
          (raise "Bad SVTV entry: ~x0." ent))
        (phase-compute-input-alist phase (cdr ins)))
       (val (svtv-baseentry-svex ent)))
    (cons (cons signal val)
          (phase-compute-input-alist phase (cdr ins)))))

(define phase-compute-override-val-alist ((phase natp) (overrides true-list-listp))
  :returns (alist svex-alist-p)
  :prepwork ((local (in-theory (enable svtv-entry-p))))
  (b* (((when (atom overrides)) nil)
       ((unless (consp (car overrides)))
        (phase-compute-override-val-alist phase (cdr overrides)))
       (signal (str-fix (caar overrides)))
       (ent (nth phase (cdar overrides)))
       ((unless (svtv-entry-p ent))
        (raise "Bad SVTV entry: ~x0." ent)
        (phase-compute-override-val-alist phase (cdr overrides)))
       ((when (svtv-dontcare-p ent))
        (phase-compute-override-val-alist phase (cdr overrides)))
       (val (if (svtv-condoverride-p ent)
                (b* (((svtv-condoverride ent)))
                  (svtv-baseentry-svex ent.value))
              (svtv-baseentry-svex ent))))
    (cons (cons signal val)
          (phase-compute-override-val-alist phase (cdr overrides)))))


(define phase-compute-override-test-alist ((phase natp) (overrides true-list-listp))
  :returns (alist svex-alist-p)
  :prepwork ((local (in-theory (enable svtv-entry-p))))
  (b* (((when (atom overrides)) nil)
       ((unless (consp (car overrides)))
        (phase-compute-override-test-alist phase (cdr overrides)))
       (signal (str-fix (caar overrides)))
       (ent (nth phase (cdar overrides)))
       ((unless (svtv-entry-p ent))
        (raise "Bad SVTV entry: ~x0." ent)
        (phase-compute-override-val-alist phase (cdr overrides)))
       ((when (svtv-dontcare-p ent))
        (phase-compute-override-test-alist phase (cdr overrides)))
       (test (if (svtv-condoverride-p ent)
                (b* (((svtv-condoverride ent)))
                  (svtv-baseentry-svex ent.test))
               (svex-quote -1))))
    (cons (cons signal test)
          (phase-compute-override-test-alist phase (cdr overrides)))))
    
(define svtv-compute-input-phases ((phase natp) (nphases natp)
                                   (ins true-list-listp))
  :guard (<= phase nphases)
  :measure (nfix (- (nfix nphases) (nfix phase)))
  :returns (inputs svex-alistlist-p)
  (b* (((when (mbe :logic (zp (- (nfix nphases) (nfix phase)))
                   :exec (eql phase nphases)))
        nil)
       (inputs (phase-compute-input-alist phase ins)))
    (cons inputs
          (svtv-compute-input-phases (1+ (lnfix phase)) nphases ins))))

(define svtv-compute-override-val-phases ((phase natp) (nphases natp)
                                          (overrides true-list-listp))
  :guard (<= phase nphases)
  :measure (nfix (- (nfix nphases) (nfix phase)))
  :returns (override-vals svex-alistlist-p)
  (b* (((when (mbe :logic (zp (- (nfix nphases) (nfix phase)))
                   :exec (eql phase nphases)))
        nil)
       (override-vals (phase-compute-override-val-alist phase overrides)))
    (cons override-vals
          (svtv-compute-override-val-phases (1+ (lnfix phase)) nphases overrides))))

(define svtv-compute-override-test-phases ((phase natp) (nphases natp)
                                           (overrides true-list-listp))
  :guard (<= phase nphases)
  :measure (nfix (- (nfix nphases) (nfix phase)))
  :returns (override-tests svex-alistlist-p)
  (b* (((when (mbe :logic (zp (- (nfix nphases) (nfix phase)))
                   :exec (eql phase nphases)))
        nil)
       (override-tests (phase-compute-override-test-alist phase overrides)))
    (cons override-tests
          (svtv-compute-override-test-phases (1+ (lnfix phase)) nphases overrides))))

(define svtv-lines-max-length ((x true-list-listp))
  :returns (max-len natp :rule-classes :type-prescription)
  (if (atom x)
      0
    (if (consp (car x))
        (max (len (cdar x))
             (svtv-lines-max-length (cdr x)))
      (svtv-lines-max-length (cdr x)))))


(define defsvtv-compute-inputs ((ins true-list-listp)
                                (overrides true-list-listp))
  :returns (mv (nphases natp :rule-classes :type-prescription)
               (inputs svex-alistlist-p)
               (override-vals svex-alistlist-p)
               (override-tests svex-alistlist-p))
  (b* ((nphases (max (svtv-lines-max-length ins) (svtv-lines-max-length overrides))))
    (mv nphases
        (svtv-compute-input-phases 0 nphases ins)
        (svtv-compute-override-val-phases 0 nphases overrides)
        (svtv-compute-override-test-phases 0 nphases overrides))))
       

(define svex-x-subst ((vars svarlist-p))
  :returns (subst svex-alist-p)
  (pairlis$ (svarlist-fix vars)
            (make-list (len vars) :initial-element (svex-x)))
  ///
  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys subst)
           (svarlist-fix vars))))

(define user-svtv-lines-to-svtv-lines ((lines true-list-listp)
                                       (namemap svtv-name-lhs-map-p))
  :returns (entries svtv-lines-p)
  (b* (((when (atom lines)) nil)
       ((unless (consp (car lines)))
        (user-svtv-lines-to-svtv-lines (cdr lines) namemap))
       ((cons name entrylist) (car lines))
       ((unless (svtv-entrylist-p entrylist))
        (raise "bad entrylist: ~x0~%" (car lines))
        (user-svtv-lines-to-svtv-lines (cdr lines) namemap)))
    (cons (make-svtv-line :lhs (cdr (hons-assoc-equal (str-fix name) namemap))
                          :entries entrylist)
          (user-svtv-lines-to-svtv-lines (cdr lines) namemap))))
              
      
(local (defthm true-list-listp-of-append
         (implies (and (true-list-listp x)
                       (true-list-listp y))
                  (true-list-listp (append x y)))))

(define svtv-lines-expand ((lines true-list-listp)
                           (nphases natp)
                           (namemap svtv-name-lhs-map-p))
  :returns (new-lines true-list-listp)
  (b* (((when (atom lines)) nil)
       ((unless (consp (car lines)))
        (svtv-lines-expand (cdr lines) nphases namemap))
       ((cons name entrylist) (car lines))
       ((unless (svtv-entrylist-p entrylist))
        (raise "bad entrylist: ~x0~%" (car lines))
        (svtv-lines-expand (cdr lines) nphases namemap))
       (lhs (cdr (hons-assoc-equal (str-fix name) namemap)))
       (width (lhs-width lhs))
       (ext-entrylist (svtv-extend-entrylist entrylist nphases 'acl2::_ 'acl2::_ width)))
    (cons (cons name ext-entrylist)
          (svtv-lines-expand (cdr lines) nphases namemap))))
    



(define svtv-compute-trivial-cycle ((pre-simplify booleanp) svtv-data
                                    (simp svex-simpconfig-p))
  :guard (and (svtv-data->phase-fsm-validp svtv-data)
              (svtv-data->flatnorm-validp svtv-data)
              (not (svtv-data->cycle-fsm-validp svtv-data))
              (not (svtv-data->pipeline-validp svtv-data)))
  :returns (new-svtv-data)
  (b* ((cycle-phases (list (make-svtv-cyclephase :constants nil
                                                 :inputs-free t
                                                 :outputs-captured t)))
       (svtv-data (update-svtv-data->cycle-phases cycle-phases svtv-data))
       (svtv-data (svtv-data-compute-cycle-fsm svtv-data simp))

       (svtv-data (svtv-data-maybe-rewrite-cycle-fsm pre-simplify svtv-data :verbosep t)))
    svtv-data)
  ///
  
  (defret svtv-data$c-get-of-<fn>
    (implies (and (equal key (svtv-data$c-field-fix k))
                  (not (equal key :cycle-phases))
                  (not (equal key :cycle-fsm))
                  (not (equal key :cycle-fsm-validp)))
             (equal (svtv-data$c-get k new-svtv-data)
                    (svtv-data$c-get key svtv-data))))

  (defret cycle-fsm-validp-of-<fn>
    (svtv-data$c->cycle-fsm-validp new-svtv-data)))


(define defsvtv-compute-pipeline-setup ((outs+ true-list-listp)
                                        (ins true-list-listp)
                                        (overrides true-list-listp)
                                        (initial-state-vars)
                                        (statevars svarlist-p)
                                        (namemap svtv-name-lhs-map-p))
  :returns (setup pipeline-setup-p)
  (b* ((probes (defsvtv-compute-probes outs+))
       (nphases (svtv-lines-max-length outs+))
       (ins (svtv-lines-expand ins nphases namemap))
       (overrides (svtv-lines-expand overrides nphases namemap))
       ((mv ?in-nphases inputs override-vals override-tests) (defsvtv-compute-inputs ins overrides))
       (initst
        (make-fast-alist
         (if initial-state-vars
             (svex-identity-subst statevars)
           (svex-x-subst statevars)))))
    (make-pipeline-setup :probes probes
                         :inputs (make-fast-alists inputs)
                         :override-vals (make-fast-alists override-vals)
                         :override-tests (make-fast-alists override-tests)
                         :initst initst))
  ///
  (defret initst-keys-of-<fn>
    (equal (svex-alist-keys (pipeline-setup->initst setup))
           (svarlist-fix statevars) )))
  

(defthm svex-alist-keys-of-svtv-data->cycle-nextstate
  (implies (and (svtv-data$ap svtv-data)
                ;; (svtv-data$c->fsm-validp svtv-data)
                (svtv-data$c->cycle-fsm-validp svtv-data))
           (equal (svex-alist-keys (fsm->nextstate (svtv-data$c->cycle-fsm svtv-data)))
                  (svex-alist-keys (fsm->nextstate (svtv-data$c->phase-fsm svtv-data)))))
  :hints(("Goal" :in-theory (enable svtv-data$ap))))






(defprod defsvtv-args
  ((name symbolp)
   (stages true-list-listp)
   (inputs true-list-listp)
   (overrides true-list-listp)
   (outputs true-list-listp)
   (internals true-list-listp)
   (design design-p)
   (design-const symbolp)
   (labels symbol-listp)
   (phase-config phase-fsm-config-p
                 :default (make-phase-fsm-config
                           :override-config (make-svtv-assigns-override-config-omit)))
   (clocks svarlist-p :default nil)
   (phase-scc-limit maybe-natp :default nil)
   (monotonify booleanp :default t)
   (simplify booleanp :default t)
   (pre-simplify booleanp :default t)
   (pipe-simp svex-simpconfig-p)
   (cycle-phases svtv-cyclephaselist-p)
   (cycle-phases-p)
   (cycle-simp svex-simpconfig-p)
   ;; state-machine
   (initial-state-vars booleanp)
   ;; keep-final-state
   ;; keep-all-states
   (define-macros :default t)
   (define-mod)
   parents
   short
   long
   form)
  :layout :list)

(define keyword-value-list-add-quotes ((quoted-keys symbol-listp)
                                       (args acl2::keyword-value-listp))
  :returns (new-args (implies (acl2::keyword-value-listp args)
                              (acl2::keyword-value-listp new-args)))
  (if (atom args)
      nil
    (cons-with-hint
     (car args)
     (cons-with-hint
      (if (member-eq (car args) quoted-keys)
          (list 'quote (cadr args))
        (cadr args))
      (keyword-value-list-add-quotes quoted-keys (cddr args))
      (cdr args))
     args)))

(defmacro make-defsvtv-args! (&rest args)
  (if (acl2::keyword-value-listp args)
      (cons 'make-defsvtv-args (keyword-value-list-add-quotes '(:parents) args))
    (er hard? 'make-defsvtv-args! "Arguments must be a keyword/value-list~%")))






(define svtv-data-to-svtv ((x defsvtv-args-p)
                           svtv-data)
  :returns (svtv svtv-p)
  (b* ((namemap (svtv-data->namemap svtv-data))
       ((defsvtv-args x))
       (outs+ (append x.internals x.outputs))
       (nphases (svtv-lines-max-length outs+))
       (exp-ins (svtv-lines-expand x.inputs nphases namemap))
       (exp-overrides (svtv-lines-expand x.overrides nphases namemap))
       (expanded-ins (user-svtv-lines-to-svtv-lines exp-ins namemap))
       (expanded-overrides (user-svtv-lines-to-svtv-lines exp-overrides namemap))
       (expanded-outs (user-svtv-lines-to-svtv-lines outs+ namemap)))
    
    (make-svtv :name x.name
               :outexprs (svtv-data->pipeline svtv-data)
               :inmasks
               (append (fast-alist-free (fast-alist-clean (svtv-collect-masks
                                                           expanded-ins)))
                       (fast-alist-free (fast-alist-clean (svtv-collect-masks
                                                           expanded-overrides))))
               :outmasks 
               (fast-alist-free (fast-alist-clean (svtv-collect-masks
                                                   expanded-outs)))
               :inmap
               (svtv-collect-inmap t expanded-overrides
                                   (svtv-collect-inmap nil expanded-ins nil))
               :orig-ins x.inputs
               :orig-overrides x.overrides
               :orig-outs x.outputs
               :orig-internals x.internals
               :expanded-ins expanded-ins
               :expanded-overrides expanded-overrides
               :nphases nphases
               :labels x.labels
               :form x.form)))

(local (defthm string-listp-of-remove-duplicates
         (implies (string-listp x)
                  (string-listp (remove-duplicates-equal x)))))

(local (defthm true-list-listp-of-svtv*-outputs-to-svtv-lines
         (true-list-listp (svtv*-outputs-to-svtv-lines names phases))
         :hints(("Goal" :in-theory (enable svtv*-outputs-to-svtv-lines)))))

(local (defthm true-list-listp-of-svtv*-inputs-to-svtv-lines
         (true-list-listp (svtv*-inputs-to-svtv-lines names phases overridep))
         :hints(("Goal" :in-theory (enable svtv*-inputs-to-svtv-lines)))))

(define defsvtv-args-expand-stages ((x defsvtv-args-p))
  :returns (args defsvtv-args-p)
  ;; If it has phases, expand them to inputs/outputs/overrides/labels. If not, return unchanged.
  (b* ((stages (defsvtv-args->stages x))
       ((unless stages) (defsvtv-args-fix x))
       (parsed-stages (svtv*-parse-phases stages))
       (innames (acl2::hons-remove-dups (svtv*-phaselist-collect-inputnames parsed-stages)))
       (overridenames (acl2::hons-remove-dups (svtv*-phaselist-collect-overridenames parsed-stages)))
       (outputnames (acl2::hons-remove-dups (svtv*-phaselist-collect-outputnames parsed-stages)))
       (inputs (svtv*-inputs-to-svtv-lines innames parsed-stages nil))
       (overrides (svtv*-inputs-to-svtv-lines overridenames parsed-stages t))
       (outputs (svtv*-outputs-to-svtv-lines outputnames parsed-stages))
       (labels (svtv*-phaselist-collect-labels parsed-stages)))
    (change-defsvtv-args
     x
     :inputs inputs
     :overrides overrides
     :outputs outputs
     :labels labels))
  ///
  (defret design-of-<fn>
    (equal (defsvtv-args->design args) (defsvtv-args->design x)))
  (defret cycle-phases-of-<fn>
    (equal (defsvtv-args->cycle-phases args) (defsvtv-args->cycle-phases x)))
  (defret cycle-phases-p-of-<fn>
    (equal (defsvtv-args->cycle-phases-p args) (defsvtv-args->cycle-phases-p x))))

;; Does everything EXCEPT compute the pipeline.
(define defsvtv-stobj-pipeline-setup ((x defsvtv-args-p)
                                      ;; (keep-final-state)
                                      ;; (keep-all-states)
                                      svtv-data
                                      &key ((skip-cycle booleanp) 'nil))
  :guard (modalist-addr-p (design->modalist (defsvtv-args->design x)))
  :guard-hints (("goal" :do-not-induct t))
  :returns (mv err
               (pipeline-setup (implies (not err) (pipeline-setup-p pipeline-setup)))
               (new-svtv-data))
  (b* (((defsvtv-args x)) 
       (cycle-phases (if x.cycle-phases-p
                         x.cycle-phases
                       (list (make-svtv-cyclephase :constants nil
                                                   :inputs-free t
                                                   :outputs-captured t))))
       (outs+ (append x.internals x.outputs))

       ((mv err svtv-data)
        (svtv-data-defcycle-core x.design cycle-phases svtv-data
                                 :phase-config x.phase-config
                                 :phase-scc-limit x.phase-scc-limit
                                 :clocks-avoid-overrides x.clocks
                                 :rewrite-assigns x.pre-simplify
                                 :rewrite-phases x.pre-simplify
                                 :rewrite-cycle x.pre-simplify
                                 :cycle-simp x.cycle-simp
                                 :monotonify x.monotonify
                                 :skip-cycle skip-cycle))
       
       ((when err)
        (mv err nil svtv-data))

       (user-names (defsvtv-compute-user-namemap x.inputs x.overrides outs+))
       ((mv err svtv-data) (svtv-data-maybe-compute-namemap user-names svtv-data))
       ((when err)
        (mv err nil svtv-data))

       (namemap (svtv-data->namemap svtv-data))
       (statevars (svex-alist-keys (fsm->nextstate (svtv-data->phase-fsm svtv-data))))
       (pipeline-setup (defsvtv-compute-pipeline-setup
                         outs+ x.inputs x.overrides x.initial-state-vars statevars namemap)))
    (mv nil pipeline-setup svtv-data))
  ///
  (defret initst-keys-of-<fn>
    (implies (not err)
             (equal (svex-alist-keys (pipeline-setup->initst pipeline-setup))
                    (svex-alist-keys (fsm->nextstate
                                      (svtv-data->phase-fsm new-svtv-data))))))

  (defret validp-of-<fn>
    (implies (not err)
             (and (b* (((defsvtv-args x)))
                    (and (equal (svtv-data$c->design new-svtv-data) x.design)
                         ;; (equal (svtv-data$c->cycle-phases new-svtv-data)
                         ;;        (if x.cycle-phases-p
                         ;;            x.cycle-phases
                         ;;          (list (make-svtv-cyclephase :constants nil
                         ;;                                      :inputs-free t
                         ;;                                      :outputs-captured t))))
                         ))
                  (equal (svtv-data$c->flatten-validp new-svtv-data) t)
                  (equal (svtv-data$c->flatnorm-validp new-svtv-data) t)
                  (equal (svtv-data$c->phase-fsm-validp new-svtv-data) t)
                  (implies (not skip-cycle)
                           (equal (svtv-data$c->cycle-fsm-validp new-svtv-data) t))))))

(local (defthm intersection-equal-under-iff
         (iff (intersection-equal x y)
              (intersectp-equal x y))))


(define defsvtv-stobj-main ((x defsvtv-args-p)
                            ;; (keep-final-state)
                            ;; (keep-all-states)
                            svtv-data)
  :guard (modalist-addr-p (design->modalist (defsvtv-args->design x)))
  :guard-hints (("goal" :do-not-induct t))
  :guard-debug t
  :returns (mv err
               (svtv (implies (not err) (svtv-p svtv)))
               (new-svtv-data))
  (b* ((x (defsvtv-args-expand-stages x))
       ((mv err pipeline-setup svtv-data)
        (defsvtv-stobj-pipeline-setup x svtv-data))
       ((when err)
        (mv err nil svtv-data))
       ((defsvtv-args x))
       (st-vars  (svex-alist-keys (fsm->nextstate (svtv-data->phase-fsm svtv-data))))
       (bad-clocks (intersection-equal x.clocks st-vars))
       ((when bad-clocks)
        (mv (msg "Clocks cannot include previous-state variables -- ~x0~%" bad-clocks)
            nil svtv-data))
       (dups (acl2::hons-dups-p st-vars))
       ((when dups)
        (mv (msg "state variables have duplicates -- ~x0~%" (car dups))
            nil svtv-data))
       ((mv updatedp svtv-data)
        (svtv-data-maybe-compute-pipeline
         pipeline-setup svtv-data
         :simp x.pipe-simp
         :precomp-inputs x.clocks))
       (svtv-data (svtv-data-maybe-rewrite-pipeline (and updatedp x.simplify) svtv-data))
       (svtv (svtv-data-to-svtv x svtv-data)))
    (mv nil svtv svtv-data)))










(define defsvtv$-fn ((x defsvtv-args-p)
                     svtv-data
                     ;; irrelevant, just included for make-event signature requirement
                     state)
  :guard (modalist-addr-p (design->modalist (defsvtv-args->design x)))
  :irrelevant-formals-ok t
  :hooks nil
  ;; much of this copied from defstv
  (b* (((mv err svtv svtv-data)
        (defsvtv-stobj-main x svtv-data))
       ((when err)
        (raise "Failed to generate svtv: ~@0" err)
        (mv err nil state svtv-data))
       ((defsvtv-args x))
       (events (defsvtv-events svtv x.design-const x.define-macros x.define-mod x.parents x.short x.long)))
    (mv nil events state svtv-data)))



(define remove-keywords ((keys symbol-listp)
                         (args keyword-value-listp))
  :returns (new-args (implies (keyword-value-listp args)
                              (keyword-value-listp new-args)))
  (cond ((endp args) nil)
        ((member-eq (car args) keys)
         (remove-keywords keys (cddr args)))
        (t (cons-with-hint (car args)
                           (cons-with-hint (cadr args)
                                           (remove-keywords keys (cddr args))
                                           (cdr args))
                           args))))

(define process-defsvtv$-user-args (name args)
  ;; Returns the :stobj argument (defaults to SVTV-DATA) and the list of
  ;; arguments to be passed to make-defsvtv-args.
  :returns (mv stobj norm-args)
  :mode :program
  (b* (((unless (keyword-value-listp args))
        (raise "Arguments must be a keyword/value list.~%")
        (mv nil nil))
       ((unless (xor (assoc-keyword :design args)
                     (assoc-keyword :mod args)))
        (raise "Must provide either :design or :mod (interchangeable), but not both.~%")
        (mv nil nil))
       (design (cadr (or (assoc-keyword :design args)
                         (assoc-keyword :mod args))))
       (stobj-look (assoc-keyword :stobj args))
       (stobj (if stobj-look (cadr stobj-look) 'svtv-data))
       (cycle-phases-p (consp (assoc-keyword :cycle-phases args)))
       (stages-look (or (assoc-keyword :phases args)
                        (assoc-keyword :stages args)))
       (in/out/overrides-look (or (assoc-keyword :inputs args)
                                  (assoc-keyword :outputs args)
                                  (assoc-keyword :overrides args)))
       ((when (and stages-look in/out/overrides-look))
        (raise "Must provide either :stages or (deprecated) :phases or :inputs/:outputs/:overrides, not both.~%")
        (mv nil nil))
       (stages-args (and stages-look
                         (b* ((stages-arg (cadr stages-look))
                              (stages-quote (if (and (consp stages-arg)
                                                     (consp (car stages-arg))
                                                     (keywordp (caar stages-arg)))
                                                ;; can't be a term, and looks like a literal phases list
                                                (kwote stages-arg)
                                              stages-arg)))
                           `(:stages ,stages-quote))))
       (norm-args (list* :name (list 'quote name)
                         :design design
                         :design-const (list 'quote design)
                         :cycle-phases-p cycle-phases-p
                         (append stages-args
                                 (remove-keywords '(:mod :design :stobj :phases :stages) args)))))
    (mv stobj norm-args)))



;; Documented in new-svtv-doc.lisp
(defmacro defsvtv$ (&whole form name &rest args)
  (b* (((mv stobj norm-args)
        (process-defsvtv$-user-args name (list* :form (kwote form) args))))
    `(make-event (defsvtv$-fn (make-defsvtv-args! . ,norm-args)
                   ,stobj state))))

(defmacro defsvtv$-phasewise (&rest args)
  (cons 'defsvtv$ args))



;; Doc in new-svtv-doc.lisp


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
                                                      (svcall zerox 5 "in")))))))))))
(local
 (defsvtv$ my-svtv
   :design *my-design*
   :stages
   ((:label the-phase
     :inputs (("in" in))
     :outputs (("out" out)))
    (:label the-next-phase
     :inputs (("in" in2))
     :outputs (("out" out2))))))

(local
 (defsvtv$ my-svtv2
   :design *my-design*
   :stages
   `((:label the-phase
      ,@'(:inputs (("in" in)))
     :outputs (("out" out)))
    (:label the-next-phase
     :inputs (("in" in2))
     :outputs (("out" out2))))))
