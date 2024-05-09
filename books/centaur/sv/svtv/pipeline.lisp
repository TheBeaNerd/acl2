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

(include-book "assign")
(include-book "fsm")
(include-book "probe")
(include-book "compose-phases")
(include-book "../svex/rewrite")
(include-book "../svex/alist-equiv")
(local (include-book "../svex/alist-thms"))
(local (std::add-default-post-define-hook :fix))





;; First goal: make a set of svex alists that symbolically gives the outputs
;; from an svtv-fsm-run.  Then, extract those outputs into a single
;; svex alist in the style of svtv-run.  Additionally, parse a defsvtv-like
;; form into symbolic inputs for this symbolic svtv-fsm-run.

;; Ingredients: svtv-fsm-run can be phrased as

;; (svtv-fsm-run-extract-outs
;;  outvars
;;  (svtv-fsm-run
;;   (svtv-fsm-run-input-envs inputs override-tests x)
;;   prev-st
;;   x
;;   (svtv-fsm-run-output-signals (take (len inputs) outvars) x))
;;  x)

;; (svtv-fsm-run-output-signals (take (len inputs) outvars) x) has no symbolic components
;; so it can remain the same.

;; (svtv-fsm-run-input-envs inputs override-tests x) becomes
;; svtv-fsm-run-input-substs.

;; svtv-fsm-run becomes a series of svex-alist-compose-svtv-phases

;; svtv-fsm-run-extract-outs becomes a series of 
;; (svex-alist-subst
;;   (svtv-name-lhs-map-to-svex-alist (fal-extract outvars) x.namemap)
;;   full-outs)
;; as in svtv-fsm-step-extract-outs.

(local (defthm len-of-svex-alist-keys
         (implies (svex-alist-p x)
                  (equal (len (svex-alist-keys x))
                         (len x)))
         :hints(("Goal" :in-theory (enable svex-alist-p svex-alist-keys)))))

;; (local (defthm svex-alist-keys-of-svex-alist-extract
;;          (equal (svex-alist-keys (svex-alist-extract vars x))
;;                 (svarlist-fix vars))
;;          :hints(("Goal" :in-theory (enable svex-alist-keys svex-alist-extract)))))

(local (defthm len-of-svexlist-compose-svtv-phases
         (equal (len (svexlist-compose-svtv-phases x phase data))
                (len x))
         :hints(("Goal" :in-theory (enable svexlist-compose-svtv-phases)))))

;; (local (defthm svex-env-extract-of-svex-alist-eval
;;          (equal (svex-env-extract vars (Svex-alist-eval x y))
;;                 (svex-alist-eval (svex-alist-extract vars x) y))
;;          :hints(("Goal" :in-theory (enable svex-env-extract svex-alist-extract)))))

(define fsm-run-compile-phase ((phase natp)
                               (outvars svarlist-p)
                               (out-values svex-alist-p)
                               (data svtv-composedata-p))
  :returns (out-alist svex-alist-p)
  (b* ((alist (svex-alist-extract outvars out-values)))
    (svex-alist-compose-svtv-phases alist phase data))
  ///
  (local (defthm pairlis-svexlist-eval-extract
           (equal (pairlis$ (svarlist-fix vars) (svexlist-eval (svex-alist-vals (svex-alist-extract vars vals)) env))
                  (svex-env-extract vars (svex-alist-eval vals env)))
           :hints(("Goal" :in-theory (enable svex-env-extract svex-alist-vals svex-alist-extract)))))
  
  (defret eval-of-<fn>
    :pre-bind (((svtv-precompose-data predata))
               (data (svtv-precompose-phases nphases predata)))
    (implies (and (< (nfix phase) (nfix nphases))
                  (not (intersectp-equal (svex-alist-keys predata.nextstate) predata.pre-compose-inputs))
                  ;; (equal (svex-alist-keys predata.nextstate) (svex-alist-keys predata.initst))
                  )
             (equal (svex-alist-eval out-alist env)
                    (b* (((svtv-composedata data)))
                      (svex-env-extract outvars
                                        (svex-alist-eval out-values

                                                         (APPEND
                                                          (fsm-FINAL-STATE
                                                           (TAKE PHASE
                                                                 (SVEX-ALISTLIST-EVAL (SVTV-PRECOMPOSE-DATA->INPUT-SUBSTS PREDATA)
                                                                                      ENV))
                                                           (SVEX-ALIST-EVAL (SVTV-PRECOMPOSE-DATA->INITST PREDATA)
                                                                            ENV)
                                                           (SVTV-PRECOMPOSE-DATA->NEXTSTATE PREDATA))
                                                          (SVEX-ALIST-EVAL (NTH PHASE
                                                                                (SVTV-PRECOMPOSE-DATA->INPUT-SUBSTS PREDATA))
                                                                           ENV)))
                                        ;; (APPEND
                                        ;;  (SVEX-ALIST-EVAL (SVEX-UNROLL-MULTISTATE-PHASE-STATE
                                        ;;                    PHASE
                                        ;;                    (SVTV-COMPOSEDATA->NEXTSTATES
                                        ;;                     (SVTV-PRECOMPOSE-PHASES NPHASES PREDATA))
                                        ;;                    (SVTV-COMPOSEDATA->INPUT-SUBSTS
                                        ;;                     (SVTV-PRECOMPOSE-PHASES NPHASES PREDATA)))
                                        ;;                   ENV)
                                        ;;  (SVEX-ALIST-EVAL (NTH PHASE
                                        ;;                        (SVTV-COMPOSEDATA->INPUT-SUBSTS
                                        ;;                         (SVTV-PRECOMPOSE-PHASES NPHASES PREDATA)))
                                        ;;                   ENV))
                                        ;; (svexlist-eval-unroll-multienv
                                        ;;  (svex-alist-vals (svex-alist-extract outvars out-values))
                                        ;;  phase
                                        ;;  predata.nextstates
                                        ;;  (svex-alistlist-eval predata.input-substs env)
                                        ;;  (svex-alist-eval predata.initst env))
                                        ))))
    :hints(("Goal" :in-theory (enable svex-alist-compose-svtv-phases-correct)))))



;; (local
;;  (std::defret-mutual take-in-envs-of-svex-eval-unroll-multienv
;;    (defret take-in-envs-of-<fn>
;;      (implies (< (nfix cycle) (nfix n))
;;               (equal (let ((in-envs (take n in-envs))) <call>)
;;                      new-x))
;;      :hints ('(:expand ((:free (in-envs cycle) <call>))))
;;      :fn svex-eval-unroll-multienv)
;;    (defret take-in-envs-of-<fn>
;;      (implies (< (nfix cycle) (nfix n))
;;               (equal (let ((in-envs (take n in-envs))) <call>)
;;                      new-x))
;;      :hints ('(:expand ((:free (in-envs) <call>))))
;;      :fn svexlist-eval-unroll-multienv)
;;    :mutual-recursion svex-eval-unroll-multienv))
            

                     
(local
 (encapsulate nil
   (local (Defthm member-alist-keys
            (iff (member-equal k (alist-keys x))
                 (hons-assoc-equal k x))
            :hints(("Goal" :in-theory (enable alist-keys)))))
   (defthm svex-env-extract-keys-under-svex-envs-equivalent
     (implies (equal keys (alist-keys (svex-env-fix x)))
              (svex-envs-equivalent (svex-env-extract keys x) x))
     :hints(("Goal" :in-theory (enable svex-envs-equivalent))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-lookup svex-env-boundp)))))))


(define fsm-run-compile-phases ((phase natp)
                                     (outvars svarlist-list-p)
                                     (out-values svex-alist-p)
                                     (data svtv-composedata-p))
  :returns (out-alists svex-alistlist-p)
  (if (atom outvars)
      nil
    (cons (fsm-run-compile-phase phase (car outvars) out-values data)
          (fsm-run-compile-phases (1+ (lnfix phase)) (cdr outvars) out-values data)))
  ///

  (local (include-book "std/lists/nth" :dir :system))

  (local (defthm nthcdr-gte-len
           (implies (and (true-listp x)
                         (<= (len x) (nfix n)))
                    (equal (nthcdr n x) nil))
           :hints(("Goal" :in-theory (enable nthcdr)))))

  (local (defthm nthcdr-of-svex-envlist-extract
           (equal (nthcdr n (svex-envlist-extract vars envs))
                  (svex-envlist-extract (nthcdr n vars) (nthcdr n envs)))
           :hints(("Goal" :in-theory (enable svex-envlist-extract nthcdr)))))

  (local (defthm car-nthcdr
           (equal (car (nthcdr n x))
                  (nth n x))
           :hints(("Goal" :in-theory (enable nthcdr nth)))))

  (local (defthm len-of-take
           (equal (len (take n x))
                  (nfix n))
           :hints(("Goal" :in-theory (enable take)))))

  (defret svex-alistlist-eval-of-<fn>
    :pre-bind (((svtv-precompose-data predata))
               (data (svtv-precompose-phases nphases predata)))
    (implies (and (<= (+ (nfix phase) (len outvars)) (nfix nphases))
                  (not (intersectp-equal (svex-alist-keys predata.nextstate) predata.pre-compose-inputs))
                  ;; (equal (svex-alist-keys predata.nextstate) (svex-alist-keys predata.initst))
                  ;; (no-duplicatesp-equal (svex-alist-keys predata.nextstate))
                  )
             (equal (svex-alistlist-eval out-alists env)
                    (b* (((svtv-composedata data)))
                      (nthcdr phase
                              (fsm-run (svex-alistlist-eval predata.input-substs env)
                                            (svex-alist-eval predata.initst env)
                                            (make-fsm :nextstate predata.nextstate
                                                           :values out-values)
                                            (append (repeat phase nil) outvars))))))
    :hints(("Goal" :in-theory (e/d (fsm-run
                                    ;; svex-envlist-extract
                                    ;; fsm-eval-is-svex-eval-unroll-multienv
                                    nth-of-fsm-eval
                                    fsm-step-outs
                                    fsm-step-env
                                    )
                                   (car-of-fsm-eval
                                    cdr-of-fsm-eval
                                    fsm-eval-of-cons
                                    acl2::take-of-too-many
                                    nthcdr-of-fsm-eval-is-fsm-eval
                                    take))
            :expand ((svex-alist-eval nil env)
                     (:free (n a b) (nth n (cons a b)))
                     ;; (:free (x ins initst fsm) (fsm-eval (take (+ 1 x) ins) initst fsm))
                     (:free (x) (svex-envlist-extract outvars x)))
            :induct  <call>))))



(local (in-theory (disable hons-dups-p)))  


(local (include-book "std/lists/sets" :dir :system))

(local (defthm intersectp-set-diff
         (not (intersectp-equal x (set-difference-equal y x)))
         :hints(("Goal" ; :induct (len x)
                 :in-theory (enable acl2::intersectp-witness-rw)))))

(local (defthm set-difference-when-not-intersectp
         (implies (not (intersectp x y))
                  (equal (set-difference-equal x y)
                         (true-list-fix x)))
         :hints(("Goal" :in-theory (enable intersectp set-difference-equal)))))

(define fsm-run-compile ((ins svex-alistlist-p)
                              (prev-st svex-alist-p)
                              (x fsm-p)
                              (signals svarlist-list-p)
                              (precomp-inputs svarlist-p)
                              (simp svex-simpconfig-p))
  :guard (b* ((st-vars (svex-alist-keys (fsm->nextstate x))))
           (and (equal (svex-alist-keys prev-st) st-vars)
                (not (acl2::hons-dups-p st-vars))
                (not (acl2::hons-intersect-p precomp-inputs st-vars))))
  :returns (out-alists svex-alistlist-p)
  (b* (((fsm x))
       ((acl2::with-fast x.nextstate x.values prev-st))
       (composedata
        (svtv-precompose-phases (len signals)
                                (make-svtv-precompose-data
                                 :nextstate x.nextstate
                                 :input-substs (make-fast-alists ins)
                                 :initst prev-st
                                 :simp simp
                                 :pre-compose-inputs
                                 (mbe :logic (acl2::hons-set-diff (svarlist-fix precomp-inputs)
                                                                  (svex-alist-keys x.nextstate))
                                      :exec precomp-inputs))))
       (ans (fsm-run-compile-phases 0 signals x.values composedata)))
    (fast-alistlist-clean ins)
    (clear-memoize-table 'svex-compose-svtv-phases-call)
    (clear-memoize-table 'svtv-precompose-inputs-compose)
    ans)
  ///
  
  (defret svex-alistlist-eval-of-<fn>
    (equal (svex-alistlist-eval out-alists env)
           (fsm-run (svex-alistlist-eval ins env)
                    (svex-alist-eval prev-st env)
                    x
                    signals))))

(define fsm-final-state-compile ((ins svex-alistlist-p)
                                 (prev-st svex-alist-p)
                                 (x fsm-p)
                                 (precomp-inputs svarlist-p)
                                 (simp svex-simpconfig-p))
  :guard (b* ((st-vars (svex-alist-keys (fsm->nextstate x))))
           (and (equal (svex-alist-keys prev-st) st-vars)
                (not (acl2::hons-dups-p st-vars))
                (not (acl2::hons-intersect-p precomp-inputs st-vars))))
  :prepwork ((local (defthm len-equal-0
                      (equal (Equal (len x) 0) (not (consp x)))))
             (local (defthm svex-alist-extract-cdr-when-car-not-member
                      (implies (or (not (consp (car x)))
                                   (not (svar-p (caar x)))
                                   (not (member-equal (caar x) (svarlist-fix keys))))
                               (equal (svex-alist-extract keys (cdr x))
                                      (svex-alist-extract keys x)))
                      :hints(("Goal" :in-theory (enable svex-alist-extract
                                                        svex-lookup)))))
                                        
             (local (defthm svex-alist-extract-when-alist-keys-equal
                      (implies (and (equal (svex-alist-keys x) keys)
                                    (no-duplicatesp keys))
                               (equal (svex-alist-extract keys x)
                                      (svex-alist-fix x)))
                      :hints(("Goal" :in-theory (enable svex-alist-extract svex-alist-fix
                                                        svex-alist-keys no-duplicatesp))
                             (and stable-under-simplificationp
                                  (not (access acl2::clause-id id :pool-lst))
                                  '(:induct t))
                             (and stable-under-simplificationp
                                  '(:in-theory (enable svex-lookup)))
                             ))))
  :returns (final-state svex-alist-p)
  (b* (((fsm x))
       ((unless (consp ins))
        (mbe :logic (svex-alist-extract (svex-alist-keys x.nextstate) prev-st)
             :exec prev-st))
       ((acl2::with-fast x.nextstate prev-st))
       (composedata
        (svtv-precompose-phases (len ins)
                                (make-svtv-precompose-data
                                 :nextstate x.nextstate
                                 :input-substs (make-fast-alists ins)
                                 :initst prev-st
                                 :simp simp
                                 :pre-compose-inputs
                                 (mbe :logic (acl2::hons-set-diff (svarlist-fix precomp-inputs)
                                                                  (svex-alist-keys x.nextstate))
                                      :exec precomp-inputs))))
       (ans  (svex-alist-compose-svtv-phases x.nextstate (1- (len ins)) composedata)))
    (fast-alistlist-clean ins)
    (clear-memoize-table 'svex-compose-svtv-phases-call)
    (clear-memoize-table 'svtv-precompose-inputs-compose)
    ans)
  ///

  (local (defthm fsm-final-state-of-atom
           (implies (atom ins)
                    (Equal (fsm-final-state ins prev-st x)
                           (svex-env-extract (svex-alist-keys x) prev-st)))
           :hints(("Goal" :in-theory (enable fsm-final-state)))))
  
  (local (defthm fsm-final-state-expand-from-end
           (implies (consp ins)
                    (Equal (fsm-final-state ins prev-st x)
                           (svex-env-extract (svex-alist-keys x)
                                             (fsm-step (nth (1- (len ins)) ins)
                                                       (fsm-final-state (take (1- (len ins)) ins)
                                                                        prev-st x)
                                                       x))))
           :hints(("Goal" :in-theory (enable (:i fsm-final-state))
                   :induct (fsm-final-state ins prev-st x)
                   :expand ((fsm-final-state ins prev-st x)
                            (fsm-final-state nil prev-st x)
                            (:free (a b) (fsm-final-state (cons a b) prev-st x)))))))

  (local (defthm consp-of-svex-alistlist-eval
           (equal (Consp (svex-alistlist-eval x env))
                  (consp x))
           :hints(("Goal" :in-theory (enable svex-alistlist-eval)))))
  
  (defret svex-alist-eval-of-<fn>
    (implies (no-duplicatesp-equal (svex-alist-keys (fsm->nextstate x)))
             (equal (svex-alist-eval final-state env)
                    (fsm-final-state (svex-alistlist-eval ins env)
                                     (svex-alist-eval prev-st env)
                                     (fsm->nextstate x))))
    :hints (("goal" :do-not-induct t
             :in-theory (enable fsm-step fsm-step-env)
             :expand ((len ins)))))

  (defret svex-alist-eval-of-<fn>-under-svex-envs-equivalent
    (svex-envs-equivalent
     (svex-alist-eval final-state env)
     (fsm-final-state (svex-alistlist-eval ins env)
                      (svex-alist-eval prev-st env)
                      (fsm->nextstate x)))
    :hints (("goal" :do-not-induct t
             :in-theory (enable fsm-step fsm-step-env)
             :expand ((len ins))))))


;; (define svtv-fsm-step-compile-extract-outs ((outvars svarlist-p)
;;                                                     (full-outs svex-alist-p)
;;                                                     (x svtv-fsm-p))
;;   :returns (outs svex-alist-p)
;;   (b* (((svtv-fsm x))
;;        (out-alist1 (acl2::fal-extract (svarlist-fix outvars) x.renamed-values)))
;;     (with-fast-alist full-outs
;;       (svtv-name-lhs-map-subst out-alist1 full-outs)))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval outs env)
;;            (svtv-fsm-step-extract-outs
;;             outvars (svex-alist-eval full-outs env) x))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-step-extract-outs)))))
       

;; (define svtv-fsm-run-compile-extract-outs ((outvars svarlist-list-p)
;;                                                    (full-outs svex-alistlist-p)
;;                                                    (x svtv-fsm-p))
;;   :returns (outs svex-alistlist-p)
;;   (if (atom outvars)
;;       nil
;;     (cons (svtv-fsm-step-compile-extract-outs (car outvars) (car full-outs) x)
;;           (svtv-fsm-run-compile-extract-outs (cdr outvars) (cdr full-outs) x)))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alistlist-eval outs env)
;;            (svtv-fsm-run-extract-outs
;;             outvars (svex-alistlist-eval full-outs env) x))
;;     :hints(("Goal" :in-theory (enable svtv-fsm-run-extract-outs
;;                                       svex-alistlist-eval)
;;             :expand ((svex-alist-eval nil env))))))






(define svtv-fsm-run-compile ((ins svex-alistlist-p)
                              (override-vals svex-alistlist-p)
                              (override-tests svex-alistlist-p)
                              (prev-st svex-alist-p)
                              (x svtv-fsm-p)
                              (outvars svarlist-list-p)
                              (precomp-inputs svarlist-p)
                              (simp svex-simpconfig-p))
  :guard (b* ((st-vars (svex-alist-keys (svtv-fsm->nextstate x))))
           (and (equal (svex-alist-keys prev-st) st-vars)
                (not (acl2::hons-dups-p st-vars))
                (not (acl2::hons-intersect-p precomp-inputs st-vars))))
  :guard-hints (("goal" :in-theory (enable svtv-fsm->renamed-fsm)))
  :returns (out-alists svex-alistlist-p)
  (b* ((input-substs (svtv-fsm-to-fsm-inputsubsts
                      (take (len outvars) ins)
                      override-vals override-tests
                      (svtv-fsm->namemap x)))
       ((svtv-fsm x)))
    (fsm-run-compile input-substs prev-st x.renamed-fsm outvars precomp-inputs simp))
  ///

  (local (defthm take-of-svex-alistlist-eval
           (equal (take n (svex-alistlist-eval x env))
                  (svex-alistlist-eval (take n x) env))
           :hints(("Goal" :in-theory (e/d (svex-alistlist-eval)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))
                   :expand ((svex-alist-eval nil env))))))

  (defret eval-of-<fn>
    (equal (svex-alistlist-eval out-alists env)
           (svtv-fsm-run
            (svex-alistlist-eval ins env)
            (svex-alist-eval prev-st env)
            x
            outvars
            :override-vals (svex-alistlist-eval override-vals env)
            :override-tests (svex-alistlist-eval override-tests env)))
    :hints(("Goal" :in-theory (enable svtv-fsm-run-is-fsm-run))))

  (defret eval-lookup-of-<fn>
    (equal (svex-eval (svex-lookup var (nth n out-alists)) env)
           (svex-env-lookup var (nth n (svtv-fsm-run
                                        (svex-alistlist-eval ins env)
                                        (svex-alist-eval prev-st env)
                                        x
                                        outvars
                                        :override-vals (svex-alistlist-eval override-vals env)
                                        :override-tests (svex-alistlist-eval override-tests env)))))
    :hints(("Goal" :use eval-of-<fn>
            :in-theory (disable eval-of-<fn> <fn>))))

  (local
   (defret lookup-under-iff-of-<fn>
     (iff (svex-lookup var (nth n out-alists))
          (svex-env-boundp var (nth n (svtv-fsm-run
                                       (svex-alistlist-eval ins env)
                                       (svex-alist-eval prev-st env)
                                       x
                                       outvars
                                       :override-vals (svex-alistlist-eval override-vals env)
                                       :override-tests (svex-alistlist-eval override-tests env)))))
     :hints(("Goal" :use eval-of-<fn>
             :in-theory (disable eval-of-<fn> <fn>)))))

  (local
   (defret len-of-<fn>
     (equal (len out-alists)
            (len (svtv-fsm-run
                  (svex-alistlist-eval ins env)
                  (svex-alist-eval prev-st env)
                  x
                  outvars
                  :override-vals (svex-alistlist-eval override-vals env)
                  :override-tests (svex-alistlist-eval override-tests env))))
     :hints(("Goal" :use eval-of-<fn>
             :in-theory (disable eval-of-<fn> <fn> len-of-svtv-fsm-run)))))


  (defret normalize-<fn>-simp-under-svex-alistlist-eval-equiv
    (implies (syntaxp (not (equal simp ''nil)))
             (svex-alistlist-eval-equiv out-alists
                                        (let ((simp nil)) <call>)))
    :hints (("goal" :in-theory (disable <fn>))
            (witness) (witness) (witness)))

  (local (defthm take-of-svex-alistlist-fix
           (equal (take n (svex-alistlist-fix x))
                  (svex-alistlist-fix (take n x)))
           :hints(("Goal" :in-theory (e/d (svex-alistlist-fix)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))))))

  (defcong svtv-fsm-eval/namemap-equiv svex-alistlist-eval-equiv
    (svtv-fsm-run-compile ins override-vals override-tests prev-st x outvars precomp-ins rewrite) 5
    :hints (("goal" :in-theory (disable svtv-fsm-run-compile))
            (witness) (witness) (witness))))
       



                               

(local (defthm rassoc-equal-of-lookup
         (implies (And (hons-assoc-equal key x)
                       (alistp x))
                  (rassoc-equal (cdr (hons-assoc-equal key x)) x))
         :hints(("Goal" :in-theory (enable hons-assoc-equal rassoc-equal)))))

(local (defthm alistp-when-svtv-probealist-p-rw
         (implies (svtv-probealist-p probes)
                  (alistp probes))
         :hints(("Goal" :in-theory (enable svtv-probealist-p)))))

(local (defthm svarlist-p-of-nth
         (implies (svarlist-list-p x)
                  (svarlist-p (nth n x)))
         :hints(("Goal" :in-theory (enable nth svarlist-p)))))

(encapsulate nil
  (local
   (defun take-of-in-envs-ind (n ins override-vals override-tests)
     (if (zp n)
         (list ins override-vals override-tests)
       (take-of-in-envs-ind (1- n) (cdr ins) (cdr override-vals) (cdr override-tests)))))

  (defthm take-of-svtv-fsm-to-fsm-inputs
           (equal (take n (svtv-fsm-to-fsm-inputs (take n ins) override-vals override-tests x))
                  (svtv-fsm-to-fsm-inputs (take n ins) override-vals override-tests x))
           :hints(("Goal" :in-theory (e/d (svtv-fsm-to-fsm-inputs)
                                          (acl2::take-of-too-many
                                           acl2::take-when-atom))
                   :induct (take-of-in-envs-ind n ins override-vals override-tests)))))

(defthm lookup-in-pipeline
  (equal (svex-eval (svex-lookup name
                                 (svtv-probealist-extract-alist
                                  probes
                                  (svtv-fsm-run-compile
                                   inputs override-vals override-tests initst fsm
                                   (svtv-probealist-outvars probes) precomp-inputs simp)))
                    env)
         (b* ((inputs-eval (svex-alistlist-eval inputs env))
              (initst-eval (svex-alist-eval initst env))
              (probe-look (hons-assoc-equal (svar-fix name) (svtv-probealist-fix probes)))
              ((svtv-probe probe) (cdr probe-look))
              (ins (svtv-fsm-to-fsm-inputs
                    (take (len (svtv-probealist-outvars probes)) inputs-eval)
                    (svex-alistlist-eval override-vals env)
                    (svex-alistlist-eval override-tests env)
                    (svtv-fsm->namemap fsm))))
           (if probe-look
               (svex-env-lookup
                probe.signal
                (nth probe.time (fsm-run
                                 ins initst-eval
                                 (svtv-fsm->renamed-fsm fsm)
                                 (svtv-probealist-outvars probes))))
             (4vec-x))))
  :hints(("Goal" :in-theory (e/d (SVTV-FSM-RUN-IS-EXTRACT-OF-EVAL
                                    ;; lookup-of-svtv-fsm-step-extract-outs
                                    svtv-fsm-eval-is-svtv-fsm-eval-of-input-envs)
                                 (nth)))))
