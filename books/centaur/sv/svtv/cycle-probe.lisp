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

(include-book "probe")
(include-book "cycle-compile")
(include-book "assign")
(local (std::add-default-post-define-hook :fix))

(define svtv-name-lhs-map-eval-list ((namemap svtv-name-lhs-map-p)
                                     (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (atom envs)
      nil
    (cons (svtv-name-lhs-map-eval namemap (car envs))
          (svtv-name-lhs-map-eval-list namemap (cdr envs))))
  ///
  (defret nth-of-<fn>
    (equal (nth n new-envs)
           (and (< (lnfix n) (len envs))
                (svtv-name-lhs-map-eval namemap (nth n envs))))
    :hints(("Goal" :in-theory (enable nth)
            :induct (nth n envs))))

  (defret len-of-<fn>
    (Equal (len new-envs) (len envs))))

(define svtv-probealist-cycle-adjust-aux ((x svtv-probealist-p)
                                          (cycle-len posp)
                                          (cycle-outphase natp))
  :returns (new-x svtv-probealist-p)
  (b* (((when (atom x))
        nil)
       ((unless (mbt (consp (car x))))
        (svtv-probealist-cycle-adjust-aux (cdr x) cycle-len cycle-outphase))
       ((cons var (svtv-probe pr)) (car x)))
    (cons (cons (svar-fix var) (change-svtv-probe pr :time (+ (* pr.time (lposfix cycle-len))
                                                              (lnfix cycle-outphase))))
          (svtv-probealist-cycle-adjust-aux (cdr x) cycle-len cycle-outphase)))
  ///

  (local (defthm svtv-cycle-output-phase-limit
           (implies (svtv-cycle-output-phase phases)
                    (< (svtv-cycle-output-phase phases) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase)))
           :rule-classes :linear))

  (local (defthm cycle-output-phase-bound
           (implies (and (natp probe-time)
                         (svtv-cycle-output-phase phases))
                    (iff (> (len (svtv-cycle-run-fsm-inputs ins phases))
                            (+ (SVTV-CYCLE-OUTPUT-PHASE PHASES)
                               (* (LEN PHASES)
                                  probe-time)))
                         (< probe-time (LEN INS))))
           :hints(("Goal" :in-theory (enable len-of-svtv-cycle-run-fsm-inputs))
                  (and stable-under-simplificationp
                       '(:nonlinearp t)))))

  (defret <fn>-correct
    (implies (and (equal cycle-len (len phases))
                  (equal cycle-outphase (svtv-cycle-output-phase phases))
                  cycle-outphase)
             (equal (svtv-probealist-extract x (fsm-eval ins initst (fsm-to-cycle phases fsm simp)))
                    (svtv-probealist-extract
                     new-x (fsm-eval (svtv-cycle-run-fsm-inputs ins phases) initst fsm))))
    :hints(("Goal"
            :expand (<call>
                     (:free (eval) (svtv-probealist-extract x eval))
                     (:free (eval) (svtv-probealist-extract nil eval))
                     (:free (eval a b) (svtv-probealist-extract (cons a b) eval)))
            :induct <call>)))

  (defret <fn>-correct-name-lhs-map-eval-list
    (implies (and (equal cycle-len (len phases))
                  (equal cycle-outphase (svtv-cycle-output-phase phases))
                  cycle-outphase)
             (equal (svtv-probealist-extract x (svtv-name-lhs-map-eval-list
                                                map
                                                (fsm-eval ins initst (fsm-to-cycle phases fsm simp))))
                    (svtv-probealist-extract
                     new-x
                     (svtv-name-lhs-map-eval-list
                      map
                      (fsm-eval (svtv-cycle-run-fsm-inputs ins phases) initst fsm)))))
    :hints(("Goal"
            :in-theory (disable len-of-svtv-cycle-run-fsm-inputs)
            :expand (<call>
                     (svtv-name-lhs-map-eval map nil)
                     (:free (eval) (svtv-probealist-extract x eval))
                     (:free (eval) (svtv-probealist-extract nil eval))
                     (:free (eval a b) (svtv-probealist-extract (cons a b) eval)))
            :induct <call>)))

  (local (in-theory (enable svtv-probealist-fix))))


(define svtv-probealist-cycle-adjust ((x svtv-probealist-p)
                                      (phases svtv-cyclephaselist-p))
  :returns (new-x svtv-probealist-p)
  (b* ((len (pos-fix (len phases)))
       (outphase (or (svtv-cycle-output-phase phases) 0)))
    (svtv-probealist-cycle-adjust-aux x len outphase))
  ///
  (local (defthm svtv-cycle-output-phase-limit
           (implies (svtv-cycle-output-phase phases)
                    (< (svtv-cycle-output-phase phases) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase)))
           :rule-classes :linear))
  
  (defret <fn>-correct
    (implies (svtv-cycle-output-phase phases)
             (equal (svtv-probealist-extract x (fsm-eval ins initst (fsm-to-cycle phases fsm simp)))
                    (svtv-probealist-extract
                     new-x (fsm-eval (svtv-cycle-run-fsm-inputs ins phases) initst fsm)))))

  (defret <fn>-correct-name-lhs-map-eval-list
    (implies (svtv-cycle-output-phase phases)
             (equal (svtv-probealist-extract x (svtv-name-lhs-map-eval-list
                                                map
                                                (fsm-eval ins initst (fsm-to-cycle phases fsm simp))))
                    (svtv-probealist-extract
                     new-x
                     (svtv-name-lhs-map-eval-list
                      map
                      (fsm-eval (svtv-cycle-run-fsm-inputs ins phases) initst fsm)))))))



(defthmd fsm->nextstate-of-svtv-fsm->renamed-fsm
  (equal (fsm->nextstate (svtv-fsm->renamed-fsm svtv-fsm))
         (fsm->nextstate (svtv-fsm->fsm svtv-fsm)))
  :hints(("Goal" :in-theory (enable svtv-fsm->renamed-fsm))))

(defthm fsm-step-outs-of-svtv-fsm->renamed-fsm
  (equal (fsm-step-outs in prev-st (svtv-fsm->renamed-fsm fsm))
         (svtv-name-lhs-map-eval
          (svtv-fsm->namemap fsm)
          (fsm-step-outs in prev-st (svtv-fsm->fsm fsm))
          ;; (append (fsm-step-outs in prev-st (svtv-fsm->fsm fsm))
          ;;         (fsm-step-env in prev-st (svtv-fsm->nextstate fsm)))
          ))
  :hints(("Goal" :in-theory (enable fsm-step-outs
                                    svtv-fsm->renamed-fsm
                                    fsm-step-env))))

(defthmd fsm-eval-of-svtv-fsm->renamed-fsm
    (equal (fsm-eval ins prev-st (svtv-fsm->renamed-fsm x))
           (svtv-name-lhs-map-eval-list
            (svtv-fsm->namemap x)
            (fsm-eval ins prev-st (svtv-fsm->fsm x))
            ;; (svex-envlists-append-corresp
            ;;  (fsm-eval ins prev-st (svtv-fsm->fsm x))
            ;;  (fsm-eval-envs ins prev-st (svtv-fsm->nextstate x)))
            ))
    :hints(("Goal" :in-theory (enable fsm-eval
                                      fsm-step
                                      fsm-step-outs
                                      fsm-step-env
                                      svtv-name-lhs-map-eval-list
                                      fsm->nextstate-of-svtv-fsm->renamed-fsm)
            :induct (fsm-eval ins prev-st (svtv-fsm->fsm x))
            :expand ((:free (x) (fsm-eval ins prev-st x))))))


(define svtv-probealist-sufficient-varlists ((x svtv-probealist-p)
                                             (vars svarlist-list-p))
  :prepwork ((local (defthm true-listp-when-svarlist-p-rw
                      (implies (svarlist-p x)
                               (true-listp x))))
             (local (defthm svarlist-p-nth-of-svarlist-list
                      (implies (svarlist-list-p x)
                               (svarlist-p (nth n x))))))
  (if (atom x)
      t
    (if (mbt (consp (car x)))
        (b* (((svtv-probe x1) (cdar x)))
          (and (member-equal x1.signal (svarlist-fix (nth x1.time vars)))
               (svtv-probealist-sufficient-varlists (cdr x) vars)))
      (svtv-probealist-sufficient-varlists (cdr x) vars)))
  ///
  (defthm add-preserves-sufficient-varlists
    (implies (svtv-probealist-sufficient-varlists x vars)
             (svtv-probealist-sufficient-varlists x (update-nth n (cons v (nth n vars)) vars)))
    :hints(("Goal" :in-theory (disable nth))))

  (defthm svtv-probealist-sufficient-of-outvars
    (svtv-probealist-sufficient-varlists x
                                         (svtv-probealist-outvars x))
    :hints(("Goal" :in-theory (enable svtv-probealist-outvars))))

  ;; (local (defthm nth-of-svex-envlist-extract
  ;;          (Equal (nth n (svex-envlist-extract vars envs))
  ;;                 (svex-env-extract (nth n vars)
  ;;                                   (nth n envs)))
  ;;          :hints(("Goal" :in-theory (enable svex-envlist-extract)))))

  (defthm svtv-probealist-extract-of-svex-envlist-extract-when-sufficient
    (implies (svtv-probealist-sufficient-varlists x vars)
             (equal (svtv-probealist-extract x (svex-envlist-extract vars envs))
                    (svtv-probealist-extract x envs)))
    :hints(("Goal" :in-theory (enable svtv-probealist-extract))))

  (local (in-theory (enable svtv-probealist-fix)))

  (local (defthm nth-out-of-bounds
           (implies (<= (len x) (nfix n))
                    (equal (nth n x) nil)))))

(defthm svtv-probealist-extract-of-svex-envlist-extract-outvars
  (equal (svtv-probealist-extract probes (svex-envlist-extract (svtv-probealist-outvars probes) envs))
         (svtv-probealist-extract probes envs))
  :hints(("Goal" :in-theory (enable svtv-probealist-outvars svtv-probealist-extract))))



(define svtv-cyclephaselist-keys ((x svtv-cyclephaselist-p))
  :returns (keys svarlist-p)
  :prepwork ((local (defthm svarlist-p-alist-keys
                      (implies (svex-env-p x)
                               (svarlist-p (alist-keys x)))
                      :hints (("goal" :in-theory (enable alist-keys))))))
  (if (atom x)
      nil
    (append (alist-keys (svtv-cyclephase->constants (car x)))
            (svtv-cyclephaselist-keys (cdr x)))))


(define svtv-cyclephaselist-no-i/o-phase ((phases svtv-cyclephaselist-p))
  (if (atom phases)
      t
    (and (b* (((svtv-cyclephase ph1) (car phases)))
           (and (not ph1.inputs-free)
                (not ph1.outputs-captured)))
         (svtv-cyclephaselist-no-i/o-phase (cdr phases)))))

(define svtv-cyclephaselist-unique-i/o-phase ((phases svtv-cyclephaselist-p))
  (if (atom phases)
      nil
    (b* (((svtv-cyclephase ph1) (car phases)))
      (or (and (not ph1.inputs-free)
               (not ph1.outputs-captured)
               (svtv-cyclephaselist-unique-i/o-phase (cdr phases)))
          (and ph1.inputs-free
               ph1.outputs-captured
               (svtv-cyclephaselist-no-i/o-phase (cdr phases)))))))
