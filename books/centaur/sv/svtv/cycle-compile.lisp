; Centaur SV Hardware Verification Package
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

(include-book "cycle-base")
(include-book "../svex/rewrite")
(include-book "../svex/unroll")
(local (std::add-default-post-define-hook :fix))

(std::make-returnspec-config :hints-sub-returnnames t)

(encapsulate nil
  (local (defthm member-of-cons
           (iff (member k (cons a b))
                (or (equal k a)
                    (member k b)))))
  (local (in-theory (disable cons-equal member-equal)))
  (local (defthmd svex-alist-extract-when-not-present
           (implies (not (member-equal (caar x) (svarlist-fix keys)))
                    (equal (svex-alist-extract keys x)
                           (svex-alist-extract keys (cdr x))))
           :hints(("Goal" :in-theory (enable (:i svex-alist-extract)
                                             svex-lookup)
                   :induct (svex-alist-extract keys x)
                   :expand ((:free (x) (svex-alist-extract keys x))
                            (svarlist-fix keys)
                            (:free (k) (hons-assoc-equal k x)))))))

  (local (defthmd svex-alist-extract-when-bad-pair
           (implies (or (not (consp (car x)))
                        (not (svar-p (caar x))))
                    (equal (svex-alist-extract keys x)
                           (svex-alist-extract keys (cdr x))))
           :hints(("Goal" :in-theory (enable (:i svex-alist-extract)
                                             svex-lookup)
                   :induct (svex-alist-extract keys x)
                   :expand ((:free (x) (svex-alist-extract keys x))
                            (:free (k) (hons-assoc-equal k x)))))))

  (local (defthm svex-alist-extract-of-cons
           (equal (svex-alist-extract (cons key rest) x)
                  (cons (cons (svar-fix key)
                              (or (svex-lookup key x)
                                  (svex-x)))
                        (svex-alist-extract rest x)))
           :hints(("Goal" :in-theory (enable svex-alist-extract)))))

  (defthm svex-alist-extract-when-same-keys
    (implies (no-duplicatesp-equal (svex-alist-keys x))
             (equal (svex-alist-extract (svex-alist-keys x) x)
                    (svex-alist-fix x)))
    :hints(("Goal" :in-theory (enable svex-alist-extract-when-bad-pair
                                      svex-alist-extract-when-not-present
                                      svex-alist-fix
                                      svex-alist-keys
                                      no-duplicatesp-equal
                                      svex-lookup)))))


(local (in-theory (disable hons-dups-p)))

(local (defthm hons-assoc-equal-of-append
         (equal (hons-assoc-equal k (append x y))
                (or (hons-assoc-equal k x)
                    (hons-assoc-equal k y)))))

(define fsm-step-subst ((in svex-alist-p)
                             (prev-st svex-alist-p)
                             (x.nextstate svex-alist-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys x.nextstate))
              (not (acl2::hons-dups-p (svex-alist-keys x.nextstate))))
  :returns (subst svex-alist-p)
  (make-fast-alist
   (append (mbe :logic (svex-alist-extract (svex-alist-keys x.nextstate)
                                           prev-st)
                :exec prev-st)
           (svex-alist-fix in)))
  ///
  (defret eval-of-fsm-step-subst
    (equal (svex-alist-eval subst env)
           (fsm-step-env (svex-alist-eval in env)
                              (svex-alist-eval prev-st env)
                              x.nextstate))
    :hints(("Goal" :in-theory (enable fsm-step-env))))

  (local (defthm svex-lookup-of-append
           (equal (svex-lookup k (append x y))
                  (or (svex-lookup k x)
                      (svex-lookup k y)))
           :hints(("Goal" :in-theory (enable svex-lookup)))))

  (defret eval-lookup-of-fsm-step-subst
    (equal (svex-eval (svex-lookup k subst) env)
           (svex-env-lookup k (fsm-step-env (svex-alist-eval in env)
                                                 (svex-alist-eval prev-st env)
                                                 x.nextstate)))
    :hints(("Goal" :in-theory (enable fsm-step-env)))))

       

(define svtv-cycle-step-phase-exprs ((prev-st svex-alist-p)
                                     (phase svtv-cyclephase-p)
                                     (x fsm-p)
                                     (simp svex-simpconfig-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (fsm->nextstate x)))))
  :returns (mv (outs svex-alist-p)
               (nextsts svex-alist-p))
  (b* (((svtv-cyclephase phase))
       ((fsm x))
       (subst (make-svex-substconfig
               :simp simp
               :alist (fsm-step-subst (svex-env-to-subst phase.constants)
                                           prev-st x.nextstate)))
       (outs (and phase.outputs-captured
                  (if phase.inputs-free
                      (svex-alist-compose-rw x.values subst)
                    (svex-alist-subst-rw x.values subst))))
       (nextsts (if phase.inputs-free
                    (svex-alist-compose-rw x.nextstate subst)
                  (svex-alist-subst-rw x.nextstate subst))))
    (fast-alist-free subst)
    (clear-memoize-table (if phase.inputs-free 'svex-compose-rw 'svex-subst-rw))
    (mv outs nextsts))
  ///
  (defret eval-outs-of-<fn>
    (equal (svex-alist-eval outs env)
           (and (svtv-cyclephase->outputs-captured phase)
                (svtv-cycle-step-phase-outs env
                                            (svex-alist-eval prev-st env)
                                            phase x)))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-outs
                                      fsm-step-env)
            :expand ((svex-alist-eval nil env)))))

  (defret eval-nextsts-of-<fn>
    (equal (svex-alist-eval nextsts env)
           (svtv-cycle-step-phase-nextsts env
                                          (svex-alist-eval prev-st env)
                                          phase (fsm->nextstate x)))
    :hints(("Goal" :in-theory (enable svtv-cycle-step-phase-nextsts
                                      fsm-step-env)
            :expand ((svex-alist-eval nil env)))))

  (local (defthm svex-eval-of-svex-lookup
           (equal (svex-eval (svex-lookup k x) env)
                  (svex-env-lookup k (svex-alist-eval x env)))
           :hints(("Goal" :in-theory (enable svex-alist-eval svex-env-lookup svex-lookup
                                             svex-env-fix svex-alist-fix)))))

  (defret eval-outs-lookup-of-<fn>
    (equal (svex-eval (svex-lookup k outs) env)
           (if (svtv-cyclephase->outputs-captured phase)
               (svex-env-lookup k
                                (svtv-cycle-step-phase-outs env
                                                            (svex-alist-eval prev-st env)
                                                            phase x))
             (svex-x)))
    :hints(("Goal" :in-theory (disable svex-env-lookup-of-svex-alist-eval <fn>))))

  (defret eval-nextsts-lookup-of-<fn>
    (equal (svex-eval (svex-lookup k nextsts) env)
           (svex-env-lookup k
                            (svtv-cycle-step-phase-nextsts env
                                                           (svex-alist-eval prev-st env)
                                                           phase (fsm->nextstate x))))
    :hints(("Goal" :in-theory (disable svex-env-lookup-of-svex-alist-eval <fn>))))

  (defret svex-alist-keys-of-<fn>-nextst
    (equal (svex-alist-keys nextsts)
           (svex-alist-keys (fsm->nextstate x)))))



;; (define svtv-cycle-compile-outs ((ins svex-alist-p)
;;                                  (prev-st svex-alist-p)
;;                                  (phases svtv-cyclephaselist-p)
;;                                  (x fsm-p))
;;   :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (fsm->nextstate x)))
;;               (not (acl2::hons-dups-p (svex-alist-keys (fsm->nextstate x)))))
;;   :returns (outs svex-alist-p)
;;   :prepwork ((local (defthm true-listp-when-svex-alist-p-rw
;;                       (implies (svex-alist-p x)
;;                                (true-listp x)))))
;;   (b* (((when (atom phases)) nil)
;;        ((mv outs1 nextst) (svtv-cycle-step-phase-exprs ins prev-st (car phases) x))
;;        (rest-outs (svtv-cycle-compile-outs ins nextst (cdr phases) x)))
;;     (mbe :logic (append outs1 rest-outs)
;;          :exec (if rest-outs
;;                    (append outs1 rest-outs)
;;                  outs1)))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval outs env)
;;            (svtv-cycle-eval-outs (svex-alist-eval ins env)
;;                                  (svex-alist-eval prev-st env)
;;                                  phases x))
;;     :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
;;             :induct t
;;             :expand ((svex-alist-eval nil env))))))


;; (define svtv-cycle-compile-nextst ((ins svex-alist-p)
;;                                 (prev-st svex-alist-p)
;;                                 (phases svtv-cyclephaselist-p)
;;                                 (x fsm-p))
;;   :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (fsm->nextstate x)))
;;               (not (acl2::hons-dups-p (svex-alist-keys (fsm->nextstate x)))))
;;   :returns (nextst svex-alist-p)
;;   (b* (((when (atom phases))
;;         (mbe :logic (svex-alist-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
;;              :exec prev-st))
;;        (nextst (svtv-cycle-step-phase-nextsts ins prev-st (car phases) x)))
;;     (svtv-cycle-compile-nextst ins nextst (cdr phases) x))
;;   ///
;;   (defret eval-of-<fn>
;;     (equal (svex-alist-eval nextst env)
;;            (svtv-cycle-eval-nextst (svex-alist-eval ins env)
;;                                  (svex-alist-eval prev-st env)
;;                                  phases x))
;;     :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
;;             :induct t
;;             :expand ((svex-alist-eval nil env)))))

;;   (defret svex-alist-keys-of-<fn>
;;     (equal (svex-alist-keys nextst)
;;            ()


(define svtv-cycle-compile ((prev-st svex-alist-p)
                            (phases svtv-cyclephaselist-p)
                            (x fsm-p)
                            (simp svex-simpconfig-p))
  :guard (and (equal (svex-alist-keys prev-st) (svex-alist-keys (fsm->nextstate x)))
              (not (acl2::hons-dups-p (svex-alist-keys (fsm->nextstate x)))))
  :returns (mv (outs svex-alist-p)
               (nextst svex-alist-p))
  :prepwork ((local (defthm true-listp-when-svex-alist-p-rw
                      (implies (svex-alist-p x)
                               (true-listp x)))))
  (b* (((when (atom phases))
        (mv nil
            (mbe :logic (svex-alist-extract (svex-alist-keys (fsm->nextstate x)) prev-st)
                 :exec (make-fast-alist prev-st))))
       ((mv outs1 nextst) (svtv-cycle-step-phase-exprs prev-st (car phases) x simp))
       ((mv rest-outs final-st) (svtv-cycle-compile nextst (cdr phases) x simp)))
    (mv (if (svtv-cyclephase->outputs-captured (car phases))
            (make-fast-alist outs1)
          rest-outs)
        final-st))
  ///
  (defret eval-outs-of-<fn>
    (equal (svex-alist-eval outs env)
           (svtv-cycle-eval-outs env
                                 (svex-alist-eval prev-st env)
                                 phases x))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-outs)
            :induct <call>
            :expand ((svex-alist-eval nil env)))))

  (defret eval-nextsts-of-<fn>
    (equal (svex-alist-eval nextst env)
           (svtv-cycle-eval-nextst env
                                   (svex-alist-eval prev-st env)
                                   phases (fsm->nextstate x)))
    :hints(("Goal" :in-theory (enable svtv-cycle-eval-nextst)
            :induct <call>
            :expand ((svex-alist-eval nil env)))))

  (defret svex-alist-keys-of-<fn>
    (equal (svex-alist-keys nextst)
           (svex-alist-keys (fsm->nextstate x)))
    :hints (("goal" :in-theory (disable <fn>
                                        alist-keys-of-svex-alist-eval)
             :use ((:instance alist-keys-of-svex-alist-eval
                    (x nextst)))))))







(define fsm-to-cycle ((phases svtv-cyclephaselist-p)
                           (x fsm-p)
                           (simp svex-simpconfig-p))
  :returns (cycle fsm-p)
  :guard (not (hons-dups-p (svex-alist-keys (fsm->nextstate x))))
  (b* (((fsm x))
       (statevars (svex-alist-keys x.nextstate))
       (prev-st (svex-identity-subst statevars))
       ((mv outs nextst)
        (with-fast-alist prev-st
          (svtv-cycle-compile prev-st phases x simp))))
    (change-fsm x :values outs :nextstate nextst))
  ///

  (defret nextst-svex-alist-keys-of-<fn>
    (equal (svex-alist-keys (fsm->nextstate cycle))
           (svex-alist-keys (fsm->nextstate x)))))


(local (defthm svex-envlist-p-of-append
         (implies (and (svex-envlist-p x)
                       (svex-envlist-p y))
                  (svex-envlist-p (append x y)))))




(defthm fsm-step-env-of-svex-env-removekeys
  (svex-envs-equivalent (fsm-step-env (svex-env-removekeys
                                            (svex-alist-keys x)
                                            in)
                                           prev-st x)
                        (fsm-step-env in prev-st x))
  :hints(("Goal" :in-theory (enable svex-envs-equivalent fsm-step-env))))


;; BOZO obvs this should be elsewhere
(define svex-envlist-remove-keys ((keys svarlist-p) (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (atom envs)
      nil
    (cons (svex-env-removekeys keys (car envs))
          (svex-envlist-remove-keys keys (cdr envs))))
  ///
  (defthm fsm-eval-of-svex-envlist-remove-statevars
    (equal (fsm-eval (svex-envlist-remove-keys
                           (svex-alist-keys (fsm->nextstate x))
                           ins)
                          prev-st x)
           (fsm-eval ins prev-st x))
    :hints(("Goal" :in-theory (enable fsm-eval fsm-step-outs fsm-step))))

  (defthm fsm-final-state-of-svex-envlist-remove-statevars
    (equal (fsm-final-state (svex-envlist-remove-keys
                                  (svex-alist-keys x)
                                  ins)
                                 prev-st x)
           (fsm-final-state ins prev-st x))
    :hints(("Goal" :in-theory (enable fsm-final-state fsm-step))))

  (defthm svex-envlist-remove-keys-of-svtv-cycle-fsm-inputs
    (equal (svex-envlist-remove-keys keys (svtv-cycle-fsm-inputs
                                           (svex-env-removekeys keys in)
                                           phases))
           (svex-envlist-remove-keys keys (svtv-cycle-fsm-inputs in phases)))
    :hints(("Goal" :in-theory (enable svtv-cycle-fsm-inputs
                                      svtv-cycle-step-fsm-inputs)))))
  








(defsection svtv-cycle-run-fsm-inputs
  (local (std::set-define-current-function svtv-cycle-run-fsm-inputs))
  (local (in-theory (enable svtv-cycle-run-fsm-inputs)))

  (local (defthm fsm-eval-of-append
           (equal (fsm-eval (append ins1 ins2) initst x)
                  (append (fsm-eval ins1 initst x)
                          (fsm-eval ins2
                                         (fsm-final-state ins1 initst (fsm->nextstate x))
                                         x)))
           :hints(("Goal" :in-theory (enable fsm-eval fsm-final-state)))))

  (local (defthm fsm-final-state-of-append
           (equal (fsm-final-state (append ins1 ins2) initst x)
                  (fsm-final-state ins2
                                        (fsm-final-state ins1 initst x)
                                        x))
           :hints(("Goal" :in-theory (enable fsm-final-state)))))

  (local (defthm nth-of-append
           (equal (nth n (append x y))
                  (if (< (nfix n) (len x))
                      (nth n x)
                    (nth (- (nfix n) (len x)) y)))
           :hints(("Goal" :in-theory (enable nth)))))

  (local (defthm member-svar-fix
           (implies (member x y)
                    (member (svar-fix x) (svarlist-fix y)))))

  (local (defthm extract-of-append-extract
           (implies (subsetp keys1 keys2)
                    (equal (svex-env-extract keys1 (append (svex-env-extract keys2 x) y))
                           (svex-env-extract keys1 x)))
           :hints(("Goal" :in-theory (enable svex-env-extract)))))

  (local (include-book "std/lists/sets" :dir :system))

  (local (defthm fsm-final-state-of-append-extract
           (equal (fsm-final-state
                   ins
                   (append (Svex-env-extract (svex-alist-keys x) initst)
                           rest)
                   x)
                  (fsm-final-state ins initst x))
           :hints (("goal" :use ((:instance fsm-final-state-of-extract-states-from-prev-st
                                  (prev-st (append (Svex-env-extract (svex-alist-keys x) initst)
                                                   rest))
                                  (x.nextstate x))
                                 (:instance fsm-final-state-of-extract-states-from-prev-st
                                  (prev-st initst)
                                  (x.nextstate x)))
                    :in-theory (disable fsm-final-state-of-extract-states-from-prev-st)))))
                                  

  (local (defthm svex-env-removekeys-of-extract
           (implies (subsetp (svarlist-fix keys2) (svarlist-fix keys1))
                    (equal (svex-env-removekeys keys1 (svex-env-extract keys2 x))
                           nil))
           :hints(("Goal" :in-theory (enable svex-env-extract svex-env-removekeys svarlist-fix)))))

  (local (include-book "tools/trivial-ancestors-check" :dir :system))
  (local (acl2::use-trivial-ancestors-check))

  (local (defthmd fsm-final-state-rewrite-envlist-remove
           (implies (and (syntaxp (not (and (consp ins) (eq (car ins) 'svex-envlist-remove-keys))))
                         (equal ins1 (svex-envlist-remove-keys (svex-alist-keys x) ins))
                         (syntaxp
                          (prog2$ (cw "ins: ~x0 ins1: ~x1~%" ins ins1)
                                  (case-match ins1
                                    (('svex-envlist-remove-keys & ins2)
                                     (not (equal ins2 ins)))
                                    (& t)))))
                    (equal (fsm-final-state ins prev-st x)
                           (fsm-final-state ins1 prev-st x)))))

  

  (local (defthmd fsm-eval-rewrite-envlist-remove
           (implies (and (syntaxp (not (and (consp ins) (eq (car ins) 'svex-envlist-remove-keys))))
                         (equal ins1 (svex-envlist-remove-keys (svex-alist-keys (fsm->nextstate x)) ins))
                         (syntaxp
                          (prog2$ (cw "ins: ~x0 ins1: ~x1~%" ins ins1)
                                  (case-match ins1
                                    (('svex-envlist-remove-keys & ins2)
                                     (not (equal ins2 ins)))
                                    (& t)))))
                    (equal (fsm-eval ins prev-st x)
                           (fsm-eval ins1 prev-st x)))))

  (local (defthmd svex-envlist-remove-keys-of-cycle-fsm-inputs-rewrite
           (implies (and (syntaxp (not (and (consp ins) (eq (car ins) 'svex-env-removekeys))))
                         (equal ins1 (svex-env-removekeys (svex-alist-keys x.nextstate) ins))
                         (syntaxp
                          (prog2$ (cw "ins: ~x0 ins1: ~x1~%" ins ins1)
                                  (case-match ins1
                                    (('svex-env-removekeys & ins2)
                                     (not (equal ins2 ins)))
                                    (& t)))))
                    (equal (svex-envlist-remove-keys
                            (svex-alist-keys x.nextstate)
                            (svtv-cycle-fsm-inputs ins phases))
                           (svex-envlist-remove-keys
                            (svex-alist-keys x.nextstate)
                            (svtv-cycle-fsm-inputs ins1 phases))))))

  (local (defthm fsm-final-state-of-cycle-fsm-append-extract
           (equal (fsm-final-state
                   (svtv-cycle-fsm-inputs
                    (append (svex-env-extract (svex-alist-keys x) foo) ins)
                    phases)
                   initst x)
                  (fsm-final-state (svtv-cycle-fsm-inputs ins phases) initst x))
           :hints(("Goal" :in-theory (enable fsm-final-state-rewrite-envlist-remove
                                             svex-envlist-remove-keys-of-cycle-fsm-inputs-rewrite)))))


  (local (defthm fsm-eval-of-cycle-fsm-append-extract
           (equal (fsm-eval
                   (svtv-cycle-fsm-inputs
                    (append (svex-env-extract (svex-alist-keys (fsm->nextstate x)) foo) ins)
                    phases)
                   initst x)
                  (fsm-eval (svtv-cycle-fsm-inputs ins phases) initst x))
           :hints(("Goal" :in-theory (enable fsm-eval-rewrite-envlist-remove
                                             svex-envlist-remove-keys-of-cycle-fsm-inputs-rewrite)))))

                                                         


  (defthm fsm-step-of-cycle-in-terms-of-fsm
    (b* ((cycle-fsm (fsm-to-cycle phases x simp)))
      (equal (fsm-step ins initst (fsm->nextstate cycle-fsm))
             (fsm-final-state (svtv-cycle-fsm-inputs ins phases) initst (fsm->nextstate x))))
    :hints(("Goal" :in-theory (enable fsm-to-cycle fsm-step fsm-step-env
                                      svtv-cycle-eval-nextst-is-fsm-final-state-of-fsm-inputs))))

  (defthm fsm-step-outs-of-cycle-in-terms-of-fsm
    (b* ((cycle-fsm (fsm-to-cycle phases x simp)))
      (equal (fsm-step-outs ins initst cycle-fsm)
             (let ((output-phase (svtv-cycle-output-phase phases)))
               (and output-phase
                    (nth output-phase
                         (fsm-eval (svtv-cycle-fsm-inputs ins phases) initst x))))))
    :hints(("Goal" :in-theory (enable fsm-to-cycle fsm-step-outs fsm-step-env
                                      svtv-cycle-eval-outs-is-fsm-eval-of-fsm-inputs))))

  (local (defun ind1 (ins initst phases x)
           (if (atom ins)
               initst
             (ind1 (cdr ins)
                   (svtv-cycle-eval-nextst (car ins) initst phases (fsm->nextstate x))
                   phases x))))

  (defthm fsm-final-state-of-cycle-in-terms-of-fsm
    (b* ((cycle-fsm (fsm-to-cycle phases x simp)))
      (equal (fsm-final-state ins initst (fsm->nextstate cycle-fsm))
             (fsm-final-state (svtv-cycle-run-fsm-inputs ins phases) initst (fsm->nextstate x))))
    :hints (("goal" :induct (ind1 ins initst phases x)
             :expand ((svtv-cycle-run-fsm-inputs ins phases)
                      (:free (fsm) (fsm-final-state ins initst fsm))
                      (:free (x) (fsm-final-state nil initst x)))
             :in-theory (enable svtv-cycle-eval-nextst-is-fsm-final-state-of-fsm-inputs
                                fsm-step fsm-step-env))))

  (local (defun ind (n ins initst phases x)
           (if (zp n)
               (list ins initst)
             (ind (1- n) (cdr ins)
                  (svtv-cycle-eval-nextst (car ins) initst phases (fsm->nextstate x))
                  phases x))))

  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (local (defthm nat-times-nat-type
           (implies (and (natp n) (natp m))
                    (natp (* n m)))
           :rule-classes :type-prescription))

  (local (defthm lemma
           (implies (and (natp n) (posp m))
                    (<= n (* m n)))
           :rule-classes :linear))

  (local (defthm svtv-cycle-output-phase-limit
           (implies (svtv-cycle-output-phase phases)
                    (< (svtv-cycle-output-phase phases) (len phases)))
           :hints(("Goal" :in-theory (enable svtv-cycle-output-phase)))
           :rule-classes :linear))

  (defthm fsm-eval-of-cycle-in-terms-of-fsm
    (b* ((cycle-fsm (fsm-to-cycle phases x simp)))
      (equal (nth n (fsm-eval ins initst cycle-fsm))
             (let ((output-phase (svtv-cycle-output-phase phases)))
               (and output-phase
                    (nth (+ output-phase (* (nfix n) (len phases)))
                         (fsm-eval (svtv-cycle-run-fsm-inputs ins phases) initst x))))))
    :hints (("goal" :induct (ind n ins initst phases x)
             :expand ((svtv-cycle-run-fsm-inputs ins phases)
                      (:free (fsm) (fsm-eval ins initst fsm)))
             :in-theory (enable svtv-cycle-eval-nextst-is-fsm-final-state-of-fsm-inputs
                                svtv-cycle-eval-outs-is-fsm-eval-of-fsm-inputs))))

  (local (in-theory (enable svex-envlist-fix))))



(define svtv-cyclephaselist-has-outputs-captured ((phases svtv-cyclephaselist-p))
  (if (atom phases)
      nil
    (or (svtv-cyclephase->outputs-captured (car phases))
        (svtv-cyclephaselist-has-outputs-captured (cdr phases))))
  ///
  (defthm svex-alist-keys-of-svtv-cycle-compile-values
    (equal (svex-alist-keys (mv-nth 0 (svtv-cycle-compile prev-st phases x simp)))
           (and (svtv-cyclephaselist-has-outputs-captured phases)
                (svex-alist-keys (fsm->values x))))
    :hints(("Goal" :in-theory (enable svtv-cycle-compile
                                      svtv-cycle-step-phase-exprs)))))
