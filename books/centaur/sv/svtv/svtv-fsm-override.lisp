;; SV - Symbolic Vector Hardware Analysis Framework

;; INTEL TEMPORARY COPYRIGHT HEADER --
;; Not for public distribution until this is replaced with a proper license!

;; Original author: Sol Swords <sol.swords@intel.com>

(in-package "SV")

(include-book "../svex/override")
(include-book "svtv-stobj-export")
(include-book "centaur/fgl/def-fgl-thm" :dir :system)
(include-book "centaur/misc/starlogic" :dir :system)
(local (include-book "../svex/alist-thms"))
(local (include-book "std/lists/sets" :dir :system))

(local (std::add-default-post-define-hook :fix))





(define pipeline-run ((setup pipeline-setup-p)
                      (namemap svtv-name-lhs-map-p)
                      (cycle base-fsm-p)
                      (env svex-env-p))
  :guard (and (equal (svex-alist-keys (pipeline-setup->initst setup))
                     (svex-alist-keys (base-fsm->nextstate cycle)))
              (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate cycle)))))
  :guard-hints (("goal" :in-theory (enable svtv-fsm->renamed-fsm)))
  (b* ((fsm (svtv-fsm cycle namemap))
       ((pipeline-setup setup))
       (outvars (svtv-probealist-outvars setup.probes)))
    (SVTV-PROBEALIST-EXTRACT
     setup.probes
     (BASE-FSM-RUN
      (SVEX-ALISTLIST-EVAL
       (SVTV-FSM-RUN-INPUT-SUBSTS
        (TAKE
         (LEN outvars)
         setup.inputs)
        setup.overrides
        fsm)
       ENV)
      (SVEX-ALIST-EVAL setup.initst ENV)
      (SVTV-FSM->RENAMED-FSM fsm)
      outvars))))







(define svex-envlist-removekeys* ((vars svarlist-list-p)
                                  (envs svex-envlist-p))
  (if (atom envs)
      nil
    (cons (svex-env-removekeys (car vars) (car envs))
          (svex-envlist-removekeys* (cdr vars) (cdr envs))))
  ///
  (defthm svex-envlist-removekeys*-of-cons
    (Equal (svex-envlist-removekeys* vars (cons env envs))
           (cons (svex-env-removekeys (car vars) env)
                 (svex-envlist-removekeys* (cdr vars) envs))))

  ;; (defthm svex-envlist-removekeys*-of-append
  ;;   (Equal (svex-envlist-removekeys* vars (append envs envs2))
  ;;          (append (svex-envlist-removekeys* vars envs)
  ;;                  (svex-envlist-removekeys* (nthcdr (len envs) vars) envs2))))
  )

(fty::deflist svex-override-triplelistlist :elt-type svex-override-triplelist :true-listp t)

;; (define subsetlist-p ((x true-list-listp) (y true-listp))
;;   (if (atom x)
;;       t
;;     (and (subsetp-equal (car x) y)
;;          (subsetlist-p (cdr x) y))))


(define svex-override-triple-subsetlist-p ((x svex-override-triplelistlist-p)
                                           (triples  svex-override-triplelist-p))
  (if (atom x)
      t
    (and (no-duplicatesp-equal (svex-override-triplelist-vars (car x)))
         (subsetp-equal (svex-override-triplelist-fix (car x))
                        (svex-override-triplelist-fix triples))
         (svex-override-triple-subsetlist-p (cdr x) triples)))
  ///
  (defthm svex-override-triple-subsetlist-p-of-cdr
    (implies (svex-override-triple-subsetlist-p x triples)
             (svex-override-triple-subsetlist-p (cdr x) triples)))

  (defthm no-duplicatesp-car-when-svex-override-triplelist-p
    (implies (svex-override-triple-subsetlist-p x triples)
             (no-duplicatesp-equal (svex-override-triplelist-vars (car x)))))

  (defthm svexlist-check-overridetriples-car-when-svex-override-triplelist-p
    (implies (and (svex-override-triple-subsetlist-p x triples)
                  (no-duplicatesp-equal (svex-override-triplelist-vars triples))
                  (not (svexlist-check-overridetriples svexes triples)))
             (not (svexlist-check-overridetriples svexes (car x))))
    :hints(("Goal" :in-theory (enable svexlist-check-overridetriples-when-subset)))))


(define svex-override-triplelistlist-vars ((x svex-override-triplelistlist-p))
  :guard-hints (("goal" :in-theory (enable svex-override-triplelistlist-p)))
  :returns (vars svarlist-list-p)
  (if (atom x)
      nil
    (cons (svex-override-triplelist-vars (car x))
          (svex-override-triplelistlist-vars (cdr x)))))


(define svex-override-triplelistlist-testvars ((x svex-override-triplelistlist-p))
  :guard-hints (("goal" :in-theory (enable svex-override-triplelistlist-p)))
  :returns (vars svarlist-list-p)
  (if (atom x)
      nil
    (cons (svex-override-triplelist-testvars (car x))
          (svex-override-triplelistlist-testvars (cdr x)))))



(define svex-override-triplelist-fsm-inputs-ok* ((triples svex-override-triplelistlist-p)
                                                 (envs svex-envlist-p)
                                                 (prev-envs svex-envlist-p)
                                                 (initst svex-env-p)
                                                 (fsm base-fsm-p))
  :guard (and (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate fsm)))
              (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate fsm)))))
  :measure (len prev-envs)
  (if (atom prev-envs)
      t
    (and (svex-override-triplelist-env-ok (car triples)
                                          (base-fsm-step-env (car envs) initst fsm)
                                          (base-fsm-step-env (car prev-envs) initst fsm))
         (svex-override-triplelist-fsm-inputs-ok* (cdr triples)
                                                  (cdr envs)
                                                  (cdr prev-envs)
                                                  (base-fsm-step (car prev-envs) initst fsm)
                                                  fsm)))
  ///
  (defthm svex-override-triplelist-fsm-inputs-ok*-of-cons
    (equal (svex-override-triplelist-fsm-inputs-ok* triples
                                                    (cons env envs)
                                                    (cons prev-env prev-envs)
                                                    initst fsm)
           (and (svex-override-triplelist-env-ok (car triples)
                                                 (base-fsm-step-env env initst fsm)
                                                 (base-fsm-step-env prev-env initst fsm))
                (svex-override-triplelist-fsm-inputs-ok* (cdr triples) envs prev-envs
                                                         (base-fsm-step prev-env initst fsm)
                                                         fsm))))

  (defthm svex-override-triplelist-fsm-inputs-ok*-of-nil
    (equal (svex-override-triplelist-fsm-inputs-ok* triples envs nil initst fsm)
           t))

  (defthm svex-override-triplelist-fsm-inputs-ok*-of-svex-alistlist-eval-cons
    (equal (svex-override-triplelist-fsm-inputs-ok* triples
                                                    envs
                                                    (svex-alistlist-eval (cons prev-env-al prev-env-als) env1)
                                                    initst fsm)
           (and (svex-override-triplelist-env-ok (car triples)
                                                 (base-fsm-step-env (car envs) initst fsm)
                                                 (base-fsm-step-env (svex-alist-eval prev-env-al env1) initst fsm))
                (svex-override-triplelist-fsm-inputs-ok* (cdr triples)
                                                         (cdr envs)
                                                         (svex-alistlist-eval prev-env-als env1)
                                                         (base-fsm-step (svex-alist-eval prev-env-al env1) initst fsm)
                                                         fsm))))

  (defcong svex-envs-similar equal (svex-override-triplelist-fsm-inputs-ok* triples envs prev-envs prev-st fsm) 4))



(defprod svar-override-triple
  ((testvar svar-p)
   (valvar svar-p)
   (refvar svar-p))
  :layout :list)

(fty::deflist svar-override-triplelist :elt-type svar-override-triple :true-listp t)

(define svar->svex-override-triplelist ((x svar-override-triplelist-p)
                                        (values svex-alist-p))
  :returns (triples svex-override-triplelist-p)
  (if (atom x)
      nil
    (cons (b* (((svar-override-triple x1) (car x)))
            (make-svex-override-triple :testvar x1.testvar
                                       :valvar x1.valvar
                                       :valexpr (or (svex-fastlookup x1.refvar values)
                                                    (svex-x))))
          (svar->svex-override-triplelist (cdr x) values))))


(defprojection svar-override-triplelist->valvars ((x svar-override-triplelist-p))
  :returns (valvars svarlist-p)
  (svar-override-triple->valvar x))

(defprojection svar-override-triplelist->testvars ((x svar-override-triplelist-p))
  :returns (testvars svarlist-p)
  (svar-override-triple->testvar x))

(defprojection svar-override-triplelist->refvars ((x svar-override-triplelist-p))
  :returns (refvars svarlist-p)
  (svar-override-triple->refvar x))



(local (defthm consp-hons-assoc-equal
         (iff (consp (hons-assoc-equal k x))
              (hons-assoc-equal k x))))


(local (defthm svex-env-boundp-when-member-svex-env-alist-keys
         (implies (member-equal (svar-fix v) (alist-keys (svex-env-fix env)))
                  (svex-env-boundp v env))
         :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-fix alist-keys)))))

(define svar-override-triplelist-env-ok ((x svar-override-triplelist-p)
                                         (override-env svex-env-p)
                                         (ref-env svex-env-p))
  (if (atom x)
      t
    (acl2::and*
     (b* (((svar-override-triple trip) (car x))
          (testval (svex-env-lookup trip.testvar override-env))
          (valval (svex-env-lookup trip.valvar override-env))
          (refval (svex-env-lookup trip.refvar ref-env)))
       (or (equal (4vec-bit?! testval valval 0)
                  (4vec-bit?! testval refval 0))
           (prog2$ (cw "~x0: failed signal: ~x1.~%" std::__function__ trip.refvar)
                   (svtv-print-alist-readable
                    `((test . ,(2vec (logand (4vec->upper testval) (4vec->lower testval))))
                      (val  . ,(4vec-bit?! testval valval 0))
                      (ref  . ,(4vec-bit?! testval refval 0)))))))
     (svar-override-triplelist-env-ok (cdr x) override-env ref-env)))
  ///
  (defthm svar-override-triplelist-env-ok-in-terms-of-svex-override-triplelist-env-ok
    (equal (svar-override-triplelist-env-ok x override-env (svex-alist-eval values prev-env))
           (svex-override-triplelist-env-ok
            (svar->svex-override-triplelist x values)
            override-env prev-env))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-env-ok
                                      svar->svex-override-triplelist))))

  (defthm svar-override-triplelist-env-ok-of-append-ref-envs-when-subsetp-first
    (implies (subsetp-equal (svar-override-triplelist->refvars x)
                            (alist-keys (svex-env-fix ref-env)))
             (equal (svar-override-triplelist-env-ok x override-env (append ref-env ref-env2))
                    (svar-override-triplelist-env-ok x override-env ref-env)))
    :hints(("Goal" :in-theory (enable svar-override-triplelist->refvars)))))

(local (defthmd svex-env-boundp-iff-member-svex-env-alist-keys
         (iff (svex-env-boundp v env)
              (member-equal (svar-fix v) (alist-keys (svex-env-fix env))))
         :hints(("Goal" :in-theory (enable svex-env-boundp svex-env-fix alist-keys)))))

(local (defthm car-of-nthcdr
         (equal (car (nthcdr n x)) (nth n x))))
(local (defthm cdr-of-nthcdr
         (equal (cdr (nthcdr n x)) (nthcdr n (cdr x)))))
(local (defthm nthcdr-of-nil
         (equal (nthcdr n nil) nil)))
(local (defthm consp-of-nthcdr
         (iff (consp (nthcdr n x))
              (< (nfix n) (len x)))))

(local (defun nth-of-base-fsm-eval-ind (n ins st fsm)
         (if (zp n)
             (list ins st fsm)
           (nth-of-base-fsm-eval-ind (1- n) (cdr ins)
                                     (base-fsm-step (car ins) st fsm)
                                     fsm))))

(local (Defthm svex-env-lookup-when-not-bound
         (implies (not (svex-env-boundp k x))
                  (equal (svex-env-lookup k x) (4vec-x)))
         :hints(("Goal" :in-theory (enable svex-env-lookup svex-env-boundp)))))

(local (defthm svex-envs-equivalent-of-extract-keys
         (implies (equal keys (alist-keys (svex-env-fix x)))
                  (svex-envs-equivalent (svex-env-extract keys x) x))
         :hints(("Goal" :in-theory (enable svex-envs-equivalent
                                           svex-env-boundp-iff-member-svex-env-alist-keys)))))

(local (defthm base-fsm-final-state-of-take-n+1
         (implies (and (natp n)
                       ;; (no-duplicatesp-equal (svex-alist-keys (base-fsm->nextstate x)))
                       )
                  (svex-envs-equivalent
                   (base-fsm-final-state (take (+ 1 n) ins) prev-st x)
                   (base-fsm-step (nth n ins)
                                  (base-fsm-final-state (take n ins) prev-st x)
                                  x)))
         :hints(("Goal" :in-theory (e/d (take nth base-fsm-final-state)
                                        (acl2::take-of-too-many
                                         acl2::take-when-atom))
                 :induct (nth-of-base-fsm-eval-ind n ins prev-st x)
                 :expand ((take 1 ins)))
                (and stable-under-simplificationp
                     '(:in-theory (enable base-fsm-step))))))



(fty::deflist svar-override-triplelistlist :elt-type svar-override-triplelist :true-listp t)

(define svar->svex-override-triplelistlist ((x svar-override-triplelistlist-p)
                                            (values svex-alist-p))
  :returns (svex-triples svex-override-triplelistlist-p)
  (if (atom x)
      nil
    (cons (svar->svex-override-triplelist (car x) values)
          (svar->svex-override-triplelistlist (cdr x) values))))

(define svar-override-triplelist-override-vars ((x svar-override-triplelist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (b* (((svar-override-triple x1) (car x)))
      (cons x1.testvar (cons x1.valvar (svar-override-triplelist-override-vars (cdr x))))))
  ///
  (defthm svex-override-triplelist-vars-of-svar->svex-override-triplelist
    (equal (svex-override-triplelist-vars (svar->svex-override-triplelist x values))
           (svar-override-triplelist-override-vars x))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-vars svar->svex-override-triplelist)))))


(define svar-override-triplelistlist-override-vars ((x svar-override-triplelistlist-p))
  :returns (vars svarlist-list-p)
  (if (atom x)
      nil
    (cons (svar-override-triplelist-override-vars (car x))
          (svar-override-triplelistlist-override-vars (cdr x))))
  ///
  (defthm svex-override-triplelistlist-vars-of-svar->svex-override-triplelistlist
    (equal (svex-override-triplelistlist-vars (svar->svex-override-triplelistlist x values))
           (svar-override-triplelistlist-override-vars x))
    :hints(("Goal" :in-theory (enable svex-override-triplelistlist-vars svar->svex-override-triplelistlist)))))





(define append-svarlists ((x svarlist-list-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (svarlist-fix (car x))
            (append-svarlists (cdr x)))))

(define svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval ((cycle natp)
                                                             (triples svar-override-triplelistlist-p)
                                                             (envs svex-envlist-p)
                                                             (eval svex-envlist-p))
  :guard (<= cycle (len eval))
  :measure (nfix (- (len eval) (nfix cycle)))
  (if (zp (- (len eval) (lnfix cycle)))
      t
    (acl2::and* (or (svar-override-triplelist-env-ok (car triples)
                                                     (make-fast-alist (car envs))
                                                     (make-fast-alist (nth cycle eval)))
                    (cw "~x0: previous fails from cycle ~x1~%" std::__function__ cycle))
                (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval (+ 1 (lnfix cycle))
                                                                     (cdr triples)
                                                                     (cdr envs)
                                                                     eval)))
  ///
  (local (defun ind (cycle triples envs eval)
           (declare (xargs :measure (nfix (- (len eval) (nfix cycle)))))
           (if (zp (- (len eval) (nfix cycle)))
               (list triples envs)
             (ind (1+ (lnfix cycle)) (cdr triples) (cdr envs) eval))))

  (defthm svex-override-triplelist-env-ok-of-append-non-overrides
    (implies (not (intersectp-equal (svex-override-triplelist-vars triples)
                                    (alist-keys (svex-env-fix a))))
             (equal (svex-override-triplelist-env-ok
                     triples (append a b) prev-env)
                    (svex-override-triplelist-env-ok
                     triples b prev-env)))
    :hints(("Goal" :in-theory (enable svex-override-triplelist-env-ok
                                      svex-override-triplelist-vars
                                      svex-env-boundp-iff-member-svex-env-alist-keys))))
  
  (defthm svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval-of-base-fsm-eval
    (implies (not (intersectp-equal (append-svarlists (svar-override-triplelistlist-override-vars triples))
                                    (svex-alist-keys (base-fsm->nextstate fsm))))
             (equal (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                     cycle triples envs (base-fsm-eval ins prev-st fsm))
                    (svex-override-triplelist-fsm-inputs-ok*
                     (svar->svex-override-triplelistlist triples (base-fsm->values fsm))
                     envs (nthcdr cycle ins)
                     (base-fsm-final-state (take cycle ins) prev-st fsm)
                     fsm)))
    :hints(("Goal" :in-theory (e/d (nth-of-base-fsm-eval
                                    base-fsm-step-outs
                                    append-svarlists
                                    svar-override-triplelistlist-override-vars
                                    base-fsm-step-env)
                                   (take))
            :induct (ind cycle triples envs ins) ;; bit of a hack but it works
            :expand ((:free (triples eval-ins prev-st) (svex-override-triplelist-fsm-inputs-ok* triples envs eval-ins prev-st fsm))
                     (:free (eval) (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                                    cycle triples envs eval))
                     (:free (values) (svar->svex-override-triplelistlist triples values))
                     (:free (values) (svar->svex-override-triplelistlist nil values))
                     (:free (values) (svar->svex-override-triplelist nil values)))))))







(define svex-envlist-removekeys ((vars svarlist-p)
                                 (envs svex-envlist-p))
  (if (atom envs)
      nil
    (cons (svex-env-removekeys vars (car envs))
          (svex-envlist-removekeys vars (cdr envs))))
  ///
  (defthm svex-envlist-removekeys-of-cons
    (Equal (svex-envlist-removekeys vars (cons env envs))
           (cons (svex-env-removekeys vars env)
                 (svex-envlist-removekeys vars envs))))

  (defthm svex-envlist-removekeys-of-append
    (Equal (svex-envlist-removekeys vars (append envs envs2))
           (append (svex-envlist-removekeys vars envs)
                   (svex-envlist-removekeys vars envs2)))))


(define svex-override-triplelist-fsm-inputs-ok ((triples svex-override-triplelist-p)
                                                (envs svex-envlist-p)
                                                (prev-envs svex-envlist-p)
                                                (initst svex-env-p)
                                                (fsm base-fsm-p))
  :guard (and (equal (alist-keys initst)
                     (svex-alist-keys (base-fsm->nextstate fsm)))
              (not (hons-dups-p (svex-alist-keys (base-fsm->nextstate fsm)))))
  (if (atom envs)
      t
    (and (svex-override-triplelist-env-ok triples
                                          (base-fsm-step-env (car envs) initst fsm)
                                          (base-fsm-step-env (car prev-envs) initst fsm))
         (svex-override-triplelist-fsm-inputs-ok triples (cdr envs) (cdr prev-envs)
                                                 (base-fsm-step (car prev-envs) initst fsm)
                                                 fsm)))
  ///
  (defthm svex-override-triplelist-fsm-inputs-ok-of-cons
    (equal (svex-override-triplelist-fsm-inputs-ok triples
                                                   (cons env envs)
                                                   (cons prev-env prev-envs)
                                                   initst fsm)
           (and (svex-override-triplelist-env-ok triples
                                                 (base-fsm-step-env env initst fsm)
                                                 (base-fsm-step-env prev-env initst fsm))
                (svex-override-triplelist-fsm-inputs-ok triples envs prev-envs
                                                        (base-fsm-step prev-env initst fsm)
                                                        fsm))))

  (defthm svex-override-triplelist-fsm-inputs-ok-of-nil
    (equal (svex-override-triplelist-fsm-inputs-ok triples nil prev-envs initst fsm)
           t))

  (defthm svex-override-triplelist-fsm-inputs-ok-of-svex-alistlist-eval-cons
    (equal (svex-override-triplelist-fsm-inputs-ok triples
                                                   (svex-alistlist-eval (cons env-al env-als) env1)
                                                   prev-envs
                                                   initst fsm)
           (and (svex-override-triplelist-env-ok triples
                                                 (base-fsm-step-env (svex-alist-eval env-al env1) initst fsm)
                                                 (base-fsm-step-env (car prev-envs) initst fsm))
                (svex-override-triplelist-fsm-inputs-ok triples
                                                        (svex-alistlist-eval env-als env1)
                                                        (cdr prev-envs)
                                                        (base-fsm-step (car prev-envs) initst fsm)
                                                        fsm)))))


(define svex-envlists-extract* ((vars svarlist-list-p)
                                (envs svex-envlist-p))
  :returns (new-envs svex-envlist-p)
  (if (atom envs)
      nil
    (cons (svex-env-extract (car vars) (car envs))
          (svex-envlists-extract* (cdr vars) (cdr envs))))
  ///
  (defret len-of-<fn>
    (equal (len new-envs)
           (len envs)))

  (local (defun nth-ind (n vars envs)
           (if (zp n)
               (list vars envs)
             (nth-ind (1- n) (cdr vars) (cdr envs)))))
  
  (defret nth-of-<fn>
    (equal (nth n new-envs)
           (and (< (nfix n) (len envs))
                (svex-env-extract (nth n vars) (nth n envs))))
    :hints(("Goal" :in-theory (enable nth)
            :expand <call>
            :induct (nth-ind n vars envs)))))

(define svex-envlist-keys-no-1s*-p ((vars svarlist-list-p)
                                    (envs svex-envlist-p))
  (if (atom vars)
      t
    (and (svex-env-keys-no-1s-p (car vars) (car envs))
         (svex-envlist-keys-no-1s*-p (cdr vars) (cdr envs)))))
            

(local
 (defsection triplelist-vars-lemmas
   (defretd not-member-when-not-lookup-<fn>
     (implies (and (not (svex-override-triplelist-lookup var x))
                   (not (svex-override-triplelist-lookup-valvar var x)))
              (not (member-equal (svar-fix var) vars)))
     :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                       svex-override-triplelist-lookup-valvar
                                       svex-override-triplelist-lookup)))
     :fn svex-override-triplelist-vars)

   (Defthm member-vars-when-member-has-test-var
     (implies (and (member-equal trip (svex-override-triplelist-fix x))
                   (equal var (svex-override-triple->testvar trip)))
              (member-equal var (svex-override-triplelist-vars x)))
     :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                       svex-override-triplelist-fix))))

  

   (Defthm member-vars-when-member-has-valvar
     (implies (and (member-equal trip (svex-override-triplelist-fix x))
                   (equal var (svex-override-triple->valvar trip)))
              (member-equal var (svex-override-triplelist-vars x)))
     :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                       svex-override-triplelist-fix))))

   (defthm svex-override-triplelist-vars-subsetp-when-triples-subsetp
     (implies (subsetp-equal (svex-override-triplelist-fix x)
                             (svex-override-triplelist-fix y))
              (subsetp-equal (svex-override-triplelist-vars x)
                             (svex-override-triplelist-vars y)))
     :hints (("goal" :in-theory (e/d (acl2::subsetp-witness-rw)
                                     (not-member-when-not-lookup-svex-override-triplelist-vars
                                      member-vars-when-member-has-valvar
                                      member-vars-when-member-has-test-var))
              :use (;; (:instance not-lookup-when-not-member-svex-override-triplelist-vars
                    ;;  (x y) (var (acl2::subsetp-witness (svex-override-triplelist-vars x)
                    ;;                                    (svex-override-triplelist-vars y))))
                    (:instance member-vars-when-member-has-test-var
                     (trip (svex-override-triplelist-lookup
                            (acl2::subsetp-witness (svex-override-triplelist-vars x)
                                                   (svex-override-triplelist-vars y))
                            x))
                     (x (svex-override-triplelist-fix y))
                     (var (acl2::subsetp-witness (svex-override-triplelist-vars x)
                                                 (svex-override-triplelist-vars y))))
                    (:instance member-vars-when-member-has-valvar
                     (trip (svex-override-triplelist-lookup-valvar
                            (acl2::subsetp-witness (svex-override-triplelist-vars x)
                                                   (svex-override-triplelist-vars y))
                            x))
                     (x (svex-override-triplelist-fix y))
                     (var (acl2::subsetp-witness (svex-override-triplelist-vars x)
                                                 (svex-override-triplelist-vars y))))
                    (:instance not-member-when-not-lookup-svex-override-triplelist-vars
                     (x x) (var (acl2::subsetp-witness (svex-override-triplelist-vars x)
                                                       (svex-override-triplelist-vars y))))))))
  

   (local (in-theory (disable acl2::intersectp-equal-commute)))

   (defthmd not-intersectp-when-subsetp
     (implies (and (not (intersectp-equal x z))
                   (subsetp y x))
              (not (intersectp-equal y z)))
     :hints(("Goal" :in-theory (enable intersectp-equal subsetp))))
  
   (defthm svex-override-triple-subsetlistp-implies-not-intersectp
     (implies (and (svex-override-triple-subsetlist-p x triples)
                   (not (intersectp-equal (svex-override-triplelist-vars triples) vars)))
              (not (intersectp-equal (svex-override-triplelist-vars (car x)) vars)))
     :hints(("Goal" :in-theory (enable svex-override-triple-subsetlist-p
                                       not-intersectp-when-subsetp))))))

(encapsulate nil
  (local (defthm append-extract-removekeys
           (implies (and (not (intersectp-equal vars keys))
                         (svarlist-p vars)
                         (svarlist-p keys))
                    (equal (append (svex-env-extract keys x)
                                   (svex-env-removekeys vars y))
                           (svex-env-removekeys
                            vars (append (svex-env-extract keys x) y))))
           :hints(("Goal" :in-theory (enable svex-env-removekeys
                                             svex-env-extract)))))
  (local (in-theory (disable svex-env-removekeys-of-append)))

  (local (defthm base-fsm-step-env-of-removekeys
           (implies (and (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm))))
                         (svarlist-p vars))
                    (equal (base-fsm-step-env
                            (svex-env-removekeys vars in)
                            initst fsm)
                           (svex-env-removekeys vars
                                                (base-fsm-step-env in initst fsm))))
           :hints(("Goal" :in-theory (enable base-fsm-step-env)))))

  (defthm remove-override-vars-of-base-fsm-eval
    (b* ((vars (svex-override-triplelist-vars triples))
         (prev-envs (svex-envlist-removekeys vars envs))
         ((base-fsm fsm))
         (bad1 (svexlist-check-overridetriples (svex-alist-vals fsm.values) triples))
         (bad2 (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) triples)))
      (implies (and (not bad1)
                    (not bad2)
                    (no-duplicatesp-equal vars)
                    (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm))))
                    (svex-override-triplelist-fsm-inputs-ok triples envs prev-envs initst fsm))
               (equal (base-fsm-eval prev-envs initst fsm)
                      (base-fsm-eval envs initst fsm))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      svex-override-triplelist-fsm-inputs-ok
                                      svex-envlist-removekeys
                                      base-fsm-step
                                      base-fsm-step-outs)
            :induct (base-fsm-eval envs initst fsm))))


  (defun remove-override-vars-of-base-fsm-eval*-ind (triplelist envs initst fsm)
    (declare (xargs :measure (len envs)))
    (if (atom envs)
        (list triplelist initst fsm)
      (remove-override-vars-of-base-fsm-eval*-ind (cdr triplelist)
                                                  (cdr envs)
                                                  (base-fsm-step (svex-env-removekeys
                                                                  (svex-override-triplelist-vars (car triplelist))
                                                                  (car envs))
                                                                 initst fsm)
                                                  fsm)))

  (local (defthm svex-env-removekeys-when-keys-nil
           (equal (svex-env-removekeys nil env)
                  (svex-env-fix env))
           :hints(("Goal" :in-theory (enable svex-env-removekeys
                                             svex-env-fix)))))

  (local (defthm svex-envlist-removekeys*-when-keys-nil
           (equal (svex-envlist-removekeys* nil env)
                  (svex-envlist-fix env))
           :hints(("Goal" :in-theory (enable svex-envlist-removekeys*
                                             svex-envlist-fix)))))

  
  (defthm remove-override-vars-of-base-fsm-eval*
    (b* ((vars (svex-override-triplelist-vars triples))
         (varslist (svex-override-triplelistlist-vars triplelist))
         (prev-envs (svex-envlist-removekeys* varslist envs))
         ((base-fsm fsm))
         (bad1 (svexlist-check-overridetriples (svex-alist-vals fsm.values) triples))
         (bad2 (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) triples)))
      (implies (and (not bad1)
                    (not bad2)
                    (svex-override-triple-subsetlist-p triplelist triples)
                    (no-duplicatesp-equal vars)
                    (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm))))
                    (svex-override-triplelist-fsm-inputs-ok* triplelist envs prev-envs initst fsm))
               (equal (base-fsm-eval prev-envs initst fsm)
                      (base-fsm-eval envs initst fsm))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      svex-override-triplelist-fsm-inputs-ok*
                                      svex-override-triplelistlist-vars
                                      svex-envlist-removekeys*
                                      base-fsm-step
                                      base-fsm-step-outs)
            :expand ((:free (vars) (svex-envlist-removekeys* vars envs))
                     (:free (envs) (base-fsm-eval envs initst fsm)))
            :induct (remove-override-vars-of-base-fsm-eval*-ind triplelist envs initst fsm)))))



(define svex-envlists-append-corresp ((x svex-envlist-p)
                                      (y svex-envlist-p))
  :Returns (new svex-envlist-p)
  (if (atom x)
      nil
    (cons (append (svex-env-fix (car x))
                  (svex-env-fix (car y)))
          (svex-envlists-append-corresp (cdr x) (cdr y))))
  ///
  (defret len-of-<fn>
    (equal (len new) (len x)))

  (local (defun nth-ind (n x y)
           (if (zp n)
               (list x y)
             (nth-ind (1- n) (cdr x) (cdr y)))))

  (defret nth-of-<fn>
    (implies (< (nfix n) (len x))
             (equal (nth n new)
                    (append (svex-env-fix (nth n x))
                            (svex-env-fix (nth n y)))))
    :hints(("Goal" :in-theory (enable nth)
            :induct (nth-ind n x y)))))



(local (defthm svex-env-keys-keys-no-1s-p-of-append-extract
         (implies (not (intersectp-equal (svarlist-fix vars) (svarlist-fix extvars)))
                  (equal (svex-env-keys-no-1s-p vars (append (svex-env-extract extvars other) ins))
                         (svex-env-keys-no-1s-p vars ins)))
         :hints(("Goal" :in-theory (e/d (svex-env-keys-no-1s-p
                                         svarlist-fix intersectp-equal))))))

(local (defthm svex-env-keys-keys-no-1s-p-of-step-env
         (implies (not (intersectp-equal (svarlist-fix vars) (svex-alist-keys (base-fsm->nextstate fsm))))
                  (equal (svex-env-keys-no-1s-p vars (base-fsm-step-env ins initst fsm))
                         (svex-env-keys-no-1s-p vars ins)))
         :hints(("Goal" :in-theory (enable base-fsm-step-env)))))


(local (defthm svex-override-triplelist-testvars-subset-of-vars-lemma
         (subsetp-equal (svex-override-triplelist-testvars x)
                        (svex-override-triplelist-vars x))
         :hints(("Goal" :in-theory (enable svex-override-triplelist-vars
                                           svex-override-triplelist-testvars)))))

(local (defthm svex-override-triplelist-testvars-subset-of-vars
         (implies (subsetp-equal (svex-override-triplelist-vars x) vars)
                  (subsetp-equal (svex-override-triplelist-testvars x) vars))
         :hints (("goal" :use svex-override-triplelist-testvars-subset-of-vars-lemma
                  :in-theory (disable svex-override-triplelist-testvars-subset-of-vars-lemma)))))



(local (defthm base-fsm-step-env-of-append-extract-nonstates
         (implies (and (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm))))
                       (svarlist-p vars))
                  (svex-envs-equivalent
                   (base-fsm-step-env
                    (append (svex-env-extract vars in) in2)
                    initst fsm)
                   (append (svex-env-extract vars in)
                           (base-fsm-step-env in2 initst fsm))))
         :hints(("Goal" :in-theory (enable base-fsm-step-env
                                           svex-envs-equivalent)))))

(defsection un-append-override-vars-of-base-fsm-eval*
  (local (defun un-append-override-vars-of-base-fsm-eval*-ind (triplelist prev-envs override-envs initst fsm)
           (declare (xargs :measure (len prev-envs)))
           (if (atom prev-envs)
               (list override-envs triplelist initst fsm)
             (un-append-override-vars-of-base-fsm-eval*-ind
              (cdr triplelist)
              (cdr prev-envs)
              (cdr override-envs)
              (base-fsm-step (car prev-envs) initst fsm)
              fsm))))


  

  (in-theory (disable acl2::intersectp-equal-commute))
  

  
  
  (defthm un-append-override-vars-of-base-fsm-eval*
    (b* ((vars (svex-override-triplelist-vars triples))
         (varslist (svex-override-triplelistlist-vars triplelist))
         (envs (svex-envlists-append-corresp
                (svex-envlists-extract* varslist override-envs)
                prev-envs))
         ((base-fsm fsm))
         (bad1 (svexlist-check-overridetriples (svex-alist-vals fsm.values) triples))
         (bad2 (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) triples)))
      (implies (and (not bad1)
                    (not bad2)
                    (equal (len override-envs) (len prev-envs))
                    (equal (len triplelist) (len prev-envs))
                    (svex-envlist-keys-no-1s*-p
                     (svex-override-triplelistlist-testvars triplelist)
                     prev-envs)
                    (svex-override-triple-subsetlist-p triplelist triples)
                    (no-duplicatesp-equal vars)
                    (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm))))
                    (svex-override-triplelist-fsm-inputs-ok* triplelist envs prev-envs initst fsm))
               (equal (base-fsm-eval envs initst fsm)
                      (base-fsm-eval prev-envs initst fsm))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      svex-override-triplelist-fsm-inputs-ok*
                                      svex-override-triplelistlist-vars
                                      svex-override-triplelistlist-testvars
                                      svex-envlist-removekeys*
                                      base-fsm-step
                                      base-fsm-step-outs
                                      svex-override-triple-subsetlist-p
                                      svexlist-check-overridetriples-when-subset
                                      not-intersectp-when-subsetp
                                      len)
            :expand ((:free (vars) (svex-envlists-extract* vars override-envs))
                     (:free (envs1) (svex-envlists-append-corresp envs1 prev-envs))
                     (:free (vars) (svex-envlist-keys-no-1s*-p vars prev-envs))
                     (:free (envs) (base-fsm-eval envs initst fsm))
                     (:free (x) (svex-env-extract nil x)))
            :induct (un-append-override-vars-of-base-fsm-eval*-ind
                     triplelist prev-envs override-envs initst fsm)))))


(define svex-envlists-agree-except ((vars svarlist-list-p)
                                    (x svex-envlist-p)
                                    (y svex-envlist-p))
  :measure (+ (len x) (len y))
  (if (and (atom x) (atom y))
      t
    (and (svex-envs-agree-except (car vars) (car x) (car y))
         (svex-envlists-agree-except (cdr vars) (cdr x) (cdr y))))
  ///
  (local (in-theory (enable svarlist-list-fix svex-envlist-fix))))

(defsection base-fsm-eval-of-overrides

  (local (defun base-fsm-eval-of-overrides-ind (triplelist prev-envs envs initst fsm)
           (declare (xargs :measure (len prev-envs)))
           (if (atom prev-envs)
               (list envs triplelist initst fsm)
             (base-fsm-eval-of-overrides-ind
              (cdr triplelist)
              (cdr prev-envs)
              (cdr envs)
              (base-fsm-step (car prev-envs) initst fsm)
              fsm))))

  (local (defthm svex-envs-agree-except-of-base-fsm-step-env
           (implies (and (svex-envs-agree-except vars env1 env2))
                    (svex-envs-agree-except
                     vars
                     (base-fsm-step-env env1 initst fsm)
                     (base-fsm-step-env env2 initst fsm)))
           :hints (("goal" :in-theory (enable base-fsm-step-env))
                   (and stable-under-simplificationp
                        `(:expand (,(car (last clause)))
                          :in-theory (enable svex-envs-agree-except-implies))))))

  (defthm base-fsm-eval-of-overrides
    (b* ((vars (svex-override-triplelist-vars triples))
         (varslist (svex-override-triplelistlist-vars triplelist))
         ((base-fsm fsm))
         (bad1 (svexlist-check-overridetriples (svex-alist-vals fsm.values) triples))
         (bad2 (svexlist-check-overridetriples (svex-alist-vals fsm.nextstate) triples)))
      (implies (and (svex-override-triplelist-fsm-inputs-ok* triplelist envs prev-envs initst fsm)
                    (not bad1)
                    (not bad2)
                    (equal (len envs) (len prev-envs))
                    (equal (len triplelist) (len prev-envs))
                    (svex-envlist-keys-no-1s*-p
                     (svex-override-triplelistlist-testvars triplelist)
                     prev-envs)
                    (svex-envlists-agree-except varslist envs prev-envs)
                    (svex-override-triple-subsetlist-p triplelist triples)
                    (no-duplicatesp-equal vars)
                    (not (intersectp-equal vars (svex-alist-keys (base-fsm->nextstate fsm)))))
               (equal (base-fsm-eval prev-envs initst fsm)
                      (base-fsm-eval envs initst fsm))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      svex-override-triplelist-fsm-inputs-ok*
                                      svex-override-triplelistlist-vars
                                      svex-override-triplelistlist-testvars
                                      svex-envlist-removekeys*
                                      base-fsm-step
                                      base-fsm-step-outs
                                      svex-override-triple-subsetlist-p
                                      svexlist-check-overridetriples-when-subset
                                      not-intersectp-when-subsetp
                                      svex-alist-eval-when-svexlist-check-overridetriples-and-svex-envs-agree-except-overrides
                                      len)
            :expand ((:free (vars) (svex-envlists-extract* vars override-envs))
                     (:free (envs1) (svex-envlists-append-corresp envs1 prev-envs))
                     (:free (vars) (svex-envlist-keys-no-1s*-p vars prev-envs))
                     (:free (envs) (base-fsm-eval envs initst fsm))
                     (:free (varslist) (svex-envlists-agree-except varslist envs prev-envs))
                     (:free (x) (svex-env-extract nil x)))
            :induct (base-fsm-eval-of-overrides-ind
                     triplelist prev-envs envs initst fsm)))))





(define svar-override-triples-from-signal-names ((x svarlist-p)) ;; values of the FSM
  :returns (triples svar-override-triplelist-p)
  :prepwork ()
  (if (atom x)
      nil
    (cons (make-svar-override-triple :testvar (change-svar (car x) :override-test t)
                                     :valvar (change-svar (car x) :override-val t)
                                     :refvar (car x))
          (svar-override-triples-from-signal-names (cdr x)))))



(define svar-override-triplelists-from-signal-names ((x svarlist-list-p)) ;; values of the FSM
  :returns (triples svar-override-triplelistlist-p)
  :guard-hints (("goal" :in-theory (enable append-svarlists)))
  (if (atom x)
      nil
    (cons (svar-override-triples-from-signal-names (car x))
          (svar-override-triplelists-from-signal-names (cdr x))))
  ///
  (defret len-of-<fn>
    (equal (len triples) (len x))))








(local (include-book "std/osets/element-list" :dir :system))
(local (fty::deflist svarlist :elt-type svar-p :true-listp t :elementp-of-nil nil))

;; move somewhere
(define svex-alistlist-vars ((x svex-alistlist-p))
  :returns (vars (and (svarlist-p vars)
                      (set::setp vars)))
  (if (atom x)
      nil
    (union (svex-alist-vars (car x))
           (svex-alistlist-vars (cdr x))))
  ///
  
  (defthmd svex-alistlist-eval-when-envs-agree
    (implies (not (svex-envs-disagree-witness (svex-alistlist-vars x) env1 env2))
             (equal (svex-alistlist-eval x env1)
                    (svex-alistlist-eval x env2)))
    :hints(("Goal" :in-theory (enable svex-alistlist-eval svex-alistlist-vars
                                      svex-alist-eval-when-envs-agree)))))


  

;; move somewhere

(defcong svex-envs-similar equal (svex-alistlist-eval x env) 2
  :hints(("Goal" :in-theory (enable svex-alistlist-eval)))
  :package :function)

(local
 (defthm svex-env-p-nth-of-svex-envlist-p
   (implies (svex-envlist-p x)
            (svex-env-p (nth n x)))
   :hints(("Goal" :in-theory (enable nth svex-envlist-p)))))


(define svtv-probealist/namemap-eval ((x svtv-probealist-p)
                                      (namemap svtv-name-lhs-map-p)
                                      (evals svex-envlist-p))
  :returns (eval svex-env-p)
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (cons (cons (svar-fix (caar x))
                    (b* (((svtv-probe p) (cdar x))
                         (lhs (cdr (hons-get p.signal (svtv-name-lhs-map-fix namemap)))))
                      (lhs-eval-zero lhs (nth p.time evals))))
              (svtv-probealist/namemap-eval (cdr x) namemap evals))
      (svtv-probealist/namemap-eval (cdr x) namemap evals)))
  ///
  (local (in-theory (enable svtv-probealist-fix))))



(fty::defmap svtv-rev-probealist :key-type svtv-probe :val-type svar :true-listp t)



(define svtv-pipeline-cycle-extract-override-triples ((namemap svtv-name-lhs-map-p)
                                                      (inputs svex-alist-p)
                                                      (overrides svex-alist-p)
                                                      (rev-probes svtv-rev-probealist-p)
                                                      (cycle natp))
  :returns (mv (triples svar-override-triplelist-p
                        "In the pipeline namespace -- NOT the namemap or FSM namespaces.")
               (vars svarlist-p
                     "In the FSM namespace; may contain duplicates."))
  (b* (((when (atom namemap)) (mv nil nil))
       ((unless (mbt (and (consp (car namemap))
                          (svar-p (caar namemap)))))
        (svtv-pipeline-cycle-extract-override-triples (cdr namemap) inputs overrides rev-probes cycle))
       ((cons signame lhs) (car namemap))
       (input-look (svex-fastlookup signame inputs))
       ((unless (and input-look (svex-case input-look :var)))
        (svtv-pipeline-cycle-extract-override-triples (cdr namemap) inputs overrides rev-probes cycle))
       (override-look (svex-fastlookup signame overrides))
       ((unless (and override-look (svex-case override-look :var)))
        (svtv-pipeline-cycle-extract-override-triples (cdr namemap) inputs overrides rev-probes cycle))
       (probe-look (hons-get (make-svtv-probe :signal signame :time cycle) rev-probes))
       ((unless probe-look)
        (svtv-pipeline-cycle-extract-override-triples (cdr namemap) inputs overrides rev-probes cycle))
       ((mv rest-triples rest-vars)
        (svtv-pipeline-cycle-extract-override-triples (cdr namemap) inputs overrides rev-probes cycle)))
    (mv (cons (make-svar-override-triple :testvar (svex-var->name override-look)
                                         :valvar (svex-var->name input-look)
                                         :refvar (cdr probe-look))
              rest-triples)
        (append (lhs-vars lhs) rest-vars)))
  ///
  (local (in-theory (enable svtv-name-lhs-map-fix))))

(define svtv-pipeline-extract-override-triples ((namemap svtv-name-lhs-map-p)
                                                (inputs svex-alistlist-p)
                                                (overrides svex-alistlist-p)
                                                (rev-probes svtv-rev-probealist-p)
                                                (cycle natp))
  :measure (+ (len inputs) (len overrides))
  :returns (mv (triples svar-override-triplelist-p
                        "In the pipeline namespace -- NOT the namemap or FSM namespaces.")
               (vars svarlist-list-p
                     "In the FSM namespace, and listed by cycle."))
  :prepwork ((local (defthm svar-override-triplelist-p-implies-true-listp
                      (implies (svar-override-triplelist-p x)
                               (true-listp x)))))
  (b* (((when (and (atom inputs) (atom overrides))) (mv nil nil))
       ((mv rest-triples rest-vars)
        (svtv-pipeline-extract-override-triples
         namemap (cdr inputs) (cdr overrides) rev-probes (1+ (lnfix cycle))))
       (in (car inputs))
       (ov (car overrides))
       ((acl2::with-fast in ov))
       ((mv first-triples first-vars)
        (svtv-pipeline-cycle-extract-override-triples
         namemap in ov rev-probes cycle)))
    (mv (append first-triples rest-triples)
        (cons (mergesort first-vars) rest-vars))))






(define svtv-pipeline-override-triples-extract ((triples svar-override-triplelist-p)
                                                (ref-values svex-env-p))
  :returns (values svex-env-p)
  (if (atom triples)
      nil
    (b* (((svar-override-triple trip) (car triples))
         ((unless (svex-env-boundp trip.refvar ref-values))
          (svtv-pipeline-override-triples-extract (cdr triples) ref-values)))
      (cons (cons trip.valvar (svex-env-lookup trip.refvar ref-values))
            (svtv-pipeline-override-triples-extract (cdr triples) ref-values))))
  ///
  (local (defthm svex-env-boundp-of-cons-2
           (equal (svex-env-boundp key (cons pair rest))
                  (if (and (consp pair) (equal (svar-fix key) (car pair)))
                      t
                    (svex-env-boundp key rest)))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))
  (local (defthm svex-env-lookup-of-cons2
           (equal (svex-env-lookup v (cons x y))
                  (if (and (consp x)
                           (svar-p (car x))
                           (equal (car x) (svar-fix v)))
                      (4vec-fix (cdr x))
                    (svex-env-lookup v y)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
  
  (defcong svex-envs-equivalent svex-envs-equivalent (svtv-pipeline-override-triples-extract triples ref-values) 2
    :hints (("goal" :induct (svtv-pipeline-override-triples-extract triples ref-values))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable svex-env-boundp-of-cons-2
                                      svex-env-lookup-of-cons2))))
    :package :function)
  
  (defret keys-of-<fn>-strict
    (implies (subsetp-equal (svar-override-triplelist->refvars triples)
                            (alist-keys (svex-env-fix ref-values)))
             (equal (alist-keys values) (svar-override-triplelist->valvars triples)))
    :hints(("Goal" :in-theory (enable alist-keys
                                      svar-override-triplelist->valvars
                                      svar-override-triplelist->refvars
                                      svex-env-boundp)))))


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
            :induct (nth n envs)))))



(define svtv-pipeline-override-triples-extract-values ((triples svar-override-triplelist-p)
                                                       (probes svtv-probealist-p)
                                                       (namemap svtv-name-lhs-map-p)
                                                       (evals svex-envlist-p))
  :returns (values svex-env-p)
  (b* (((when (atom triples)) nil)
       ((svar-override-triple trip) (car triples))
       (probe-look (hons-get trip.refvar (svtv-probealist-fix probes)))
       ((unless probe-look)
        (svtv-pipeline-override-triples-extract-values (cdr triples) probes namemap evals))
       ((svtv-probe probe) (cdr probe-look))
       (lhs-look (hons-get probe.signal (svtv-name-lhs-map-fix namemap)))
       ;; ((unless lhs-look)
       ;;  (svtv-pipeline-override-triples-extract-values (cdr triples) probes namemap evals))
       (eval (if lhs-look
                 (lhs-eval-zero (cdr lhs-look) (nth probe.time evals))
               (4vec-x))))
    (cons (cons trip.valvar eval)
          (svtv-pipeline-override-triples-extract-values (cdr triples) probes namemap evals)))
  ///
  (local (Defthm svex-env-lookup-of-svtv-name-lhs-map-eval
           (equal (svex-env-lookup key (svtv-name-lhs-map-eval namemap env))
                  (b* ((look (hons-assoc-equal (svar-fix key) namemap)))
                    (if look
                        (lhs-eval-zero (cdr look) env)
                      (4vec-x))))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval
                                             svtv-name-lhs-map-fix
                                             svex-env-lookup-of-cons)))))

  (local (defthm svex-env-boundp-of-cons-2
           (equal (svex-env-boundp key (cons pair rest))
                  (if (and (consp pair) (equal (svar-fix key) (car pair)))
                      t
                    (svex-env-boundp key rest)))
           :hints(("Goal" :in-theory (enable svex-env-boundp)))))
  
  (local (Defthm svex-env-boundp-of-svtv-name-lhs-map-eval
           (iff (svex-env-boundp var (svtv-name-lhs-map-eval namemap env))
                (hons-get (svar-fix var) (svtv-name-lhs-map-fix namemap)))
           :hints(("Goal" :in-theory (enable svtv-name-lhs-map-eval
                                             svtv-name-lhs-map-fix)))))

  (local (defthm len-of-svtv-probealist-outvars-gte-time
           (implies (and (hons-assoc-equal var (svtv-probealist-fix probes)))
                    (< (svtv-probe->time (cdr (hons-assoc-equal var (svtv-probealist-fix probes))))
                       (len (svtv-probealist-outvars probes))))
           :hints(("Goal" :in-theory (enable svtv-probealist-outvars
                                             svtv-probealist-fix)))
           :rule-classes :linear))
  
  (defret <fn>-in-terms-of-svtv-probealist-extract
    (implies (<= (len (svtv-probealist-outvars probes)) (len evals))
             (equal values
                    (svtv-pipeline-override-triples-extract
                     triples (svtv-probealist-extract
                              probes (svtv-name-lhs-map-eval-list namemap evals)))))
    :hints(("Goal" :in-theory (enable svtv-pipeline-override-triples-extract)
            :induct <call>)))

  (local
   (defretd keys-of-<fn>-lemma
     (subsetp-equal (alist-keys values) (svar-override-triplelist->valvars triples))
     :hints(("Goal" :in-theory (enable alist-keys)))))

  (defret keys-of-<fn>
    (implies (subsetp-equal (svar-override-triplelist->valvars triples) vars)
             (subsetp-equal (alist-keys values) vars))
    :hints (("goal" :use keys-of-<fn>-lemma)))

  
  (local (defthm hons-assoc-equal-member-alist-keys
           (iff (hons-assoc-equal k x)
                (member-equal k (alist-keys x)))
           :hints(("Goal" :in-theory (enable alist-keys)))))
  
  (defret keys-of-<fn>-strict
    (implies (subsetp-equal (svar-override-triplelist->refvars triples)
                            (alist-keys (svtv-probealist-fix probes)))
             (equal (alist-keys values) (svar-override-triplelist->valvars triples)))
    :hints(("Goal" :in-theory (enable alist-keys
                                      svar-override-triplelist->valvars
                                      svar-override-triplelist->refvars))))

  (local (defthm nth-out-of-bounds
           (implies (<= (len x) (nfix n))
                    (equal (nth n x) nil)))))



(defconst *overrides-crux-thm-template*
  '(encapsulate nil

     (make-event
      (if (fgetprop 'logand-mask-out-notnice 'acl2::untranslated-theorem nil (w state))
          (value '(value-triple :ok))
        (mv "~%Include-book \"centaur/sv/svtv/svtv-fsm-override-fgl-theory\" :dir :system before trying to run this event"
            nil state)))
     
     ;; just a heuristic, should at least allow user override
     (defconsts (*<name>-pipeline-override-triples* *<name>-fsm-cycle-override-signals*)
       (b* ((namemap (make-fast-alist (svtv-data-obj->namemap (<export>))))
            ((sv::pipeline-setup pipe) (svtv-data-obj->pipeline-setup (<export>)))
            (rev-probes (make-fast-alist (pairlis$ (alist-vals pipe.probes) (alist-keys pipe.probes))))
            ((mv triples signals)
             (svtv-pipeline-extract-override-triples
              namemap pipe.inputs  pipe.overrides rev-probes 0)))
         (fast-alist-free rev-probes)
         (mv triples signals)))

     (make-event
      `(defund <name>-pipeline-override-triples ()
         (declare (Xargs :guard t))
         ',*<name>-pipeline-override-triples*))

     (make-event
      `(defund <name>-fsm-cycle-override-signals ()
         (declare (Xargs :guard t))
         ',*<name>-fsm-cycle-override-signals*))
    
    
     (local
      (fgl::def-fgl-thm <name>-override-crux-lemma
        (b* ((namemap (make-fast-alist (svtv-data-obj->namemap (<export>))))
             ((sv::pipeline-setup pipe) (svtv-data-obj->pipeline-setup (<export>)))
             (fsm-triples (sv::svar-override-triplelists-from-signal-names
                           (<name>-fsm-cycle-override-signals)))
             (fsm (svtv-data-obj->cycle-fsm (<export>)))
             (rename-fsm (sv::make-svtv-fsm :base-fsm fsm :namemap namemap))
             (outvars (sv::svtv-probealist-outvars pipe.probes))
             (substs (sv::svtv-fsm-run-input-substs
                      (take (len outvars) pipe.inputs)
                      pipe.overrides rename-fsm)))
          (implies (equal (len spec-eval) (len outvars))
                   (b* ((spec-result (make-fast-alist
                                      (sv::svtv-pipeline-override-triples-extract-values
                                       (<name>-pipeline-override-triples)
                                       (make-fast-alist pipe.probes)
                                       namemap spec-eval)))
                        (user-env (sv::svex-env-append spec-result rest-env))
                        (final-envs
                         (sv::svex-alistlist-eval substs user-env)))
                     (sv::svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                      0 fsm-triples final-envs spec-eval))))))
     
     (defthm <name>-override-crux
       (b* ((namemap (make-fast-alist (svtv-data-obj->namemap (<export>))))
            ((sv::pipeline-setup pipe) (svtv-data-obj->pipeline-setup (<export>)))
            (fsm-triples (sv::svar-override-triplelists-from-signal-names
                          (<name>-fsm-cycle-override-signals)))
            (fsm (svtv-data-obj->cycle-fsm (<export>)))
            (rename-fsm (sv::make-svtv-fsm :base-fsm fsm :namemap namemap))
            (outvars (sv::svtv-probealist-outvars pipe.probes))
            (substs (sv::svtv-fsm-run-input-substs
                     (take (len outvars) pipe.inputs)
                     pipe.overrides rename-fsm)))
         (implies (and (equal (len spec-eval) (len outvars))
                       (not (sv::svex-envs-disagree-witness
                             (svar-override-triplelist->valvars
                              (<name>-pipeline-override-triples))
                             (sv::svtv-pipeline-override-triples-extract-values
                              (<name>-pipeline-override-triples)
                              pipe.probes namemap spec-eval)
                             user-env)))
                  (b* ((final-envs
                        (sv::svex-alistlist-eval substs user-env)))
                    (sv::svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                     0 fsm-triples final-envs spec-eval))))
       :hints (("goal" :use ((:instance <name>-override-crux-lemma
                              (rest-env user-env)))
                :in-theory
                '((:CONGRUENCE SVEX-ENVS-SIMILAR-IMPLIES-EQUAL-SVEX-ALISTLIST-EVAL-2)
                  (:DEFINITION MAKE-FAST-ALIST)
                  (:DEFINITION NOT)
                  (:EXECUTABLE-COUNTERPART SVAR-OVERRIDE-TRIPLELISTS-FROM-SIGNAL-NAMES)
                  (:REWRITE EVAL-OF-SVTV-FSM-RUN-INPUT-SUBSTS)
                  (:REWRITE svex-envs-similar-of-append-when-agree-on-keys-superset)
                  (:TYPE-PRESCRIPTION SVAR-OVERRIDE-TRIPLELIST-FSM-INPUTS-OK*-OF-FSM-EVAL)
                  (:REWRITE KEYS-OF-SVTV-PIPELINE-OVERRIDE-TRIPLES-EXTRACT-VALUES)
                  (:REWRITE SUBSETP-OF-SVAR-OVERRIDE-TRIPLELIST->VALVARS-WHEN-SUBSETP)
                  (:REWRITE ACL2::SUBSETP-REFL)
                  (:REWRITE SVARLIST-FIX-WHEN-SVARLIST-P)
                  (:REWRITE SVARLIST-P-OF-SVAR-OVERRIDE-TRIPLELIST->VALVARS)
                  (:REWRITE SVEX-ENV-FIX-WHEN-SVEX-ENV-P)
                  (:REWRITE SVEX-ENV-P-OF-SVTV-PIPELINE-OVERRIDE-TRIPLES-EXTRACT-VALUES)))))))

(defmacro def-overrides-crux-thm (name export-name &key pkg-sym)
  (acl2::template-subst *overrides-crux-thm-template*
                        :atom-alist `((<export> . ,export-name))
                        :str-alist `(("<EXPORT>" . ,(symbol-name export-name))
                                     ("<NAME>" . ,(symbol-name name)))
                        :pkg-sym (or pkg-sym name)))
                        










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


(defthmd intersectp-svex-alist-keys-by-hons-intersect-p1
  (iff (acl2::hons-intersect-p1 x (svex-alist-fix y))
       (intersectp-equal x (svex-alist-keys y)))
  :hints(("Goal" :in-theory (enable intersectp-equal acl2::hons-intersect-p1 svex-lookup))))

(defthmd subsetp-svex-alist-keys-by-hons-subset1
  (iff (acl2::hons-subset1 x (svex-alist-fix y))
       (subsetp-equal x (svex-alist-keys y)))
  :hints(("Goal" :in-theory (enable subsetp-equal acl2::hons-subset1 svex-lookup))))


(local (defthmd hons-assoc-equal-member-alist-keys
         (iff (hons-assoc-equal k x)
              (member-equal k (alist-keys x)))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(defthmd hons-subset1-is-subsetp-alist-keys
  (iff (acl2::hons-subset1 x y)
       (subsetp-equal x (alist-keys y)))
  :hints(("Goal" :in-theory (enable acl2::hons-subset1 subsetp-equal alist-keys
                                    hons-assoc-equal-member-alist-keys))))



(defcong svex-envs-similar equal (svex-envs-disagree-witness vars x y) 2
  :hints(("Goal" :in-theory (enable svex-envs-disagree-witness))))

(defcong svex-envs-similar equal (svex-envs-disagree-witness vars x y) 3
  :hints(("Goal" :in-theory (enable svex-envs-disagree-witness))))


(defthm base-fsm-final-state-of-svtv-fsm->renamed-fsm
  (equal (base-fsm-final-state ins initst (svtv-fsm->renamed-fsm fsm))
         (base-fsm-final-state ins initst (svtv-fsm->base-fsm fsm)))
  :hints(("Goal" :in-theory (enable base-fsm-final-state
                                    svtv-fsm->renamed-fsm
                                    base-fsm-step
                                    base-fsm-step-env))))

(defthm base-fsm-step-outs-of-svtv-fsm->renamed-fsm
  (equal (base-fsm-step-outs in prev-st (svtv-fsm->renamed-fsm fsm))
         (svtv-name-lhs-map-eval
          (svtv-fsm->namemap fsm)
          (append (base-fsm-step-outs in prev-st (svtv-fsm->base-fsm fsm))
                  (base-fsm-step-env in prev-st (svtv-fsm->base-fsm fsm)))))
  :hints(("Goal" :in-theory (enable base-fsm-step-outs
                                    svtv-fsm->renamed-fsm
                                    base-fsm-step-env))))





(defthmd base-fsm->nextstate-of-svtv-fsm->renamed-fsm
  (equal (base-fsm->nextstate (svtv-fsm->renamed-fsm svtv-fsm))
         (base-fsm->nextstate (svtv-fsm->base-fsm svtv-fsm)))
  :hints(("Goal" :in-theory (enable svtv-fsm->renamed-fsm))))

(define base-fsm-eval-envs ((ins svex-envlist-p)
                            (prev-st svex-env-p)
                            (x base-fsm-p))
  :guard (and (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate x))))
              (equal (alist-keys prev-st)
                     (svex-alist-keys (base-fsm->nextstate x))))
  (b* (((when (Atom ins)) nil))
    (cons (base-fsm-step-env (car ins) prev-st x)
          (base-fsm-eval-envs (cdr ins)
                              (base-fsm-step (car ins) prev-st x)
                              x)))
  ///
  (defthmd base-fsm-eval-of-svtv-fsm->renamed-fsm
    (equal (base-fsm-eval ins prev-st (svtv-fsm->renamed-fsm x))
           (svtv-name-lhs-map-eval-list
            (svtv-fsm->namemap x)
            (svex-envlists-append-corresp
             (base-fsm-eval ins prev-st (svtv-fsm->base-fsm x))
             (base-fsm-eval-envs ins prev-st (svtv-fsm->base-fsm x)))))
    :hints(("Goal" :in-theory (enable base-fsm-eval
                                      base-fsm-step
                                      base-fsm-step-env
                                      svex-envlists-append-corresp
                                      svtv-name-lhs-map-eval-list
                                      base-fsm->nextstate-of-svtv-fsm->renamed-fsm)
            :induct (base-fsm-eval ins prev-st (svtv-fsm->base-fsm x))
            :expand ((:free (x) (base-fsm-eval ins prev-st x))
                     (base-fsm-eval-envs ins prev-st (svtv-fsm->base-fsm x)))))))



(define svar-override-triplelistlist->all-refvars ((x svar-override-triplelistlist-p))
  :returns (refvars svarlist-p)
  (if (atom x)
      nil
    (append (svar-override-triplelist->refvars (car x))
            (svar-override-triplelistlist->all-refvars (cdr x)))))

(define svar-override-triplelistlist-refvars-bound-in-envs ((x svar-override-triplelistlist-p)
                                                            (envs svex-envlist-p))
  :prepwork ((local (defthm hons-subset1-is-subsetp-alist-kes
                      (iff (acl2::hons-subset1 x y)
                           (subsetp-equal x (alist-keys y)))
                      :hints(("Goal" :in-theory (enable hons-assoc-equal-member-alist-keys))))))
  :measure (len envs)
  (if (atom envs)
      t
    (and (mbe :logic (subsetp-equal (svar-override-triplelist->refvars (car x))
                                    (alist-keys (svex-env-fix (car envs))))
              :exec (acl2::hons-subset1 (svar-override-triplelist->refvars (car x))
                                        (car envs)))
         (svar-override-triplelistlist-refvars-bound-in-envs (cdr x) (cdr envs))))

  ///

  (local (defun refvars-bound-of-base-fsm-eval-ind (x ins prev-st fsm)
           (if (atom ins)
               (list x prev-st fsm)
             (refvars-bound-of-base-fsm-eval-ind (cdr x) (cdr ins)
                                                 (base-fsm-step (car ins) prev-st fsm)
                                                 fsm))))
  
  (defthm svar-override-triplelistlist-refvars-bound-in-envs-of-base-fsm-eval
    (implies (<= (len x) (len ins))
             (equal (svar-override-triplelistlist-refvars-bound-in-envs x (base-fsm-eval ins prev-st fsm))
                    (subsetp-equal (svar-override-triplelistlist->all-refvars x)
                                   (svex-alist-keys (base-fsm->values fsm)))))
    :hints(("Goal" :in-theory (enable svar-override-triplelistlist->all-refvars
                                      base-fsm-eval
                                      base-fsm-step-outs)
            :induct (refvars-bound-of-base-fsm-eval-ind x ins prev-st fsm)))))

(defthm svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval-of-append-corresp
  (implies (svar-override-triplelistlist-refvars-bound-in-envs triples (nthcdr cycle ref-envs1))
           (equal (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                   cycle triples envs (svex-envlists-append-corresp ref-envs1 ref-envs2))
                  (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                   cycle triples envs ref-envs1)))
  :hints(("Goal" :in-theory (enable svar-override-triplelistlist-refvars-bound-in-envs
                                    svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                                    svex-envlists-append-corresp
                                    acl2::and* nthcdr)
          :expand ((svar-override-triplelistlist-refvars-bound-in-envs triples (nthcdr cycle ref-envs1))
                   (:free (env ref-env) (SVAR-OVERRIDE-TRIPLELIST-ENV-OK NIL env ref-env)))
          :induct (svar-override-triplelist-fsm-inputs-ok*-of-fsm-eval
                   cycle triples envs ref-envs1))))
           



(local (defthmd alist-keys-member-hons-assoc-equal
         (iff (member-equal v (alist-keys x))
              (hons-assoc-equal v x))
         :hints(("Goal" :in-theory (enable hons-assoc-equal-member-alist-keys)))))

(defthm svex-envs-disagree-witness-of-append-when-no-intersect
  (implies (not (intersectp-equal (svarlist-fix vars) (alist-keys (svex-env-fix b))))
           (equal (svex-envs-disagree-witness vars a (append b c))
                  (svex-envs-disagree-witness vars a c)))
  :hints(("Goal" :in-theory (e/d (svex-envs-disagree-witness
                                  svex-env-boundp
                                  intersectp-equal
                                  alist-keys-member-hons-assoc-equal)
                                 (hons-assoc-equal-member-alist-keys))
          :induct t
          :expand ((svarlist-fix vars)))))

(defthm svex-envs-disagree-witness-of-append-when-subset
  (implies (subsetp-equal (svarlist-fix vars) (alist-keys (svex-env-fix b)))
           (equal (svex-envs-disagree-witness vars a (append b c))
                  (svex-envs-disagree-witness vars a b)))
  :hints(("Goal" :in-theory (e/d (svex-envs-disagree-witness
                                  svex-env-boundp
                                  intersectp-equal
                                  alist-keys-member-hons-assoc-equal)
                                 (hons-assoc-equal-member-alist-keys))
          :induct t
          :expand ((svarlist-fix vars)))))


(defthm alist-keys-of-svtv-probealist-extract
  (equal (alist-keys (svtv-probealist-extract probes vals))
         (alist-keys (svtv-probealist-fix probes)))
  :hints(("Goal" :in-theory (enable svtv-probealist-fix
                                    svtv-probealist-extract
                                    alist-keys))))


(defthm-svex-eval-flag
  (defthm svex-eval-of-append-first-non-intersecting
    (implies (not (intersectp-equal (svex-vars x) (alist-keys (svex-env-fix a))))
             (equal (svex-eval x (append a b))
                    (svex-eval x b)))
    :hints ('(:expand ((:free (env) (svex-eval x env))
                       (svex-vars x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-boundp))))
    :flag expr)
  (defthm svexlist-eval-of-append-first-non-intersecting
    (implies (not (intersectp-equal (svexlist-vars x) (alist-keys (svex-env-fix a))))
             (equal (svexlist-eval x (append a b))
                    (svexlist-eval x b)))
    :hints ('(:expand ((:free (env) (svexlist-eval x env))
                       (svexlist-vars x))))
    :flag list))

(defthm svex-alist-eval-of-append-first-non-intersecting
  (implies (not (intersectp-equal (svex-alist-vars x) (alist-keys (svex-env-fix a))))
           (equal (svex-alist-eval x (append a b))
                  (svex-alist-eval x b)))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars))))

(defthm-svex-eval-flag
  (defthm svex-eval-of-append-superset
    (implies (subsetp-equal (svex-vars x) (alist-keys (svex-env-fix a)))
             (equal (svex-eval x (append a b))
                    (svex-eval x a)))
    :hints ('(:expand ((:free (env) (svex-eval x env))
                       (svex-vars x)))
            (and stable-under-simplificationp
                 '(:in-theory (enable svex-env-boundp))))
    :flag expr)
  (defthm svexlist-eval-of-append-superset
    (implies (subsetp-equal (svexlist-vars x) (alist-keys (svex-env-fix a)))
             (equal (svexlist-eval x (append a b))
                    (svexlist-eval x a)))
    :hints ('(:expand ((:free (env) (svexlist-eval x env))
                       (svexlist-vars x))))
    :flag list))


(defthm svex-alist-eval-of-append-superset
  (implies (subsetp-equal (svex-alist-vars x) (alist-keys (svex-env-fix a)))
           (equal (svex-alist-eval x (append a b))
                  (svex-alist-eval x a)))
  :hints(("Goal" :in-theory (enable svex-alist-eval
                                    svex-alist-vars))))





































;;; -----------------------------------------------------
;;; All the rest of this is maybe unnecessary


















;; Svex-override-triplelist-fsm-inputs-ok* will be true if, for the set portion
;; of each override test variable, the corresponding override value variable is
;; set to the signal's current value.

(local (defthm cdr-hons-assoc-when-svex-alist-p
         (implies (svex-alist-p x)
                  (iff (cdr (hons-assoc-equal k x))
                       (hons-assoc-equal k x)))))
(local (defthm hons-subset1-of-svex-alist
         (implies (and (svex-alist-p y)
                       (svarlist-p x))
                  (equal (acl2::hons-subset1 x y)
                         (subsetp-equal x (svex-alist-keys y))))
         :hints(("Goal" :in-theory (enable acl2::hons-subset1
                                           subsetp-equal
                                           svex-lookup)))))

(local (defthmd member-alist-keys
         (iff (member-equal v (alist-keys x))
              (hons-assoc-equal v x))
         :hints(("Goal" :in-theory (enable alist-keys)))))

(local (defthmd hons-subset1-is-alist-keys
         (equal (acl2::hons-subset1 x y)
                (subsetp-equal x (alist-keys y)))
         :hints(("Goal" :in-theory (enable acl2::hons-subset1
                                           subsetp-equal
                                           member-alist-keys
                                           alist-keys)))))


(define svex-override-triples-from-signal-names ((x svarlist-p)
                                                 (values svex-alist-p)) ;; values of the FSM
  :returns (triples svex-override-triplelist-p)
  :guard (mbe :logic (subsetp-equal x (svex-alist-keys values))
              :exec (acl2::hons-subset1 x values))
  :prepwork ()
  (if (atom x)
      nil
    (cons (make-svex-override-triple :testvar (change-svar (car x) :override-test t)
                                     :valvar (change-svar (car x) :override-val t)
                                     :valexpr (svex-fastlookup (car x) values))
          (svex-override-triples-from-signal-names (cdr x) values))))



(define svex-override-triplelists-from-signal-names ((x svarlist-list-p)
                                                     (values svex-alist-p)) ;; values of the FSM
  :returns (triples svex-override-triplelistlist-p)
  :guard (mbe :logic (subsetp-equal (append-svarlists x) (svex-alist-keys values))
              :exec (acl2::hons-subset1 (append-svarlists x) values))
  :guard-hints (("goal" :in-theory (enable append-svarlists)))
  (if (atom x)
      nil
    (cons (svex-override-triples-from-signal-names (car x) values)
          (svex-override-triplelists-from-signal-names (cdr x) values))))






;; One way of creating an env with correct overrides -- append this to the original env.
(define svex-alist-collect-override-env ((test-env svex-env-p) ;; Maps variables to their override test values
                                         (eval-result-env svex-env-p))
  ;; :guard  (mbe :logic (subsetp-equal (alist-keys test-env) (alist-keys eval-result-env))
  ;;              :exec (acl2::hons-subset1 (alist-keys test-env) eval-result-env))
  ;; :guard-hints (("goal" :in-theory (enable alist-keys hons-subset1-is-alist-keys)))
  :returns (override-env svex-env-p)
  (if (atom test-env)
      nil
    (if (mbt (and (consp (car test-env))
                  (svar-p (caar test-env))))
        (b* (((cons var testval) (car test-env))
             (testval (4vec-fix testval)))
          (cons (cons (change-svar var :override-test t) testval)
                (cons (cons (change-svar var :override-val t)
                            ;; could be 4vec-bit?! masked with the testval
                            (svex-env-lookup var eval-result-env))
                      (svex-alist-collect-override-env (cdr test-env) eval-result-env))))
      (svex-alist-collect-override-env (cdr test-env) eval-result-env)))
  ///
  (defret lookup-override-test-in-<fn>
    (implies (and (svarlist-non-override-p (alist-keys (svex-env-fix test-env)))
                  (svar->override-test var))
             (and (equal (svex-env-boundp var override-env)
                         (svex-env-boundp (change-svar var :override-test nil) test-env))
                  (equal (svex-env-lookup var override-env)
                         (svex-env-lookup (change-svar var :override-test nil) test-env))))
    :hints(("Goal" :in-theory (enable svarlist-non-override-p
                                      svex-env-boundp
                                      svex-env-lookup
                                      svex-env-fix
                                      alist-keys))))
  
  (local (defthm change-svar-when-not-test/val
           (implies (and (not (svar->override-test x))
                         (not (svar->override-val x)))
                    (equal (change-svar x :override-test nil :override-val nil)
                           (svar-fix x)))
           :hints (("goal" :in-theory (enable svar-fix-redef)))))
  
  (defret lookup-override-val-in-<fn>
    (implies (and (svarlist-non-override-p (alist-keys (svex-env-fix test-env)))
                  (svar->override-val var)
                  (not (svar->override-test var)))
             (and (equal (svex-env-boundp var override-env)
                         (svex-env-boundp (change-svar var :override-val nil) test-env))
                  (equal (svex-env-lookup var override-env)
                         (if (svex-env-boundp (change-svar var :override-val nil) test-env)
                             (svex-env-lookup (change-svar var :override-val nil) eval-result-env)
                           (4vec-x)))))
    :hints(("Goal" :in-theory (enable svarlist-non-override-p
                                      svex-env-boundp
                                      svex-env-lookup
                                      svex-env-fix
                                      alist-keys))))
  
  (local (defthm svex-override->test-and-val-when-member
           (implies (and (svarlist-non-override-p x)
                         (member-equal (svar-fix v) (svarlist-fix x)))
                    (and (not (svar->override-test v))
                         (not (svar->override-val v))))
           :hints(("Goal" :in-theory (enable svarlist-non-override-p)))))

  
  
  (defret svex-override-triplelist-env-ok-of-<fn>
    :pre-bind ((eval-result-env (svex-alist-eval values eval-env)))
    (implies (and (subsetp-equal (alist-keys (svex-env-fix test-env)) (svex-alist-keys values))
                  (subsetp-equal (svarlist-fix signals) (alist-keys (svex-env-fix test-env)))
                  ;; (no-duplicatesp-equal (alist-keys (svex-env-fix test-env)))
                  (svarlist-non-override-p (alist-keys (svex-env-fix test-env))))
             (svex-override-triplelist-env-ok (svex-override-triples-from-signal-names signals values)
                                              (append override-env any-env)
                                              eval-env))
    :hints(("Goal" :in-theory (e/d (svex-override-triples-from-signal-names
                                      svex-override-triplelist-env-ok
                                      subsetp-equal
                                      svarlist-fix
                                      svarlist-non-override-p)
                                   (<fn>))
            :induct (svex-override-triples-from-signal-names signals values))))


  (defret svex-env-removekeys-of-<fn>
    (equal (svex-env-removekeys (svex-override-triplelist-vars
                                 (svex-override-triples-from-signal-names
                                  (alist-keys (svex-env-fix test-env))
                                  any-values))
                                override-env)
           nil)
    :hints(("Goal" :in-theory (enable svex-env-removekeys
                                      svex-env-fix
                                      alist-keys
                                      svex-override-triplelist-vars
                                      svex-override-triples-from-signal-names))))
  
  (local (in-theory (enable svex-env-fix))))


(define append-corresp-svex-envs ((envs1 svex-envlist-p)
                                  (envs2 svex-envlist-p))
  :returns (appended svex-envlist-p)
  :measure (+ (len envs1) (len envs2))
  (if (and (atom envs1) (atom envs2))
      nil
    (cons (append (svex-env-fix (car envs1))
                  (svex-env-fix (car envs2)))
          (append-corresp-svex-envs (cdr envs1) (cdr envs2)))))


(define svex-envlist-all-keys ((x svex-envlist-p))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (append (alist-keys (svex-env-fix (car x)))
            (svex-envlist-all-keys (cdr x)))))

(define svex-envlist-keys-list ((x svex-envlist-p))
  :returns (vars svarlist-list-p)
  (if (atom x)
      nil
    (cons (alist-keys (svex-env-fix (car x)))
          (svex-envlist-keys-list (cdr x)))))

;; Similarly, one way of creating an envlist with correct overrides for base-fsm-eval -- append these to the original input envs.

(define base-fsm-collect-override-envs ((test-envs svex-envlist-p) ;; maps variables for each cycle to their override tests
                                        (eval-ins svex-envlist-p)
                                        (prev-st svex-env-p)
                                        (fsm base-fsm-p))
  :guard  (and (mbe :logic (subsetp-equal (svex-envlist-all-keys test-envs) (svex-alist-keys (base-fsm->values fsm)))
                    :exec (acl2::hons-subset1 (svex-envlist-all-keys test-envs) (base-fsm->values fsm)))
               (equal (alist-keys prev-st) (svex-alist-keys (base-fsm->nextstate fsm)))
               (not (acl2::hons-dups-p (svex-alist-keys (base-fsm->nextstate fsm)))))
  :guard-hints (("goal" :in-theory (enable svex-envlist-all-keys)))
  :returns (override-envs svex-envlist-p)
  (if (atom eval-ins)
      nil
    (cons (svex-alist-collect-override-env
           (car test-envs)
           (base-fsm-step-outs (car eval-ins) prev-st fsm))
          (base-fsm-collect-override-envs
           (cdr test-envs)
           (cdr eval-ins)
           (base-fsm-step (car eval-ins) prev-st fsm)
           fsm)))
  ///

  (local (defun base-fsm-collect-override-envs-env-ind (test-envs eval-ins prev-st fsm other-ins)
           (if (Atom eval-ins)
               (list test-envs  prev-st other-ins)
             (base-fsm-collect-override-envs-env-ind
              (cdr test-envs)
              (cdr eval-ins)
              (base-fsm-step (car eval-ins) prev-st fsm)
              fsm
              (cdr other-ins)))))

  (local (defthm svex-env-lookup-of-cons2
           (equal (svex-env-lookup v (cons x y))
                  (if (and (consp x)
                           (svar-p (car x))
                           (equal (car x) (svar-fix v)))
                      (4vec-fix (cdr x))
                    (svex-env-lookup v y)))
           :hints(("Goal" :in-theory (enable svex-env-lookup)))))
  
  (local (defcong svex-envs-similar svex-envs-similar (cons x y) 2
           :hints ((and stable-under-simplificationp
                        `(:expand (,(car (last clause))))))))

  (local (defthm svex-envs-similar-append-cons
           (implies (not (svex-env-boundp (car y) x))
                    (svex-envs-similar (append x (cons y z))
                                       (cons y (append x z))))
           :hints(("Goal" :in-theory (enable svex-envs-similar)))))

  (local (defthm svex-env-boundp-when-keys-non-override-p
           (implies (and (svarlist-non-override-p (alist-keys (svex-env-fix env)))
                         (or (svar->override-test x)
                             (svar->override-val x)))
                    (not (svex-env-boundp x env)))
           :hints(("Goal" :in-theory (enable svex-env-fix svex-env-boundp svarlist-non-override-p alist-keys)))))
           
  
  (local (defthm base-fsm-step-env-of-append-override-env
           (implies (svarlist-non-override-p (svex-alist-keys (base-fsm->nextstate fsm)))
                    (svex-envs-similar
                     (base-fsm-step-env
                      (append (svex-alist-collect-override-env test-env res-env)
                              env2)
                      prev-st fsm)
                     (append (svex-alist-collect-override-env test-env res-env)
                             (base-fsm-step-env env2 prev-st fsm))))
           :hints(("Goal" :in-theory (enable base-fsm-step-env
                                             svex-alist-collect-override-env)
                   :induct (svex-alist-collect-override-env test-env res-env)))))


  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (atom x))))
  
  (defret svex-override-triplelist-fsm-inputs-ok*-of-<fn>
    (implies (and (subsetp-equal (svex-envlist-all-keys test-envs) (svex-alist-keys (base-fsm->values fsm)))
                  (svarlist-non-override-p (svex-envlist-all-keys test-envs))
                  (svarlist-non-override-p (svex-alist-keys (base-fsm->nextstate fsm)))
                  (equal (len any-envs) (len eval-ins)))
             (svex-override-triplelist-fsm-inputs-ok*
              (svex-override-triplelists-from-signal-names 
               (svex-envlist-keys-list test-envs)
               (base-fsm->values fsm))
              (append-corresp-svex-envs override-envs any-envs)
              eval-ins prev-st fsm))
    :hints(("Goal" :in-theory (enable svex-envlist-all-keys
                                      svex-envlist-keys-list
                                      svex-override-triplelist-fsm-inputs-ok*
                                      svex-override-triplelists-from-signal-names
                                      append-corresp-svex-envs
                                      base-fsm-step-outs)
            :induct (base-fsm-collect-override-envs-env-ind test-envs eval-ins prev-st fsm any-envs))))

  (defcong svex-envs-similar equal (base-fsm-collect-override-envs
                                    test-envs eval-ins prev-st fsm)
    3
    :hints(("Goal" :in-theory (enable base-fsm-step-outs
                                      base-fsm-step
                                      base-fsm-step-env)))))


;; (local
;;  (defsection nth-of-base-fsm-eval
;;    (local (defun nth-of-base-fsm-eval-ind (n ins st fsm)
;;             (if (zp n)
;;                 (list ins st fsm)
;;               (nth-of-base-fsm-eval-ind (1- n) (cdr ins)
;;                                         (base-fsm-step (car ins) st fsm)
;;                                         fsm))))

;;    (defthmd nth-of-base-fsm-eval
;;      (equal (nth n (base-fsm-eval eval-ins prev-st fsm))
;;             (base-fsm-step-outs (nth n eval-ins)
;;                                 (nth n (cons prev-st (base-fsm-eval-states eval-ins prev-st fsm)))
;;                                 fsm))
;;      :hints(("Goal" :in-theory (enable base-fsm-eval base-fsm-eval-states)
;;              :induct (nth-of-base-fsm-eval n eval-ins prev-st fsm))))))

(define base-fsm-collect-override-envs-alt ((cycle natp)
                                            (test-envs svex-envlist-p) ;; the rest of them starting with cycle
                                            (fsm-eval svex-envlist-p)
                                            ;; (eval-ins svex-envlist-p) ;; full, starting with cycle=0
                                            ;; (prev-st svex-env-p)    ;; starting with cycle=0
                                            ;; (fsm base-fsm-p)
                                            )
  :guard  (and (mbe :logic (subsetp-equal (svex-envlist-all-keys test-envs) (alist-keys fsm-eval))
                    :exec (acl2::hons-subset1 (svex-envlist-all-keys test-envs) fsm-eval))
               (<= cycle (len fsm-eval)))
  :guard-hints(("Goal" :in-theory (enable nth-of-base-fsm-eval
                                          hons-subset1-is-alist-keys
                                          svex-envlist-all-keys)))
  :measure (nfix (- (len fsm-eval) (nfix cycle)))
  :returns (override-envs svex-envlist-p)
  (if (zp (- (len fsm-eval) (nfix cycle)))
      nil
    (cons (svex-alist-collect-override-env
           (car test-envs)
           (nth cycle fsm-eval))
          (base-fsm-collect-override-envs-alt
           (+ 1 (lnfix cycle))
           (cdr test-envs)
           fsm-eval)))

  :prepwork ((defthm svex-env-p-nth-of-svex-envlist
               (implies (svex-envlist-p x)
                        (svex-env-p (nth n x)))))
  ///

  
  (defret base-fsm-collect-override-envs-alt-redef
    :pre-bind ((fsm-eval (base-fsm-eval eval-ins prev-st fsm)))
    (equal override-envs
           (base-fsm-collect-override-envs test-envs (nthcdr cycle eval-ins)
                                           (base-fsm-final-state (take cycle eval-ins) prev-st fsm)
                                           fsm))
    :hints(("Goal" :in-theory (e/d (nth-of-base-fsm-eval)
                                   (take))
            :induct (base-fsm-collect-override-envs-alt cycle test-envs eval-ins) ;; bit of a hack but it works
            :expand ((:free (eval-ins prev-st) (base-fsm-collect-override-envs test-envs eval-ins prev-st fsm))
                     (:free (fsm-eval) <call>))))))






;; For a given pipeline 
