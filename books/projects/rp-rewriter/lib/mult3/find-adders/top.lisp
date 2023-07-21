
; Multiplier verification

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

(include-book "../fnc-defs")
(include-book "centaur/svl/top" :dir :system)
(include-book "centaur/sv/svex/lists" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
(include-book "centaur/fgl/portcullis" :dir :system)

(include-book "heuristics")
(include-book "adder-patterns")
(include-book "macros")

(local
 (include-book "centaur/bitops/ihs-extensions" :dir :system))

(local
 (include-book "ihs/logops-lemmas" :dir :system))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (defthm svexlist-p-of-remove-duplicates
   (implies (sv::Svexlist-p x)
            (sv::Svexlist-p (remove-duplicates-equal x)))))

(local
 (in-theory (disable acl2::merge-sort-lexorder
                     acl2::merge-lexorder)))

(local
 (in-theory (e/d (acl2::maybe-integerp
                  sv::svex-kind)
                 ((:e tau-system)))))

(defines svex-has-bitxor-0
  (define svex-has-bitxor-0 ((x sv::svex-p))
    :measure (sv::svex-count x)
    (sv::Svex-case
     x
     :var nil
     :quote nil
     :call (case-match x
             (('sv::bitxor 0 &) t)
             (('sv::bitxor & 0) t)
             (& (svexlist-has-bitxor-0 x.args)))))
  (define svexlist-has-bitxor-0 ((lst sv::svexlist-p))
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        nil
      (or (svex-has-bitxor-0 (car lst))
          (svexlist-has-bitxor-0 (cdr lst)))))
  ///
  (memoize 'svex-has-bitxor-0))

(local
 ;; some more lemmas first.
 (defsection 4vec-lemmas

   (defthm 4vec-concat$-to-logapp
     (implies (and (natp size)
                   (integerp x)
                   (integerp y))
              (equal (svl::4vec-concat$ size x y)
                     (logapp size x y)))
     :hints (("goal"
              :in-theory (e/d (svl::4vec-concat$
                               svl::logapp-to-4vec-concat)
                              ()))))

   (defthm sv::4vec-bitops-to-logops
     (and (implies (and (integerp x)
                        (integerp y))
                   (and (equal (sv::4vec-bitxor x y)
                               (logxor x y))
                        (equal (sv::4vec-bitand x y)
                               (logand x y))
                        (equal (sv::4vec-bitor x y)
                               (logior x y))))
          (implies (integerp x)
                   (equal (sv::4vec-bitnot x)
                          (lognot x))))
     :hints (("goal"
              :do-not-induct t
              :in-theory (e/d* (sv::4vec
                                sv::4vec-bitand
                                sv::3vec-bitand
                                sv::3vec-bitor
                                sv::4vec-bitor
                                sv::3vec-bitnot
                                sv::4vec-bitnot
                                bitops::ihsext-inductions
                                bitops::ihsext-recursive-redefs
                                sv::4vec-bitxor
                                sv::4vec->lower
                                sv::4vec->upper
                                sv::4vec-rsh
                                sv::4vec-shift-core
                                svl::bits
                                sv::4vec-part-select
                                sv::4vec-concat)
                               (floor
                                svl::equal-of-4vec-concat-with-size=1
                                logand)))))

   (defthm sv::svexlist-eval$-when-consp
     (implies (consp lst)
              (equal (sv::svexlist-eval$ lst env)
                     (cons (sv::svex-eval$ (car lst) env)
                           (sv::svexlist-eval$ (cdr lst) env)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subtle: create some aux lemmas/functions to make this a meta-rule for RP-Rewriter.
(progn
  (def-formula-checks-default-evl
    rp-evl
    (list* 'apply$ 'badge-userfn 'apply$-userfn
           (strip-cars rp::*small-evl-fncs*)))

  (with-output
    :off :all :on (error comment)
    :gag-mode nil
    (rp::def-formula-checks
      find-adders-in-svex-formula-checks-small
      (binary-or binary-? binary-not binary-xor binary-and s-spec c-spec)
      :warranted-fns
      (ha-c-chain
       ha-s-chain
       fa-c-chain
       fa-s-chain
       full-adder
       half-adder
       ha+1-c-chain
       ha+1-s-chain)))

  (defun find-adders-in-svex-formula-checks (state)
    (declare (xargs :stobjs (state)))
    (and (find-adders-in-svex-formula-checks-small state)
         (svl::svex-ev-wog-formula-checks state) ;; using this here to save
         ;; certification time instead of adding all those svex-eval functions.
         )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Now functions  to search  for pattern globally  and do  more simplifications
;; etc.

;; Globally search and get rid of things like unfloat/id when possible.
(defines clear-adder-fnc-from-unfloat
  :verify-guards nil
  :prepwork
  ((define ex-adder-fnc-from-unfloat ((svex sv::Svex-p))
     :returns (res-svex sv::svex-p :hyp (sv::Svex-p svex))
     (case-match svex
       (('sv::unfloat ('id x))
        (if (and (equal (sv::svex-kind x) :call)
                 (member-equal  (sv::Svex-call->fn  x)
                                '(fa-c-chain fa-s-chain
                                             full-adder half-adder  ha+1-c-chain ha+1-s-chain
                                             ha-c-chain   ha-s-chain   sv::bitand   sv::bitor
                                             sv::bitxor)))
            (cadr svex)
          svex))
       (('sv::unfloat x)
        (if (and (equal (sv::svex-kind x) :call)
                 (member-equal  (sv::Svex-call->fn  x)
                                '(fa-c-chain fa-s-chain
                                             full-adder half-adder  ha+1-c-chain ha+1-s-chain
                                             ha-c-chain   ha-s-chain   sv::bitand   sv::bitor
                                             sv::bitxor)))
            x svex))
       (& svex))
     ///
     (defret <fn>-correct
       (implies (and (warrants-for-adder-pattern-match))
                (equal (sv::svex-eval$ res-svex env)
                       (sv::svex-eval$ svex env)))
       :hints (("Goal"
                :expand ((sv::svex-call->fn svex)
                         (sv::svex-call->args svex)
                         (sv::svex-call->fn (cadr svex))
                         (sv::svex-call->args (cadr svex))
                         (:free (args) (sv::svex-apply 'id args))
                         (:free (args) (sv::svex-apply 'sv::bitor args))
                         (:free (args) (sv::svex-apply 'sv::bitxor args))
                         (:free (args) (sv::svex-apply 'sv::bitand args))
                         (:free (args) (sv::svex-apply 'sv::unfloat args)))
                :in-theory (e/d (fa-c-chain
                                 fa-s-chain
                                 full-adder half-adder
                                 ha-c-chain ha-s-chain
                                 ha+1-s-chain ha+1-c-chain
                                 sv::svex-apply$)
                                ()))))))

  (define clear-adder-fnc-from-unfloat ((svex sv::svex-p))
    :returns (res-svex sv::svex-p :hyp (sv::svex-p svex))
    :measure (sv::Svex-count svex)
    (sv::svex-case
     svex
     :quote svex
     :var svex
     :call
     (ex-adder-fnc-from-unfloat
      (sv::Svex-call svex.fn
                     (clear-adder-fnc-from-unfloat-lst svex.args)))))
  (define clear-adder-fnc-from-unfloat-lst ((lst sv::svexlist-p))
    :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        nil
      (hons (clear-adder-fnc-from-unfloat (car lst))
            (clear-adder-fnc-from-unfloat-lst (cdr lst)))))
  ///
  (verify-guards clear-adder-fnc-from-unfloat)

  (memoize 'clear-adder-fnc-from-unfloat))

;; create an unfloat instance. This can help above
(define create-unfloat-for-adder-fnc (arg)
  :returns (res sv::Svex-p :hyp (sv::Svex-p arg))
  (case-match arg
    (('fa-c-chain & & & &)
     arg)
    (('fa-s-chain & & &)
     arg)
    (('ha+1-s-chain & & &)
     arg)
    ((fn & &)
     (if (member-equal fn
                       '(sv::bitxor sv::bitor
                                    ha-c-chain ha-s-chain ha+1-c-chain))
         arg
       (svl::svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg))))
    (&
     (svl::svex-reduce-w/-env-apply 'sv::unfloat (hons-list arg))))
  ///
  (defret <fn>-is-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-eval$ res env)
                    (sv::3vec-fix (sv::svex-eval$ arg env))))
    :hints (("Goal"
             :in-theory (e/d (ha-c-chain
                              ha-s-chain
                              ha+1-s-chain
                              ha+1-c-chain
                              fa-s-chain
                              fa-c-chain
                              sv::svex-apply
                              sv::svex-apply$
                              sv::svex-call->fn
                              sv::svex-call->args)
                             ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (defthm natp-implies-svex-p
   (implies (natp x)
            (and (sv::Svex-p x)
                 (sv::Svex-p (1- x))))
   :rule-classes (:forward-chaining)
   :hints (("Goal"
            :in-theory (e/d (sv::Svex-p) ())))))

;; For simple, quick pattern finding.

;; 1. Gather applicable patterns and create a "pattern-alist"
(acl2::defines gather-adder-patterns-in-svex
  :prepwork
  ((define register-found-adder-patterns ((pattern-fn-call-list pattern-fn-call-list-p)
                                          (pattern-alist pattern-alist-p)
                                          (column acl2::maybe-integerp))
     :returns (res pattern-alist-p :hyp (and (pattern-alist-p pattern-alist)
                                             (acl2::maybe-integerp column)))
     ;;:inline t
     ;; when a matching pattern  is found, it should be saved  in a fast-alist whose
     ;; keys are arguments, and value should be a list of all the pattern names.
     (b* (((when (atom pattern-fn-call-list)) pattern-alist)
          ((pattern-fn-call x) (car pattern-fn-call-list))

          ;;((unless (and key value)) pattern-alist)
          (entry (hons-get x.args pattern-alist))

          ;; when column is tracked, the function name is saved as a cons pair instead..
          (new-fn (if column
                      (cons x.fn
                            (if (member x.fn '(fa-c-chain ha-c-chain ha+1-c-chain))
                                (1- column)
                              column))
                    x.fn))
          (new-entry (cons new-fn (cdr entry)))
          (new-entry (if (and x.new-p (not (member :new new-entry)))
                         (list* :new new-entry)
                       new-entry))
          (key x.args)
          (pattern-alist (hons-acons key new-entry pattern-alist)))
       (register-found-adder-patterns (cdr pattern-fn-call-list)
                                      pattern-alist
                                      column))
     ///
     (defret alistp-of-<fn>
       (implies (alistp pattern-alist)
                (alistp res)))))

  :verify-guards nil

  (define gather-adder-patterns-in-svex ((x sv::svex-p)
                                         &key
                                         ((pattern-alist pattern-alist-p) 'pattern-alist)
                                         (parsed-svexes 'parsed-svexes)
                                         (adder-type 'adder-type)
                                         ((column acl2::maybe-integerp) 'column)

                                         ((env) 'env)
                                         ((context rp-term-listp) 'context)
                                         ((config svl::svex-reduce-config-p) 'config))
    :measure (sv::svex-count x)
    :returns (mv (res-pattern-alist pattern-alist-p :hyp (and (pattern-alist-p pattern-alist)
                                                              (acl2::maybe-integerp column)))
                 res-parsed-svexes)
    (sv::svex-case
     x
     :quote (mv pattern-alist parsed-svexes)
     :var   (mv pattern-alist parsed-svexes)
     :call (b* ((already-parsed (hons-get x parsed-svexes))
                ((when already-parsed) (mv pattern-alist parsed-svexes))
                (parsed-svexes (hons-acons x nil parsed-svexes))
                ;; get a list of matching patterns.
                (matching-pattern-fn-call-list (adder-pattern-match x adder-type))
                (pattern-alist
                 (register-found-adder-patterns matching-pattern-fn-call-list pattern-alist column)))
             (cond ((and column
                         (eq x.fn 'sv::concat)
                         (svl::equal-len x.args 3)
                         (natp (first x.args)))
                    (b* (((mv pattern-alist parsed-svexes)
                          (gather-adder-patterns-in-svex (second x.args))))
                      (gather-adder-patterns-in-svex (third x.args)
                                                     :column (+ column (first x.args)))))
                   (t
                    (b*  (;;  bitand and  bitor  is  likely  a part  of  carry
                          ;; logic. This will mess  up with column calculation.
                          ;; So let's  just increase  column a  lot so  it gets
                          ;; thrown away.
                          ((when (and*-exec column
                                            (member-eq x.fn '(sv::bitand sv::bitor))))
                           (mv pattern-alist parsed-svexes))

                          (column (and*-exec ;; under a known carry, move down the column..
                                   column
                                   (+ column
                                      (- (acl2::bool->bit
                                          (member-eq x.fn '(ha-c-chain fa-c-chain ha+1-c-chain))))))))
                      (gather-adder-patterns-in-svexlist x.args)))))))

  (define gather-adder-patterns-in-svexlist ((lst sv::svexlist-p)
                                             &key
                                             ((pattern-alist pattern-alist-p) 'pattern-alist)
                                             (parsed-svexes 'parsed-svexes)
                                             (adder-type 'adder-type)
                                             ((column acl2::maybe-integerp) 'column)

                                             ((env) 'env)
                                             ((context rp-term-listp) 'context)
                                             ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (res-pattern-alist pattern-alist-p :hyp (and (pattern-alist-p pattern-alist)
                                                              (acl2::maybe-integerp column)))
                 res-parsed-svexes)
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        (mv pattern-alist parsed-svexes)
      (b* (((mv pattern-alist parsed-svexes)
            (gather-adder-patterns-in-svex (car lst)))
           ((mv pattern-alist parsed-svexes)
            (gather-adder-patterns-in-svexlist (cdr lst))))
        (mv pattern-alist parsed-svexes))))
  ///

  (verify-guards gather-adder-patterns-in-svex-fn)

  (defret-mutual alistp-of-<fn>
    (defret alistp-of-<fn>
      (implies (alistp pattern-alist)
               (alistp res-pattern-alist))
      :fn gather-adder-patterns-in-svex)
    (defret alistp-of-<fn>
      (implies (alistp pattern-alist)
               (alistp res-pattern-alist))
      :fn gather-adder-patterns-in-svexlist)
    :hints (("Goal"
             :expand ((gather-adder-patterns-in-svexlist lst)
                      (gather-adder-patterns-in-svex nil)
                      (gather-adder-patterns-in-svex x))
             :in-theory (e/d () ())))))

(define gather-adder-patterns-in-svex-alist ((alist sv::svex-alist-p)
                                             &key
                                             ((pattern-alist pattern-alist-p) ''gather-adder-patterns-in-svex-alist)
                                             (parsed-svexes 'nil)
                                             (adder-type 'adder-type)
                                             (track-column? 'track-column?)
                                             ((env) 'env)
                                             ((context rp-term-listp) 'context)
                                             ((config svl::svex-reduce-config-p) 'config))
  :returns (mv (res-pattern-alist pattern-alist-p :hyp (pattern-alist-p pattern-alist))
               res-parsed-svexes)
  (if (atom alist)
      (progn$ (fast-alist-free parsed-svexes)
              (mv pattern-alist parsed-svexes))
    (b* (((mv pattern-alist parsed-svexes)
          (gather-adder-patterns-in-svex (cdar alist)
                                         :column (and track-column? 0)))
         ((mv pattern-alist parsed-svexes)
          (gather-adder-patterns-in-svex-alist (cdr alist)
                                               :pattern-alist pattern-alist
                                               :parsed-svexes parsed-svexes)))
      (mv pattern-alist parsed-svexes)))
  ///
  (defret alistp-of-<fn>
    (implies (alistp pattern-alist)
             (alistp res-pattern-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; 2. Apply patterns if their rule is satisfied (usually this means their
;; counterpart pattern is found for the same arguments.

#|(defines run-pattern-rule
:prepwork
((define andlst (lst)
(if (atom lst)
t
(and (car lst)
(andlst (cdr lst)))))
(define orlst (lst)
(if (atom lst)
nil
(or (car lst)
(orlst (cdr lst))))))
(define run-pattern-rule ((rule pseudo-termp)
(found-patterns))
(cond ((atom rule)
(cond ((equal rule 'found-patterns)
found-patterns)
((booleanp rule)
rule)
(t
(acl2::raise "Unknown atom in rule pattern is given to run-pattern-rule: ~p0. It
may need improvement.. ~%" rule))))
((and (quotep rule)
(consp (cdr rule)))
(unquote rule))
((and (equal (car rule) 'member-equal)
(equal (len (cdr rule)) 2))
(ec-call
(member-equal (run-pattern-rule (second rule) found-patterns)
(run-pattern-rule (third rule) found-patterns))))
((equal (car rule) 'and)
(andlst (run-pattern-rule-lst (cdr rule) found-patterns)))
((equal (car rule) 'or)
(orlst (run-pattern-rule-lst (cdr rule) found-patterns))))
)
(define run-pattern-rule-lst ((lst pseudo-term-listp)
(found-patterns))
(if (atom lst)
nil
(cons (run-pattern-rule (car lst) found-patterns)
(run-pattern-rule-lst (cdr lst) found-patterns)))))|#

(define run-pattern-rule ((rule symbol-listp)
                          (source.fn)
                          (found-patterns true-listp)
                          (track-column?))
  :prepwork
  ((define run-pattern-rule-aux-when-track-column (source.fn other.fn
                                                             found-patterns
                                                             (all-found-patterns true-listp))
     (if (atom found-patterns)
         nil
       (b* ((first (car found-patterns))
            (column (and (consp first) (cdr first)))
            (matched-fn? (and (consp first) (equal (car first) source.fn)))
            ((when (and matched-fn?
                        (member-equal (cons other.fn column)
                                      all-found-patterns)))
             t))
         (run-pattern-rule-aux-when-track-column
          source.fn other.fn (cdr found-patterns) all-found-patterns)))))

  (b* (((when (atom rule)) nil)
       (first-fn (car rule)))
    (or (cond ((equal first-fn t)
               t)
              (track-column?
               (run-pattern-rule-aux-when-track-column source.fn first-fn found-patterns found-patterns))
              (t (member-eq first-fn found-patterns)))
        (run-pattern-rule (cdr rule) source.fn found-patterns track-column?))))

(define pull-the-first-applicable-adder-pattern ((pattern-alist pattern-alist-p)
                                                 (pattern-fn-call-list pattern-fn-call-list-p)
                                                 (track-column?))
  :prepwork ((in-theory (e/d ()
                             (assoc-equal
                              (:e tau-system)))))
  :returns (pattern-fn-call (implies pattern-fn-call
                                     (pattern-fn-call-p pattern-fn-call))
                            :hyp (pattern-fn-call-list-p pattern-fn-call-list))
  (if (atom pattern-fn-call-list)
      nil
    (b* (((pattern-fn-call x) (car pattern-fn-call-list))
         ((when (equal x.rule '(t))) x)
         (found-patterns (cdr (hons-get x.args pattern-alist)))
         (should-rewrite (and x.rule (run-pattern-rule x.rule x.fn found-patterns track-column?)))
         ((when should-rewrite)
          (car pattern-fn-call-list)))
      (pull-the-first-applicable-adder-pattern pattern-alist
                                               (cdr pattern-fn-call-list)
                                               track-column?)))
  ///

  (defret <fn>-returns-a-member-of-pattern-fn-call-list
    (implies pattern-fn-call
             (and (member-equal pattern-fn-call pattern-fn-call-list)
                  (pattern-fn-call->rule pattern-fn-call)))))

(local
 (defthm replace-adder-patterns-in-svex-measure-lemma
   (implies
    (and (pull-the-first-applicable-adder-pattern
          pattern-alist
          (adder-pattern-match (sv::svex-fix x) adder-type)
          track-column?))
    (<
     (sv::svexlist-count
      (pattern-fn-call->args (pull-the-first-applicable-adder-pattern
                              pattern-alist
                              (adder-pattern-match (sv::svex-fix x) adder-type)
                              track-column?)))
     (sv::svex-count x)))
   :hints (("Goal"
            :use ((:instance
                   pattern-fn-call-list-provide-good-measure-p-and-member
                   (x (sv::svex-fix x))
                   (lst (adder-pattern-match (sv::svex-fix x) adder-type))
                   (e (pull-the-first-applicable-adder-pattern
                       pattern-alist
                       (adder-pattern-match (sv::svex-fix x) adder-type)
                       track-column?)))

                  (:instance adder-pattern-match-good-measure
                             (svex (sv::svex-fix x))))
            :in-theory (e/d (pattern-fn-call-provide-good-measure-p)
                            (pattern-fn-call-list-provide-good-measure-p-and-member
                             adder-pattern-match-good-measure))))))

(acl2::defines replace-adder-patterns-in-svex

  :flag-local nil

  :prepwork ((local
              (in-theory (e/d ()
                              (pattern-fn-call->args)))))

  (define replace-adder-patterns-in-svex ((x sv::Svex-p)
                                          &key
                                          ((pattern-alist pattern-alist-p) 'pattern-alist)
                                          (adder-type 'adder-type)
                                          (track-column? 'track-column?)
                                          ((env) 'env)
                                          ((context rp-term-listp) 'context)
                                          ((config svl::svex-reduce-config-p) 'config)
                                          )
    :measure (sv::svex-count x)
    :returns res
    :verify-guards nil
    (sv::svex-case
     x
     :quote x
     :var   x
     :call
     (b* ((x (sv::svex-fix x))
          (pattern-fn-call-list (adder-pattern-match x adder-type))
          (pattern-fn-call (pull-the-first-applicable-adder-pattern
                            pattern-alist pattern-fn-call-list track-column?)))
       (cond
        (pattern-fn-call
         (b* (((pattern-fn-call x) pattern-fn-call))
           (pattern-call x
                         (replace-adder-patterns-in-svexlist x.args))))
        (t
         (sv::svex-call x.fn
                        (replace-adder-patterns-in-svexlist x.args)))))))

  (define replace-adder-patterns-in-svexlist ((lst sv::svexlist-p)
                                              &key
                                              ((pattern-alist pattern-alist-p) 'pattern-alist)
                                              (adder-type 'adder-type)
                                              (track-column? 'track-column?)
                                              ((env) 'env)
                                              ((context rp-term-listp) 'context)
                                              ((config svl::svex-reduce-config-p) 'config))
    :returns res
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        nil
      (hons (replace-adder-patterns-in-svex (car lst))
            (replace-adder-patterns-in-svexlist (cdr lst)))))

  ///

  (defthm svex-p-pattern-call
    (implies (and (pattern-fn-call-p x)
                  (or (not optional-args)
                      (sv::svexlist-p optional-args)))
             (sv::svex-p (PATTERN-CALL x optional-args)))
    :hints (("Goal"
             :in-theory (e/d (PATTERN-CALL
                              SV::SVEX-P
                              PATTERN-FN-CALL->FN
                              PATTERN-FN-CALL-P)
                             ()))))

  (defret-mutual svex-p-of-<fn>
    (defret svex-p-of-<fn>
      (implies (sv::Svex-p x)
               (sv::Svex-p res))
      :fn replace-adder-patterns-in-svex)
    (defret Svexlist-p-of-<fn>
      (implies (sv::Svexlist-p lst)
               (sv::Svexlist-p res))
      :fn replace-adder-patterns-in-svexlist))

  (verify-guards replace-adder-patterns-in-svex-fn)

  (memoize 'replace-adder-patterns-in-svex ;; :condition '(eq (sv::svex-kind x) :call)
           )

  (defret-mutual replace-adder-patterns-in-svex-is-correct
    (defret <fn>-is-correct
      (implies (and (force (sv::svex-p x))
                    (force (warrants-for-adder-pattern-match))

                    (force (rp::rp-term-listp context))
                    (force (rp::valid-sc env-term a))
                    (force (rp::eval-and-all context a))
                    (force (rp::falist-consistent-aux env env-term))
                    (force (svl::width-of-svex-extn-correct$-lst
                            (svl::svex-reduce-config->width-extns config)))
                    (force
                     (svl::integerp-of-svex-extn-correct$-lst
                      (svl::svex-reduce-config->integerp-extns config))))
               (equal (sv::svex-eval$ res (rp-evlt env-term a))
                      (sv::svex-eval$ x (rp-evlt env-term a))))
      :fn replace-adder-patterns-in-svex)
    (defret <fn>-is-correct
      (implies (and (force (sv::Svexlist-p lst))
                    (force (warrants-for-adder-pattern-match))
                    (force (rp::rp-term-listp context))
                    (force (rp::valid-sc env-term a))
                    (force (rp::eval-and-all context a))
                    (force (rp::falist-consistent-aux env env-term))
                    (force (svl::width-of-svex-extn-correct$-lst
                            (svl::svex-reduce-config->width-extns config)))
                    (force
                     (svl::integerp-of-svex-extn-correct$-lst
                      (svl::svex-reduce-config->integerp-extns config))))
               (equal (sv::svexlist-eval$ res (rp-evlt env-term a))
                      (sv::svexlist-eval$ lst (rp-evlt env-term a))))
      :fn replace-adder-patterns-in-svexlist)
    :hints (("Goal"
             :do-not-induct t
             :expand ((replace-adder-patterns-in-svex x )
                      (replace-adder-patterns-in-svexlist lst )
                      (:free (x y env)
                             (sv::Svex-eval$ (cons x y) env)))
             :in-theory (e/d (SV::SVEX-EVAL$
                              SV::SVEXlist-EVAL$
                              SV::FNSYM-FIX
                              sv::svex-kind
                              SV::SVEX-P
                              PATTERN-CALL
                              SV::SVEX-CALL->ARGS
                              SV::SVEX-CALL->fn
                              )
                             (adder-pattern-match-correct-pattern)))
            (and STABLE-UNDER-SIMPLIFICATIONP
                 '(:use ((:instance
                          adder-pattern-match-correct-pattern
                          (pattern (pull-the-first-applicable-adder-pattern
                                    pattern-alist (adder-pattern-match x adder-type)
                                    track-column?))
                          (svex x))))
                 ))))

(define replace-adder-patterns-in-svex-alist ((alist sv::svex-alist-p)
                                              &key
                                              ((pattern-alist pattern-alist-p) 'pattern-alist)
                                              (adder-type 'adder-type)
                                              (track-column? 'track-column?)

                                              ((env) 'env)
                                              ((context rp-term-listp) 'context)
                                              ((config svl::svex-reduce-config-p) 'config)
                                              )
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      (progn$ (clear-memoize-table 'replace-adder-patterns-in-svex)
              nil)
    (acons (caar alist)
           (replace-adder-patterns-in-svex (cdar alist))
           (replace-adder-patterns-in-svex-alist (cdr alist))))
  ///
  (defret <fn>-is-correct
    (implies (and (force (sv::Svex-alist-p alist))
                  (force (warrants-for-adder-pattern-match))
                  (force (rp::rp-term-listp context))
                  (force (rp::valid-sc env-term a))
                  (force (rp::eval-and-all context a))
                  (force (rp::falist-consistent-aux env env-term))
                  (force (svl::width-of-svex-extn-correct$-lst
                          (svl::svex-reduce-config->width-extns config)))
                  (force
                   (svl::integerp-of-svex-extn-correct$-lst
                    (svl::svex-reduce-config->integerp-extns config))))
             (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                    (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
    :fn replace-adder-patterns-in-svex-alist
    :hints (("Goal"
             :in-theory (e/d (SV::SVEX-ALIST-EVAL$) ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Now on to careful search after initial replacements to see if any patterns
;; are missed.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection fix-order-of-fa/ha-s-args
  ;; After replacements,  ordered-ness of  arguments might change,  which might
  ;; prevent patterns  from being found  when looking more carefully.   So This
  ;; function goes around and reorders arguments in ONLY fa-s and ha-s arguments.
  (defines fix-order-of-fa/ha-s-args
    :verify-guards nil
    (define fix-order-of-fa/ha-s-args ((x sv::svex-p))
      :measure (sv::svex-count x)
      :returns (res sv::svex-p :hyp (sv::svex-p x))
      (sv::svex-case
       x
       :var x
       :quote x
       :call (case-match x
               (('fa-s-chain & & &)
                (b* ((lst1 (fix-order-of-fa/ha-s-args-list x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1)))
                  (sv::svex-call x.fn lst2)))
               (('ha-s-chain & &)
                (b* ((lst1 (fix-order-of-fa/ha-s-args-list x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1)))
                  (sv::svex-call x.fn lst2)))
               (& (sv::svex-call
                   x.fn
                   (fix-order-of-fa/ha-s-args-list x.args))))))
    (define fix-order-of-fa/ha-s-args-list ((lst sv::svexlist-p))
      :measure (sv::svexlist-count lst)
      :returns (res sv::svexlist-p :hyp (sv::svexlist-p lst))
      (if (atom lst)
          nil
        (hons (fix-order-of-fa/ha-s-args (car lst))
              (fix-order-of-fa/ha-s-args-list (cdr lst)))))

    ///

    (local
     (defthm svexlist-p-implies-true-listp
       (implies (sv::svexlist-p lst)
                (true-listp lst))))

    (verify-guards fix-order-of-fa/ha-s-args)

    (memoize 'fix-order-of-fa/ha-s-args
             ;; :condition '(eq (sv::svex-kind x) :call)
             )

    (defret-mutual <fn>-is-correct
      (defret <fn>-is-correct
        (implies (and (warrants-for-adder-pattern-match)
                      (sv::svex-p x))
                 (equal (sv::svex-eval$ res env)
                        (sv::svex-eval$ x env)))
        :fn fix-order-of-fa/ha-s-args)
      (defret <fn>-is-correct
        (implies (and (warrants-for-adder-pattern-match)
                      (sv::svexlist-p lst))
                 (equal (sv::svexlist-eval$ res env)
                        (sv::svexlist-eval$ lst env)))
        :fn fix-order-of-fa/ha-s-args-list)
      :hints (("Goal"

               :expand ((:free (args)
                               (sv::svex-apply$ 'ha-s-chain args))
                        (:free (args)
                               (sv::svex-apply$ 'fa-s-chain args))
                        (acl2::merge-sort-lexorder (cdr x))
                        (fix-order-of-fa/ha-s-args-list lst)
                        (fix-order-of-fa/ha-s-args x))
               :in-theory (e/d (acl2::merge-lexorder
                                acl2::merge-sort-lexorder
                                ha-s-chain
                                fa-s-chain
                                sv::svex-call->fn
                                sv::svex-call->args)
                               ())))))

  (define fix-order-of-fa/ha-s-args-alist ((alist sv::svex-alist-p))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
    (if (atom alist)
        nil
      (acons (caar alist)
             (fix-order-of-fa/ha-s-args (cdar alist))
             (fix-order-of-fa/ha-s-args-alist (cdr alist))))
    ///
    (defret <fn>-is-correct
      (implies (and (warrants-for-adder-pattern-match)
                    (sv::svex-alist-p alist))
               (equal (sv::svex-alist-eval$ res env)
                      (sv::svex-alist-eval$ alist env)))
      :fn fix-order-of-fa/ha-s-args-alist
      :hints (("Goal"
               :in-theory (e/d (SV::SVEX-ALIST-EVAL$) ()))))))

(defsection process-fa/ha-c-chain-pattern-args
  ;; Goal here is  to take a pattern-alist, and create  another fast-alist that
  ;; can be  used to find missed  fa-s/ha-s patterns. If  one of the args  of a
  ;; found fa-c/ha-c is  a bitxor, these function also  "explode" that argument
  ;; for a  more comprehensive  search.  Since  xor chains  can be  large, this
  ;; explosion     is    done     with     a    depth     limit    given     in
  ;; *process-fa/ha-c-chain-pattern-args-limit*.

  ;; For example, assume we have: (fa-c-chain  x y (bitxor m n)). And somewhere
  ;; else  in  the svex,  we  have  (bitxor m  (bitxor  x  (bitxor n  y))).   A
  ;; corresponding full-adder  sum pattern can  be pulled out from  this bitxor
  ;; chain.   So we  take this  already found  fa-c-chain pattern,  explode its
  ;; bitxor arguments and create a possible  search clue list containing: x y m
  ;; n. If we can  find an bitxor chain containing all  these values, then that
  ;; bitxor chain can be marked as a counterpart full-adder sum pattern.

  ;; The same thing  applies for when looking for half-adder  sum patterns from
  ;; half-adder carry.

  ;; These functions are not only useful for when looking for sum patterns from
  ;; already  found carry.  But  they  are also  useful  for  when looking  for
  ;; half-adder carry patterns from already found half-adder sum patterns.

  ;; TODO: expand this for ha+1 cases.

  ;; first define aux data types for easy programming.
  (fty::defprod exploded-args-and-args
    ((exploded-args sv::Svexlist-p) ;; exploded args
     (args sv::Svexlist-p) ;; original args as appears in full-adder carry chain.
     (column acl2::maybe-integerp))
    :layout :fulltree
    ;;:hons t
    )

  (fty::deflist exploded-args-and-args-list
    :elt-type exploded-args-and-args
    :true-listp t)

  (fty::defalist exploded-args-and-args-alist
    :key-type sv::svex-p
    :val-type exploded-args-and-args-list
    :true-listp t)

  (local
   (in-theory (disable ACL2::TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP-XXX
                       REMOVE-DUPLICATES-EQUAL
                       TRUE-LIST-LISTP
                       MEMBER-EQUAL)))

  (defthm exploded-args-and-args-alist-and-hons-assoc
    (implies (and (exploded-args-and-args-alist-p alist)
                  (hons-assoc-equal key alist))
             (and (sv::svex-p (car (hons-assoc-equal key alist)))
                  (exploded-args-and-args-list-p (cdr (hons-assoc-equal key alist)))))
    :hints (("Goal"
             :in-theory (e/d (exploded-args-and-args-alist-p) ()))))

  ;; define  an invariant  as need  to  know at  all times  that exploded  args
  ;; correspond to original args.
  (define exploded-args-and-args-inv ((x exploded-args-and-args-p)
                                      env
                                      &key
                                      ((bit-fn symbolp) 'bit-fn))
    :verify-guards nil
    (b* (((exploded-args-and-args x) x))
      (cond ((equal bit-fn 'sv::bitand) ;; when looking for ha-c from ha-s
             (equal (svl::svex-eval$-bitand-lst x.exploded-args env)
                    (svl::svex-eval$-bitand-lst x.args env)))
            ((equal bit-fn 'sv::bitor) ;; when looking for ha-c from ha-s
             (equal (svl::svex-eval$-bitor-lst x.exploded-args env)
                    (svl::svex-eval$-bitor-lst x.args env)))
            (t
             ;; otherwise expect to find bitxor at all times.
             (equal (svl::svex-eval$-bitxor-lst x.exploded-args env)
                    (svl::svex-eval$-bitxor-lst x.args env))))))

  (define exploded-args-and-args-list-inv ((lst exploded-args-and-args-list-p)
                                           env
                                           &key
                                           ((bit-fn symbolp) 'bit-fn))
    :verify-guards nil
    (if (atom lst)
        (equal lst nil)
      (and (exploded-args-and-args-inv (car lst) env)
           (exploded-args-and-args-list-inv (cdr lst) env))))

  (define exploded-args-and-args-alist-inv ((alist exploded-args-and-args-alist-p)
                                            env
                                            &key
                                            ((bit-fn symbolp) 'bit-fn))
    :verify-guards nil
    (if (atom alist)
        (equal alist nil)
      (and (exploded-args-and-args-list-inv (cdar alist) env)
           (exploded-args-and-args-alist-inv (cdr alist) env)))
    ///
    (defthm exploded-args-and-args-alist-inv-x-is-nil
      (exploded-args-and-args-alist-inv nil env))

    (defthm exploded-args-and-args-alist-inv-hons-assoc
      (implies (exploded-args-and-args-alist-inv alist env)
               (exploded-args-and-args-list-inv (cdr (hons-assoc-equal key alist)) env))
      :hints (("Goal"
               :expand (EXPLODED-ARGS-AND-ARGS-LIST-INV NIL ENV)
               :in-theory (e/d () ())))))

  ;; set a limit for explosion in order to save time.
  (define process-fa/ha-c-chain-pattern-args-limit ()
    :returns (res natp)
    (if (aggressive-find-adders-in-svex) ;; agressive search will trigger a deeper explosion.
        5
      2) ; 2 should be sufficient for the majority of cases if not all.
    ///
    (in-theory (disable (:e process-fa/ha-c-chain-pattern-args-limit))))

  ;; Need to create a fast-alist to lookup possibly matching arguments quickly.
  ;; This function pick a  the best key. It looks like it is  best for this key
  ;; to not be  a partsel of a variable  OR when an argument is  a constant.  I
  ;; cannot recall  why this  is the  case and  this may  now be  redundant. It
  ;; probably helps with speed ups. Note that it may still select these as keys
  ;; if no other leaf is left.
  (define cons-with-best-first-key (leaves rest-keys)
    ;; chosing constants or simple partsel of input operands is not a good choice usually...
    :returns (keys sv::svexlist-p :hyp (and (sv::Svexlist-p leaves)
                                            (sv::Svexlist-p rest-keys)))
    (if (atom leaves)
        rest-keys
      (b* ((l (car leaves))
           ((when (and (or (integerp l)
                           (case-match l
                             (('sv::partsel & & x)
                              (atom x))))
                       (consp (cdr leaves))))
            (cons-with-best-first-key (cdr leaves) rest-keys)))
        (cons l rest-keys))))

  ;; Pull exploded args, and also create keys for quick lookups.
  (define process-fa/ha-c-chain-pattern-args-aux ((args)
                                                  &key
                                                  ((bit-fn symbolp) 'bit-fn))
    :prepwork
    ((local
      (defret consp-of-<fn>
        (consp svl::leaves)
        :fn svl::bitand/or/xor-collect-leaves2
        :hints (("Goal"
                 :in-theory (e/d (svl::bitand/or/xor-collect-leaves2) ()))))))

    :returns (mv (keys sv::svexlist-p :hyp (and (sv::Svexlist-p args)
                                                (force (or (equal bit-fn 'sv::bitand)
                                                           (equal bit-fn 'sv::bitor)
                                                           (equal bit-fn 'sv::bitxor)))))
                 (exploded-args sv::svexlist-p :hyp (and (sv::Svexlist-p args)
                                                         (force
                                                          (or (equal bit-fn 'sv::bitand)
                                                              (equal bit-fn 'sv::bitor)
                                                              (equal bit-fn 'sv::bitxor))))))
    (if (atom args)
        (mv nil nil)
      (b* (((mv rest-keys exploded-args)
            (process-fa/ha-c-chain-pattern-args-aux (cdr args)))
           ((mv leaves &)
            (svl::bitand/or/xor-collect-leaves2 (car args)
                                                bit-fn
                                                (process-fa/ha-c-chain-pattern-args-limit))))
        (mv (cons-with-best-first-key leaves rest-keys)
            (append leaves exploded-args))))
    ///
    (defret <fn>-is-correct
      (and (implies (equal bit-fn 'sv::bitxor)
                    (equal (svl::svex-eval$-bitxor-lst exploded-args env)
                           (svl::svex-eval$-bitxor-lst args env)))
           (implies (equal bit-fn 'sv::bitand)
                    (equal (svl::svex-eval$-bitand-lst exploded-args env)
                           (svl::svex-eval$-bitand-lst args env)))
           (implies (equal bit-fn 'sv::bitor)
                    (equal (svl::svex-eval$-bitor-lst exploded-args env)
                           (svl::svex-eval$-bitor-lst args env)))
           )
      :fn process-fa/ha-c-chain-pattern-args-aux))

  ;; create fast-alist  entries to  find exploded-args and  args. Note  that it
  ;; does not override already existing entries!!
  (define process-fa/ha-c-chain-pattern-args-collect-aux ((keys true-listp)
                                                          exploded-args-and-args
                                                          collected
                                                          &key
                                                          (enabled 't))
    :returns (collected-res exploded-args-and-args-alist-p
                            :hyp (and (exploded-args-and-args-alist-p collected)
                                      (or (not enabled) (sv::svexlist-p keys))
                                      (or (not enabled) (exploded-args-and-args-p exploded-args-and-args))))
    (if (atom keys)
        collected
      (b* (((unless enabled) collected)
           (key (car keys))
           (existing-entry (cdr (hons-get key collected)))
           (new-entry (cons exploded-args-and-args existing-entry)))
        (process-fa/ha-c-chain-pattern-args-collect-aux (cdr keys)
                                                        exploded-args-and-args
                                                        (hons-acons key new-entry collected)
                                                        :enabled enabled)))
    ///

    (defret <fn>-is-correct
      (implies (and (exploded-args-and-args-alist-inv collected env)
                    (or (not enabled)
                        (exploded-args-and-args-inv exploded-args-and-args env)))
               (exploded-args-and-args-alist-inv collected-res env))
      :hints (("Goal"
               :in-theory (e/d (exploded-args-and-args-alist-inv
                                exploded-args-and-args-list-inv)
                               ())))))

  (defthm svexlist-p-implies-true-listp
    (implies (sv::Svexlist-p x)
             (true-listp x))
    :rule-classes (:rewrite))

  ;; check inersection without consing.
  (define has-common-elements-p (l1 (l2 true-listp))
    (if (atom l1)
        nil
      (or (member-equal (car l1) l2)
          (has-common-elements-p (cdr l1) l2))))

  (local
   (in-theory (disable subsetp-equal)))

  (define safe-take ((num natp) x)
    :returns (res sv::svexlist-p :hyp (sv::svexlist-p x))
    (if (or (atom x)
            (zp num))
        nil
      (cons (car x)
            (safe-take (1- num) (cdr x)))))

  #|(local
  (defthm EXPLODED-ARGS-AND-ARGS-ALIST-P-implies-true-listp ;
  (implies (EXPLODED-ARGS-AND-ARGS-ALIST-P x) ;
  (true-listp x))))|#

  (local
   (defthmd dumb-true-listp-lemma
     (implies (true-listp x)
              (iff (consp x)
                   x))
     ))

  ;; (define pull-first-args-from-pattern-alist ((pattern-alist pattern-alist-p)
  ;;                                             (track-column?))
  ;;   :inline t
  ;;   :guard (consp pattern-alist)
  ;;   :returns (args sv::svexlist-p :hyp (and ;;(pattern-alist-p pattern-alist)
  ;;                                       (consp pattern-alist)))
  ;;   (b* ((args (caar (pattern-alist-fix pattern-alist)))
  ;;        (args (if  track-column? (cdr  args)  args)))
  ;;     ;;if track-column? is
  ;;     ;; activated,   then   the
  ;;     ;; first   arg   will   be
  ;;     ;; column number,  we need
  ;;     ;; to get rid of it.
  ;;     args))

  (define check-member-in-pattern-fns ((fn symbolp) fns
                                       &key
                                       (track-column? 'track-column?))
    (if (atom fns)
        nil
      (or (cond (track-column? ;; when track-column?,  a fn will be expected to
                 ;; be in the  form of (ha-c-chain .  5) where  5 is the column
                 ;; number that the match  should happen.  This function should
                 ;; return that number when
                 (and (consp (car fns))
                      (eq fn (caar fns))
                      (cdar fns)))
                (t (eq fn (car fns))))
          (check-member-in-pattern-fns fn (cdr fns)))))

  (with-output
    :off :all
    :on (error summary)
    :gag-mode nil
    (define process-fa/ha-c-chain-pattern-args ((pattern-alist pattern-alist-p)
                                                (collected exploded-args-and-args-alist-p)
                                                &key
                                                ((adder-type symbolp) 'adder-type)
                                                (track-column? 'track-column?))
      :returns (collected-res exploded-args-and-args-alist-p
                              :hyp (and (exploded-args-and-args-alist-p collected)
                                        (pattern-alist-p pattern-alist)))
      :guard-hints (("Goal")
                    (and stable-under-simplificationp
                         '(:in-theory (e/d (dumb-true-listp-lemma) ()))))
      (if (atom pattern-alist)
          collected
        (b* ((fns (cdar (pattern-alist-fix pattern-alist)))

             ;; if already has a pattern of its self, then don't be too hard on
             ;; it and avoid-column-check.  Setting the  column value to nil in
             ;; exploded-args-and-args  should  later  make  the  program  skip
             ;; column check.

             ((mv bit-fn column/match-p do-not-explode avoid-column-check)
              (cond ((eq adder-type 'ha)
                     (mv 'sv::bitxor (or (check-member-in-pattern-fns 'ha-c-chain fns)
                                         (check-member-in-pattern-fns 'ha+1-c-chain fns))
                         nil
                         (and*-exec track-column?
                                    (or* (check-member-in-pattern-fns 'ha-s-chain-self fns)
                                         (check-member-in-pattern-fns 'ha+1-s-chain-self fns)))))
                    ((eq adder-type 'ha-c) ;; ha-c will also be searched carefully like sum outputs.
                     (mv 'sv::bitand
                         (check-member-in-pattern-fns 'ha-s-chain fns)
                         nil ;;(check-member-in-pattern-fns 'ha-c-chain fns) ;;
                         ;;if there is already a full pattern, then don't
                         ;;explode..
                         (and*-exec track-column?
                                    (check-member-in-pattern-fns 'ha-s-chain-self fns))
                         ))
                    ((eq adder-type 'ha+1-c) ;; probably not fully implemented.
                     (mv 'sv::bitor
                         (check-member-in-pattern-fns 'ha+1-s-chain fns)
                         nil ;;(check-member-in-pattern-fns 'ha+1-c-chain fns)
                         ;; if there is already a full pattern, then don't
                         ;; explode..
                         (and*-exec track-column?
                                    (check-member-in-pattern-fns 'ha+1-s-chain-self fns))
                         ))
                    (t (mv 'sv::bitxor
                           (check-member-in-pattern-fns 'fa-c-chain fns)
                           nil
                           (and*-exec track-column?
                                      (check-member-in-pattern-fns 'fa-s-chain-self fns))))))
             ;; making the check subsetp-equal to still hit partially found fa-s/ha-s pairs.
             ((unless column/match-p)
              (process-fa/ha-c-chain-pattern-args (cdr pattern-alist) collected))
             (args (caar (pattern-alist-fix pattern-alist)))
             ((when (and*-exec (eq adder-type 'ha) (or* (member 0 args) (member 1 args))))
              ;; constants should not be in args, at least for ha. if they are, ignore them..
              (process-fa/ha-c-chain-pattern-args (cdr pattern-alist) collected))
             ((mv keys exploded-args)
              (if do-not-explode
                  (mv args args)
                (process-fa/ha-c-chain-pattern-args-aux args)))

             (keys (safe-take 1 keys)) ;; minimize the number of keys to prevent cluttering the collected alist

             (exploded-args-orig exploded-args)
             ;; remove  duplicates to  maximize  changes  why remove  duplicates:
             ;; because  the matching  pattern might  have already  simplifed the
             ;; repeated elements.
             (exploded-args (cond ((equal bit-fn 'sv::bitxor)
                                   (svl::remove-pair-equal exploded-args)
                                   #|(remove-equal 0
                                   )|#)
                                  ((equal bit-fn 'sv::bitor)
                                   (remove-duplicates-equal exploded-args)
                                   #|(remove-equal 0
                                   )|#)
                                  ((equal bit-fn 'sv::bitand)
                                   (remove-duplicates-equal exploded-args))
                                  (t
                                   exploded-args ;; maybe make it remove duplicates or something.
                                   )))

             ;; All  viable  keys   could  have  been  removed   above  due  to
             ;; removing-pairs/duplicates above if that's the case, then extend
             ;; keys to make sure we can have a hit:
             (keys (if (implies (or keys ;;  keys might be intentionally empty if
                                    ;; so, then don't put  stuff in it unless the
                                    ;; agressive mode is enabled.
                                    (aggressive-find-adders-in-svex))
                                (has-common-elements-p keys exploded-args))
                       keys
                     (append (safe-take 1 exploded-args) keys)))

             (?exploded-args-and-args (make-exploded-args-and-args :exploded-args exploded-args
                                                                   :args args
                                                                   :column (and*-exec track-column?
                                                                                      (not* avoid-column-check)
                                                                                      (integerp column/match-p)
                                                                                      column/match-p)))
             (collected (process-fa/ha-c-chain-pattern-args-collect-aux keys exploded-args-and-args collected))

             (exploded-args-changed? (not (equal exploded-args-orig exploded-args)))
             (collected
              ;; do   this  below   when   removing  duplicates/pairs   changes
              ;; something. this makes  sure we have both  versions to increase
              ;; the chances.
              (process-fa/ha-c-chain-pattern-args-collect-aux keys
                                                              (and exploded-args-changed?
                                                                   (change-exploded-args-and-args
                                                                    exploded-args-and-args
                                                                    :exploded-args exploded-args-orig))
                                                              collected
                                                              :enabled exploded-args-changed?))

             )
          (process-fa/ha-c-chain-pattern-args (cdr pattern-alist) collected)))
      ///

      (local
       (defthm atom-remove-pair-equal-lemma
         (implies (bind-free '((env . env)) (env))
                  (iff (consp (svl::remove-pair-equal lst))
                       (not (and (hide (not (consp (svl::remove-pair-equal lst))))
                                 (equal (svl::svex-eval$-bitxor-lst lst env)
                                        0)))))
         :hints (("goal"
                  :use ((:instance svl::svex-eval$-bitxor-lst-of-remove-pair-equal
                                   (svl::lst lst)))
                  :do-not-induct t
                  :expand ((:free (x) (hide x)))
                  :in-theory (e/d ()
                                  (svl::svex-eval$-bitxor-lst-of-remove-pair-equal
                                   svl::remove-pair-equal
                                   ;;svl::svex-eval$-bitxor-lst
                                   ))))))
      (defret <fn>-is-correct
        (and
         (implies (and (exploded-args-and-args-alist-inv collected env :bit-fn 'sv::bitand)
                       (equal adder-type 'ha-c))
                  (exploded-args-and-args-alist-inv collected-res env :bit-fn 'sv::bitand))
         (implies (and (exploded-args-and-args-alist-inv collected env :bit-fn 'sv::bitor)
                       (equal adder-type 'ha+1-c))
                  (exploded-args-and-args-alist-inv collected-res env :bit-fn 'sv::bitor))
         (implies (and (exploded-args-and-args-alist-inv collected env :bit-fn 'sv::bitxor)
                       (not (equal adder-type 'ha+1-c))
                       (not (equal adder-type 'ha-c)))
                  (exploded-args-and-args-alist-inv collected-res env :bit-fn 'sv::bitxor)))
        :hints (("Goal"
                 :do-not-induct t
                 :expand ((process-fa/ha-c-chain-pattern-args pattern-alist collected
                                                              :adder-type 'ha))
                 :induct (process-fa/ha-c-chain-pattern-args pattern-alist collected)
                 :in-theory (e/d (exploded-args-and-args
                                  exploded-args-and-args->exploded-args
                                  exploded-args-and-args->args
                                  exploded-args-and-args-inv)
                                 (if*
                                  pattern-alist-p-of-cons))))))))

(defsection find-s-from-found-c-in-svex-aux-explore
  ;; These functions perform  a "cheap" search to see if  all the exploded args
  ;; appear as an argument  in the bitxor (or bitand) chain of  an svex. AND it
  ;; makes sure  that exploded args  are distributed  into two branches  of the
  ;; topmost  bitxor/bitnad.  Why  topmost:  because we  want  to preserve  the
  ;; original structure  as much  as possible  and this  indicates that  we are
  ;; ready to  shuffle around  the svex to  reveal the  matching ha-s/fa-s/ha-c
  ;; pattern.

  ;; For example, assume we have already found this: (fa-c-chain x y z), and we
  ;; are looking for a counterpart fa-s in this term:

  ;; (bitxor (bitxor  x (bitxor  a (bitxor  y z))) (bitxor  k m)).   Since this
  ;; bitxor chain has x, y and z, we can say that this includes our counterpart
  ;; full-adder sum  pattern. One thing we  can do is shuffle  the arguments at
  ;; this stage to pull out the fa-s as follows:
  ;; (bitxor (fa-s-chain x y z) (bitxor a (bitxor k m)))
  ;; Another  option is  to dive  into  the first  branch of  the main  bitxor:
  ;; (bitxor  x (bitxor  a (bitxor  y z))),  and only  shuffle these  arguments
  ;; around. So we'd get:
  ;; (bitxor (bitxor a (fa-s-chain x y z)) (bitxor k m))
  ;; a logically  equivalent term but  syntactically different. I  preferred to
  ;; use the second  option because the first one causes  elements in bitxor to
  ;; be  moved  around  too  much  and it  changes  the  original  structure  a
  ;; lot. During development, this made it very difficult to debug things. So I
  ;; now dive in as much as possible before shuffling elements around to reveal
  ;; counterpart  full-adder sum  patterns.  It  is possible  that this  became
  ;; redundant now and that this may not have any benefits anymore but there is
  ;; no harm keeping  this system intact.  This may help  with debugging in the
  ;; feature.

  (local
   (defthm member-equal-of-hons-assoc-equal
     (implies (hons-assoc-equal x lst)
              (member-equal (hons-assoc-equal x lst)
                            lst))))
  (local
   (defthm sv::svexlist-p-implies-true-listp
     (implies (sv::svexlist-p lst)
              (true-listp lst))))

  ;; Find a possible match from exploded-args-and-args-alist.
  (define find-s-from-found-c-in-svex-aux-explore-aux ((svex)
                                                       (exploded-args-and-args-alist)
                                                       (skip true-listp)
                                                       &key
                                                       ((bit-fn symbolp) 'bit-fn))
    :returns (alist-entry (implies alist-entry
                                   (member-equal alist-entry exploded-args-and-args-alist)))
    (case-match svex
      ((fn x y)
       (and (equal bit-fn fn)
            (or  ;;  be  careful:  the  below ordering  in  (and  ...) is  very
             ;;  important. This makes  sure that the result  of hons-get is
             ;;  returned upon success. So do not swap!
             (and (not  (member-equal x skip))
                  (hons-get x exploded-args-and-args-alist))
             (and (not (member-equal y skip))
                  (hons-get y exploded-args-and-args-alist))
             (find-s-from-found-c-in-svex-aux-explore-aux x exploded-args-and-args-alist skip)
             (find-s-from-found-c-in-svex-aux-explore-aux y exploded-args-and-args-alist skip))))
      (& nil))
    ///
    (defret return-val-of-<fn>
      (implies (and alist-entry
                    (exploded-args-and-args-alist-p exploded-args-and-args-alist))
               (and (consp alist-entry)
                    (sv::svex-p (car alist-entry))
                    (exploded-args-and-args-list-p (cdr alist-entry))))
      :hints (("Goal"
               :in-theory (e/d () (true-listp hons-assoc-equal)))))

    (defret <fn>-is-correct
      (implies (and (exploded-args-and-args-alist-inv exploded-args-and-args-alist env)
                    alist-entry)
               (exploded-args-and-args-list-inv (cdr alist-entry) env))))

  (define find-s-from-found-c-guard (bit-fn svex)
    :inline t
    :enabled t
    (cond ((equal bit-fn 'sv::bitand)
           (bitand-pattern-p svex))
          ((equal bit-fn 'sv::bitor)
           (bitor-pattern-p svex))
          (t
           (bitxor-pattern-p svex))))

  ;; When this function returns 3, then it means the exploded-args appear in both
  ;; branches of the svex. It will indicate that rewriting the svex at this point
  ;; is a good idea.
  (define find-s-from-found-c-in-svex-aux-explore2 ((svex)
                                                    (exploded-args)
                                                    &key
                                                    ((bit-fn symbolp) 'bit-fn))
    :prepwork
    ((define find-s-from-found-c-in-svex-aux-arg-exists-p ((svex)
                                                           (arg)
                                                           &key
                                                           ((bit-fn symbolp) 'bit-fn))
       :returns exists
       (or (hons-equal svex arg)
           (case-match svex
             ((fn x y)
              (and (equal fn bit-fn)
                   (or (find-s-from-found-c-in-svex-aux-arg-exists-p x arg)
                       (find-s-from-found-c-in-svex-aux-arg-exists-p y arg))))
             (& nil)))))
    :returns (exist-branch (and (acl2::maybe-integerp exist-branch)
                                (or (not exist-branch)
                                    (equal exist-branch 0)
                                    (equal exist-branch 1)
                                    (equal exist-branch 2)
                                    (equal exist-branch 3))))
    :guard (find-s-from-found-c-guard bit-fn svex)
    (if (atom exploded-args)
        0
      (b* ((rest (find-s-from-found-c-in-svex-aux-explore2 svex (cdr exploded-args)))
           ((Unless rest)
            nil)
           (cur (car exploded-args))
           (x (cadr svex))
           (exist-in-x (find-s-from-found-c-in-svex-aux-arg-exists-p x cur))
           ((when exist-in-x)
            (logior 1 rest))
           (y (caddr svex))
           (exist-in-y (find-s-from-found-c-in-svex-aux-arg-exists-p y cur))
           ((when exist-in-y)
            (logior 2 rest))
           ((when (integerp cur)) ;; will need to borrow a constant (likely 1 or -1).
            (logior 0 rest)))
        nil)))

  (define find-s-from-found-c-in-svex-aux-explore-list ((svex)
                                                        (exploded-args-and-args-list exploded-args-and-args-list-p)
                                                        &key
                                                        ((bit-fn symbolp) 'bit-fn)
                                                        ((column acl2::maybe-integerp) 'column)
                                                        ;; give a large limit for measure. I don't expect this to go too big.
                                                        )
    :guard-debug t
    :guard (find-s-from-found-c-guard bit-fn svex)
    :returns #|(mv (args sv::svexlist-p :hyp (force (exploded-args-and-args-list-p exploded-args-and-args-list)))
    (exploded-args sv::svexlist-p :hyp (force (exploded-args-and-args-list-p
    exploded-args-and-args-list)))
    (column acl2::maybe-integerp :hyp (force (exploded-args-and-args-list-p exploded-args-and-args-list)))
    )|#
    (exploded-args-and-args exploded-args-and-args-p :hyp (force (exploded-args-and-args-list-p exploded-args-and-args-list)))

    (if (atom exploded-args-and-args-list)
        (make-exploded-args-and-args) ;;(mv nil nil nil)
      (b* (((exploded-args-and-args cur) (car exploded-args-and-args-list))
           ((when (and*-exec column cur.column
                             ;; this is not  a great way to do  this because it
                             ;; will mess up column value when it is full-adder that is missed.
                             (not (equal cur.column (if* (eq bit-fn 'sv::bitxor) column (1- column))))))
            (find-s-from-found-c-in-svex-aux-explore-list svex (cdr exploded-args-and-args-list)))
           (args cur.args)
           (exploded-ags cur.exploded-args)
           ;; See if all the exploded-args  are present in svex. Also determine
           ;; if  they are  dispersed into  two branches  of bitxor  (bitand if
           ;; working for ha-c), or if they all  appear in only one of them. If
           ;; they  appear in  only  one of  the branches,  it  means the  same
           ;; pattern can be  applied down the line.  In order  to preserve the
           ;; SVEX'es structure  as much  as possible,  we avoid  applying such
           ;; matches when it is too early.
           (exist-branch (find-s-from-found-c-in-svex-aux-explore2 svex exploded-ags))
           ;; 3 means all exploded-args exist, and they are dispersed to the two branches.
           ((when (equal exist-branch 3))
            (progn$ (and*-exec
                     ;; a  check  to print a warning message  when  ha/ha-c is  being
                     ;; searched, it didn't just match the svex itself. Catching such a case
                     ;; might indicate something went wrong along the way because that would
                     ;; have been caught in quick search stage.
                     (svl::equal-len args 2)
                     (consp svex)
                     (subsetp-equal args (cdr svex))
                     (subsetp-equal (cdr svex) args)
                     (cwe "WARNING: Careful search found something that should have been matched in the quick search stage.~%"))
                    cur
                    #|(mv args exploded-ags cur.column)|#)))

        ;;if exist-branch is not 3, then keep searching for other matches.
        (find-s-from-found-c-in-svex-aux-explore-list svex (cdr exploded-args-and-args-list))))
    ///
    (defret <fn>-is-correct
      (b* (((exploded-args-and-args cur) exploded-args-and-args))
        (implies (and (exploded-args-and-args-list-inv exploded-args-and-args-list env)
                      cur.args)
                 (and (implies (equal bit-fn 'sv::bitxor)
                               (equal (svl::svex-eval$-bitxor-lst cur.args env)
                                      (svl::svex-eval$-bitxor-lst cur.exploded-args env)))
                      (implies (equal bit-fn 'sv::bitand)
                               (equal (svl::svex-eval$-bitand-lst cur.args env)
                                      (svl::svex-eval$-bitand-lst cur.exploded-args env)
                                      ))
                      (implies (equal bit-fn 'sv::bitor)
                               (equal (svl::svex-eval$-bitor-lst cur.args env)
                                      (svl::svex-eval$-bitor-lst cur.exploded-args env)
                                      )))))
      :hints (("Goal"
               :in-theory (e/d (exploded-args-and-args-list-inv
                                exploded-args-and-args-inv
                                )
                               ())))))

  ;; This function should return ARGS and EXPLODED-ARGS  that are ready to be applied the svex
  (define find-s-from-found-c-in-svex-aux-explore ((svex)
                                                   (exploded-args-and-args-alist exploded-args-and-args-alist-p)
                                                   (skip true-listp)
                                                   &key
                                                   ((bit-fn symbolp) 'bit-fn)
                                                   ((column acl2::maybe-integerp) 'column)
                                                   ;; give a large limit for measure. I don't expect this to go too big.
                                                   ((limit natp) '1000))
    :guard-debug t
    :guard (find-s-from-found-c-guard bit-fn svex)
    :returns (exploded-args-and-args exploded-args-and-args-p
                                     :hyp (force (exploded-args-and-args-alist-p exploded-args-and-args-alist)))
    #|(mv (args sv::svexlist-p :hyp (force (exploded-args-and-args-alist-p exploded-args-and-args-alist)))
    (exploded-args sv::svexlist-p :hyp (force (exploded-args-and-args-alist-p ;
    exploded-args-and-args-alist))))|#
    :measure (nfix limit)
    (if (zp limit)
        (make-exploded-args-and-args) ;;(mv nil nil)
      (b* (;; find  the first candidate by  looking up only one key.  It is not
           ;; guaranteed for other args to be present.
           (entry (find-s-from-found-c-in-svex-aux-explore-aux svex exploded-args-and-args-alist skip))
           ((Unless entry)
            (make-exploded-args-and-args)#|(Mv nil nil)|#)
           (key (car entry))
           (exploded-args-and-args-list (cdr entry))
           ((exploded-args-and-args cur)
            (find-s-from-found-c-in-svex-aux-explore-list svex exploded-args-and-args-list))
           ((when (and cur.args))
            cur))
        (find-s-from-found-c-in-svex-aux-explore svex exploded-args-and-args-alist
                                                 (cons key skip)
                                                 :limit (1- limit))))
    ///
    (defret <fn>-is-correct
      (b* (((exploded-args-and-args cur) exploded-args-and-args))
        (implies (and (exploded-args-and-args-alist-inv exploded-args-and-args-alist env)
                      cur.args)
                 (and (implies (equal bit-fn 'sv::bitxor)
                               (equal (svl::svex-eval$-bitxor-lst cur.args env)
                                      (svl::svex-eval$-bitxor-lst cur.exploded-args env)))
                      (implies (equal bit-fn 'sv::bitor)
                               (equal (svl::svex-eval$-bitor-lst cur.args env)
                                      (svl::svex-eval$-bitor-lst cur.exploded-args env)))
                      (implies (equal bit-fn 'sv::bitand)
                               (equal (svl::svex-eval$-bitand-lst cur.args env)
                                      (svl::svex-eval$-bitand-lst cur.exploded-args env)
                                      ))))))))

; Matt K. mod, 2/20/2023: The use of (logbitp-reasoning) makes ACL2(p) with
; waterfall-parallelism enabled complain that "the form (LOGBITP-REASONING) was
; expected to represent an ordinary value, not an error triple (mv erp val
; state), as would be acceptable in a serial execution of ACL2".  So I'll turn
; off waterfall parallelism here.
(local (set-waterfall-parallelism nil))

;; This is to remove everyting in to-remove-lst
;; When remaining-to-remove is nil, then it means everything in to-remove-lst was removed.
(define find-s-from-found-c-in-svex-aux-remove ((svex)
                                                (to-remove-lst)
                                                &key
                                                ((bit-fn symbolp) 'bit-fn))

  :prepwork
  ((define remove-equal-once (x lst)
     :returns (res true-listp :hyp (true-listp lst))
     (cond ((atom lst)
            nil)
           ((equal x (car lst))
            (cdr lst))
           (t (cons-with-hint (car lst)
                              (remove-equal-once x (cdr lst))
                              lst)))
     ///
     (defret svexlist-p-of-<fn>
       (implies (sv::svexlist-p lst)
                (sv::svexlist-p res)))
     (defret integerp-of-<fn>-1
       (implies (integer-listp (sv::svexlist-eval$ lst env))
                (integer-listp (sv::svexlist-eval$ res env)))))

   (define svex-apply$-for-bitxor-meta (arg1 arg2)
     :returns (res-svex sv::svex-p :hyp (and (force (sv::svex-p arg1))
                                             (force (sv::svex-p arg2))))
     :inline t
     (cond ((equal arg1 0)
            arg2)
           ((equal arg2 0)
            arg1)
           (t (hons-list 'sv::bitxor arg1 arg2)))
     ///
     (defret <fn>-is-correct
       (and (equal (sv::3vec-fix (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                    (sv::svex-eval$ arg2 env)))
            (equal (sv::4vec-bitxor (sv::svex-eval$ res-svex env) other)
                   (sv::4vec-bitxor (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                                     (sv::svex-eval$ arg2 env))
                                    other))
            (equal (sv::4vec-bitxor other (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitxor (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                                     (sv::svex-eval$ arg2 env))
                                    other)))
       :hints (("Goal"
                :expand ((:free (args)
                                (sv::svex-apply 'sv::bitxor args)))
                :in-theory (e/d (sv::svex-call->fn
                                 sv::svex-call->args
                                 SV::SVEXLIST-EVAL$)
                                ()))))

     )

   (define svex-apply$-for-bitand-meta (arg1 arg2)
     :returns (res-svex sv::svex-p :hyp (and (force (sv::svex-p arg1))
                                             (force (sv::svex-p arg2))))
     :inline t
     (cond ((or (equal arg1 0)
                (equal arg2 0))
            0)
           ((equal arg2 -1)
            arg1)
           ((equal arg1 -1)
            arg2)
           (t (hons-list 'sv::bitand arg1 arg2)))
     ///
     (defret <fn>-is-correct
       (and (equal (sv::3vec-fix (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitand (sv::svex-eval$ arg1 env)
                                    (sv::svex-eval$ arg2 env)))
            (equal (sv::4vec-bitand (sv::svex-eval$ res-svex env) other)
                   (sv::4vec-bitand (sv::4vec-bitand (sv::svex-eval$ arg1 env)
                                                     (sv::svex-eval$ arg2 env))
                                    other))
            (equal (sv::4vec-bitand other (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitand (sv::4vec-bitand (sv::svex-eval$ arg1 env)
                                                     (sv::svex-eval$ arg2 env))
                                    other)))
       :hints (("Goal"
                :expand ((:free (args)
                                (sv::svex-apply 'sv::bitand args)))
                :in-theory (e/d (sv::svex-call->fn
                                 sv::svex-call->args
                                 SV::SVEXLIST-EVAL$)
                                ()))))

     )

   (define svex-apply$-for-bitor-meta (arg1 arg2)
     :returns (res-svex sv::svex-p :hyp (and (force (sv::svex-p arg1))
                                             (force (sv::svex-p arg2))))
     :inline t
     (cond ((or (equal arg1 -1)
                (equal arg2 -1))
            -1)
           ((equal arg1 0)
            arg2)
           ((equal arg2 0)
            arg1)
           (t (hons-list 'sv::bitor arg1 arg2)))
     ///
     (defret <fn>-is-correct
       (and (equal (sv::3vec-fix (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitor (sv::svex-eval$ arg1 env)
                                   (sv::svex-eval$ arg2 env)))
            (equal (sv::4vec-bitor (sv::svex-eval$ res-svex env) other)
                   (sv::4vec-bitor (sv::4vec-bitor (sv::svex-eval$ arg1 env)
                                                   (sv::svex-eval$ arg2 env))
                                   other))
            (equal (sv::4vec-bitor other (sv::svex-eval$ res-svex env))
                   (sv::4vec-bitor (sv::4vec-bitor (sv::svex-eval$ arg1 env)
                                                   (sv::svex-eval$ arg2 env))
                                   other)))
       :hints (("goal"
                :expand ((:free (args)
                                (sv::svex-apply 'sv::bitor args))
                         (:free (x) (SV::4VEC-BITOR -1 x))
                         (:free (x) (SV::3VEC-BITOR -1 x)))
                :in-theory (e/d (sv::svex-call->fn
                                 sv::svex-call->args
                                 sv::svexlist-eval$)
                                ())))))

   )

  :returns (mv (res-svex sv::svex-p :hyp (and (sv::svex-p svex)
                                              (or (equal bit-fn 'sv::bitand)
                                                  (equal bit-fn 'sv::bitor)
                                                  (equal bit-fn 'sv::bitxor))))
               (remaining-to-remove sv::svexlist-p :hyp
                                    (and (sv::svexlist-p to-remove-lst)
                                         (or (equal bit-fn 'sv::bitand)
                                             (equal bit-fn 'sv::bitor)
                                             (equal bit-fn 'sv::bitxor)))))
  :verify-guards :after-returns

  (case-match svex
    ((fn x y)
     (b* (((unless (equal fn bit-fn))
           (if (svl::member-hons-equal svex to-remove-lst)
               (mv (if (eq bit-fn 'sv::bitand) -1 0)
                   (remove-equal-once svex to-remove-lst))
             (mv svex to-remove-lst)))
          (remove-x (svl::member-hons-equal x to-remove-lst))
          ((mv x to-remove-lst)
           (if remove-x
               (mv (if (eq bit-fn 'sv::bitand) -1 0)
                   (remove-equal-once x to-remove-lst))
             (find-s-from-found-c-in-svex-aux-remove x to-remove-lst)))
          (remove-y (svl::member-hons-equal y to-remove-lst))
          ((mv y to-remove-lst)
           (if remove-y
               (mv (if (eq bit-fn 'sv::bitand) -1 0)
                   (remove-equal-once y to-remove-lst))
             (find-s-from-found-c-in-svex-aux-remove y to-remove-lst))))
       (mv
        (cond ((eq bit-fn 'sv::bitand)
               (svex-apply$-for-bitand-meta x y))
              ((eq bit-fn 'sv::bitor)
               (svex-apply$-for-bitor-meta x y))
              (t
               (svex-apply$-for-bitxor-meta x y)))
        to-remove-lst)))
    (& (mv svex to-remove-lst)))
  ///

  (defret integerp-of-<fn>-1
    (implies (integer-listp (sv::svexlist-eval$ to-remove-lst env))
             (integer-listp (sv::svexlist-eval$ remaining-to-remove env))))

  (local
   (defthm svex-eval$-when-4vec-p
     (implies (sv::4vec-p x)
              (equal (sv::Svex-eval x env)
                     x))
     :hints (("Goal"
              :in-theory (e/d (sv::svex-quote->val sv::Svex-eval sv::4vec-p) ())))))

  (local
   (defthm svex-eval$-bitxor-lst-of-remove-equal
     (implies (member-equal x lst)
              (and (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst (remove-equal-once x lst) env)
                                           (sv::Svex-eval$ x env))
                          (svl::svex-eval$-bitxor-lst lst env))
                   (equal (sv::4vec-bitxor (sv::Svex-eval$ x env)
                                           (svl::svex-eval$-bitxor-lst (remove-equal-once x lst) env))
                          (svl::svex-eval$-bitxor-lst lst env))))
     :hints (("Goal"
              :induct (remove-equal-once x lst)
              :do-not-induct t
              :in-theory (e/d (remove-equal-once
                               svl::svex-eval$-bitxor-lst)
                              ())))))

  (local
   (defthm svex-eval$-bitand-lst-of-remove-equal
     (implies (member-equal x lst)
              (and (equal (sv::4vec-bitand (svl::svex-eval$-bitand-lst (remove-equal-once x lst) env)
                                           (sv::Svex-eval$ x env))
                          (svl::svex-eval$-bitand-lst lst env))
                   (equal (sv::4vec-bitand (sv::Svex-eval$ x env)
                                           (svl::svex-eval$-bitand-lst (remove-equal-once x lst) env))
                          (svl::svex-eval$-bitand-lst lst env))))
     :hints (("Goal"
              :induct (remove-equal-once x lst)
              :do-not-induct t
              :in-theory (e/d (remove-equal-once
                               svl::svex-eval$-bitand-lst)
                              ())))))

  (local
   (defthm svex-eval$-bitor-lst-of-remove-equal
     (implies (member-equal x lst)
              (and (equal (sv::4vec-bitor (svl::svex-eval$-bitor-lst (remove-equal-once x lst) env)
                                          (sv::Svex-eval$ x env))
                          (svl::svex-eval$-bitor-lst lst env))
                   (equal (sv::4vec-bitor (sv::Svex-eval$ x env)
                                          (svl::svex-eval$-bitor-lst (remove-equal-once x lst) env))
                          (svl::svex-eval$-bitor-lst lst env))))
     :hints (("Goal"
              :induct (remove-equal-once x lst)
              :do-not-induct t
              :in-theory (e/d (remove-equal-once
                               svl::svex-eval$-bitor-lst)
                              ())))))

  (local
   (defthmd 4vec-bitxor-introduce-new-var
     (implies (equal a b)
              (equal (sv::4vec-bitxor new a)
                     (sv::4vec-bitxor new b)))
     :hints ((bitops::logbitp-reasoning))))

  (local
   (defthmd 4vec-bitand-introduce-new-var
     (implies (equal a b)
              (equal (sv::4vec-bitand new a)
                     (sv::4vec-bitand new b)))
     :hints ((bitops::logbitp-reasoning))))

  (local
   (defthmd 4vec-bitor-introduce-new-var
     (implies (equal a b)
              (equal (sv::4vec-bitor new a)
                     (sv::4vec-bitor new b)))
     :hints ((bitops::logbitp-reasoning))))

  (local
   (defthm svex-eval$-bitxor-lst-of-remove-equal-2
     (implies (and (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst (remove-equal-once x lst) env)
                                           other)
                          other2)
                   (member-equal x lst))
              (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst lst env)
                                      other)
                     (sv::4vec-bitxor (svl::svex-eval$ x env) other2)))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :use ((:instance svex-eval$-bitxor-lst-of-remove-equal))
              :in-theory (e/d () (svex-eval$-bitxor-lst-of-remove-equal))))))

  (local
   (defthm svex-eval$-bitand-lst-of-remove-equal-2
     (implies (and (equal (sv::4vec-bitand (svl::svex-eval$-bitand-lst (remove-equal-once x lst) env)
                                           other)
                          other2)
                   (member-equal x lst))
              (equal (sv::4vec-bitand (svl::svex-eval$-bitand-lst lst env)
                                      other)
                     (sv::4vec-bitand (svl::svex-eval$ x env) other2)))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :use ((:instance svex-eval$-bitand-lst-of-remove-equal))
              :in-theory (e/d () (svex-eval$-bitand-lst-of-remove-equal))))))

  (local
   (defthm svex-eval$-bitor-lst-of-remove-equal-2
     (implies (and (equal (sv::4vec-bitor (svl::svex-eval$-bitor-lst (remove-equal-once x lst) env)
                                          other)
                          other2)
                   (member-equal x lst))
              (equal (sv::4vec-bitor (svl::svex-eval$-bitor-lst lst env)
                                     other)
                     (sv::4vec-bitor (svl::svex-eval$ x env) other2)))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :use ((:instance svex-eval$-bitor-lst-of-remove-equal))
              :in-theory (e/d () (svex-eval$-bitor-lst-of-remove-equal))))))

  (local
   (defthm bitxor-lemma
     (implies (and (equal (sv::4vec-bitxor a b)
                          (sv::4vec-bitxor x y))
                   (equal (sv::4vec-bitxor y 1z)
                          (sv::4vec-bitxor k m)))
              (equal (equal (sv::4vec-bitxor a (sv::4vec-bitxor b 1z))
                            (sv::4vec-bitxor x (sv::4vec-bitxor k m)))
                     t))))

  (local
   (defthm bitand-lemma
     (implies (and (equal (sv::4vec-bitand a b)
                          (sv::4vec-bitand x y))
                   (equal (sv::4vec-bitand y 1z)
                          (sv::4vec-bitand k m)))
              (equal (equal (sv::4vec-bitand a (sv::4vec-bitand b 1z))
                            (sv::4vec-bitand x (sv::4vec-bitand k m)))
                     t))))

  (local
   (defthm bitor-lemma
     (implies (and (equal (sv::4vec-bitor a b)
                          (sv::4vec-bitor x y))
                   (equal (sv::4vec-bitor y 1z)
                          (sv::4vec-bitor k m)))
              (equal (equal (sv::4vec-bitor a (sv::4vec-bitor b 1z))
                            (sv::4vec-bitor x (sv::4vec-bitor k m)))
                     t))))

  (local
   (defthm 3/4vec-p-of-svex-eval$-bitxor-lst
     (and (sv::3vec-p (svl::svex-eval$-bitxor-lst x env))
          (sv::4vec-p (svl::svex-eval$-bitxor-lst x env)))
     :hints (("goal"
              :in-theory (e/d (svl::svex-eval$-bitxor-lst) ())))))

  (local
   (defthm 3/4vec-p-of-svex-eval$-bitand-lst
     (and (sv::3vec-p (svl::svex-eval$-bitand-lst x env))
          (sv::4vec-p (svl::svex-eval$-bitand-lst x env)))
     :hints (("goal"
              :in-theory (e/d (svl::svex-eval$-bitand-lst) ())))))

  (local
   (defthm 3/4vec-p-of-svex-eval$-bitor-lst
     (and (sv::3vec-p (svl::svex-eval$-bitor-lst x env))
          (sv::4vec-p (svl::svex-eval$-bitor-lst x env)))
     :hints (("goal"
              :in-theory (e/d (svl::svex-eval$-bitor-lst) ())))))

  (defret <fn>-is-correct-for-bitxor
    (implies (equal bit-fn 'sv::Bitxor)
             (and (equal (sv::4vec-bitxor (sv::svex-eval$ res-svex env)
                                          (svl::svex-eval$-bitxor-lst to-remove-lst env))
                         (sv::4vec-bitxor (sv::svex-eval$ svex env)
                                          (svl::svex-eval$-bitxor-lst remaining-to-remove env)))
                  (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst to-remove-lst env)
                                          (sv::svex-eval$ res-svex env))
                         (sv::4vec-bitxor (sv::svex-eval$ svex env)
                                          (svl::svex-eval$-bitxor-lst remaining-to-remove env)))))
    :otf-flg t
    :hints (("Goal"
             :expand ((:free (args)
                             (sv::svex-apply 'sv::bitxor args)))
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-call->args
                              SV::SVEXLIST-EVAL$)
                             ()))))

  (defret <fn>-is-correct-for-bitand
    (implies (equal bit-fn 'sv::bitand)
             (and (equal (sv::4vec-bitand (sv::svex-eval$ res-svex env)
                                          (svl::svex-eval$-bitand-lst to-remove-lst env))
                         (sv::4vec-bitand (sv::svex-eval$ svex env)
                                          (svl::svex-eval$-bitand-lst remaining-to-remove env)))
                  (equal (sv::4vec-bitand (svl::svex-eval$-bitand-lst to-remove-lst env)
                                          (sv::svex-eval$ res-svex env))
                         (sv::4vec-bitand (sv::svex-eval$ svex env)
                                          (svl::svex-eval$-bitand-lst remaining-to-remove env)))))
    :otf-flg t
    :hints (("Goal"
             :expand ((:free (args)
                             (sv::svex-apply 'sv::bitand args)))
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-call->args
                              SV::SVEXLIST-EVAL$)
                             ()))))

  (defret <fn>-is-correct-for-bitor
    (implies (equal bit-fn 'sv::bitor)
             (and (equal (sv::4vec-bitor (sv::svex-eval$ res-svex env)
                                         (svl::svex-eval$-bitor-lst to-remove-lst env))
                         (sv::4vec-bitor (sv::svex-eval$ svex env)
                                         (svl::svex-eval$-bitor-lst remaining-to-remove env)))
                  (equal (sv::4vec-bitor (svl::svex-eval$-bitor-lst to-remove-lst env)
                                         (sv::svex-eval$ res-svex env))
                         (sv::4vec-bitor (sv::svex-eval$ svex env)
                                         (svl::svex-eval$-bitor-lst remaining-to-remove env)))))
    :otf-flg t
    :hints (("Goal"
             :expand ((:free (args)
                             (sv::svex-apply 'sv::bitor args)))
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-call->args
                              sv::svexlist-eval$)
                             ()))))

  (defret <fn>-is-correct-for-bitxor-2
    (implies (equal bit-fn 'sv::Bitxor)
             (and (equal (sv::4vec-bitxor (sv::svex-eval$ res-svex env)
                                          (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst to-remove-lst env)
                                                           other))
                         (sv::4vec-bitxor (sv::svex-eval$ svex env)
                                          (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst remaining-to-remove env)
                                                           other)))
                  (equal (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst to-remove-lst env)
                                          (sv::4vec-bitxor (sv::svex-eval$ res-svex env)
                                                           other))
                         (sv::4vec-bitxor (sv::svex-eval$ svex env)
                                          (sv::4vec-bitxor (svl::svex-eval$-bitxor-lst remaining-to-remove env)
                                                           other)))))
    :otf-flg t
    :hints (("Goal")))

  (defret <fn>-is-correct-for-bitand-2
    (implies (equal bit-fn 'sv::Bitand)
             (and (equal (sv::4vec-bitand (sv::svex-eval$ res-svex env)
                                          (sv::4vec-bitand (svl::svex-eval$-bitand-lst to-remove-lst env)
                                                           other))
                         (sv::4vec-bitand (sv::svex-eval$ svex env)
                                          (sv::4vec-bitand (svl::svex-eval$-bitand-lst remaining-to-remove env)
                                                           other)))
                  (equal (sv::4vec-bitand (svl::svex-eval$-bitand-lst to-remove-lst env)
                                          (sv::4vec-bitand (sv::svex-eval$ res-svex env)
                                                           other))
                         (sv::4vec-bitand (sv::svex-eval$ svex env)
                                          (sv::4vec-bitand (svl::svex-eval$-bitand-lst remaining-to-remove env)
                                                           other)))))
    :otf-flg t
    :hints (("Goal")))

  (defret <fn>-is-correct-for-bitor-2
    (implies (equal bit-fn 'sv::Bitor)
             (and (equal (sv::4vec-bitor (sv::svex-eval$ res-svex env)
                                         (sv::4vec-bitor (svl::svex-eval$-bitor-lst to-remove-lst env)
                                                         other))
                         (sv::4vec-bitor (sv::svex-eval$ svex env)
                                         (sv::4vec-bitor (svl::svex-eval$-bitor-lst remaining-to-remove env)
                                                         other)))
                  (equal (sv::4vec-bitor (svl::svex-eval$-bitor-lst to-remove-lst env)
                                         (sv::4vec-bitor (sv::svex-eval$ res-svex env)
                                                         other))
                         (sv::4vec-bitor (sv::svex-eval$ svex env)
                                         (sv::4vec-bitor (svl::svex-eval$-bitor-lst remaining-to-remove env)
                                                         other)))))
    :otf-flg t
    :hints (("Goal")))

  ;; measure lemmas:
  ;; not neaded as the caller of this function has a limit measure.
  #|(defret svex-count-of-<fn>
  (implies (or (equal bit-fn 'sv::bitand)
  (equal bit-fn 'sv::bitxor))
  (and (implies (equal remaining-to-remove to-remove-lst)
  (<= (sv::svex-count res-svex)
  (sv::svex-count svex)))
  (implies (not (equal remaining-to-remove to-remove-lst))
  (< (sv::svex-count res-svex)
  (sv::svex-count svex)))))
  :rule-classes (:rewrite :linear)
  :hints (("Goal"
  :in-theory (e/d (svex-apply$-for-bitxor-meta
  SV::SVEX-COUNT
  SV::SVEX-CALL->ARGS
  SV::SVEXlist-COUNT
  sv::Svex-kind)
  ()))))|#

  ;; (find-s-from-found-c-in-svex-aux-remove #!SV'(bitxor (bitxor a b) (bitxor c d)) #!SV'(a c))
  ;; ;; returns
  ;; ((SV::BITXOR SV::B SV::D) NIL)
  )

(define lst-to-bitxor/and-chain (lst
                                 &key
                                 ((bit-fn symbolp) 'bit-fn))
  :Returns (res sv::Svex-p :hyp (and (sv::svexlist-p lst)
                                     (or (equal bit-fn 'sv::bitand)
                                         (equal bit-fn 'sv::bitxor))))
  (if (atom lst)
      (if (eq bit-fn 'sv::bitand) -1 0)
    (if (atom (cdr lst))
        (car lst)
      (hons-list bit-fn (car lst)
                 (lst-to-bitxor/and-chain (cdr lst)))))
  ///
  (defret <fn>-correct-for-bitxor
    (implies (equal bit-fn 'sv::bitxor)
             (and (equal (sv::3vec-fix (sv::Svex-eval$ res env))
                         (svl::svex-eval$-bitxor-lst lst env))
                  (equal (sv::4vec-bitxor other (sv::Svex-eval$ res env))
                         (sv::4vec-bitxor other (svl::svex-eval$-bitxor-lst lst env)))
                  (equal (sv::4vec-bitxor (sv::Svex-eval$ res env) other)
                         (sv::4vec-bitxor other (svl::svex-eval$-bitxor-lst lst env)))))
    :hints (("Goal"
             :in-theory (e/d (SV::SVEX-CALL->FN
                              SV::SVEX-APPLY
                              SV::SVEX-CALL->args)
                             ()))))
  (defret <fn>-correct-for-bitand
    (implies (equal bit-fn 'sv::bitand)
             (and (equal (sv::3vec-fix (sv::Svex-eval$ res env))
                         (svl::svex-eval$-bitand-lst lst env))
                  (equal (sv::4vec-bitand other (sv::Svex-eval$ res env))
                         (sv::4vec-bitand other (svl::svex-eval$-bitand-lst lst env)))
                  (equal (sv::4vec-bitand (sv::Svex-eval$ res env) other)
                         (sv::4vec-bitand other (svl::svex-eval$-bitand-lst lst env)))))
    :hints (("Goal"
             :in-theory (e/d (SV::SVEX-CALL->FN
                              SV::SVEX-APPLY
                              SV::SVEX-CALL->args)
                             ())))))

(progn
  (local
   (defthm integerp-of-svex-eval$-bitxor-lst
     (implies (integer-listp (sv::svexlist-eval$ lst env))
              (integerp (svl::svex-eval$-bitxor-lst lst env)))
     :hints (("goal"
              :in-theory (e/d (svl::svex-eval$-bitxor-lst) ())))))

  (local
   (defthm integerp-of-svex-eval$-bitand-lst
     (implies (integer-listp (sv::svexlist-eval$ lst env))
              (integerp (svl::svex-eval$-bitand-lst lst env)))
     :hints (("goal"
              :in-theory (e/d (svl::svex-eval$-bitand-lst) ())))))

  (local
   (defthm integer-listp-of-svexlist-eval$-lemma
     (implies (and (integer-listp x))
              (integer-listp (sv::svexlist-eval$ x env)))
     :hints (("Goal"
              :in-theory (e/d (SV::SVEX-QUOTE->VAL) ()))))))

(define extract-from-unfloat ((x sv::svex-p))
  :returns (res sv::svex-p :hyp (sv::svex-p x))
  (case-match x
    (('sv::unfloat x)
     x)
    (& x)))

(progn
  (define already-parsed-svex-eval$-inv (alist env)
    :verify-guards nil
    (if (atom alist)
        (symbolp alist)
      (and (consp (car alist))
           (equal (sv::Svex-eval$ (caar alist) env)
                  (sv::Svex-eval$ (cdar alist) env))
           (already-parsed-svex-eval$-inv (cdr alist) env)))
    ///
    (defthm already-parsed-svex-eval$-inv-of-nil
      (implies (symbolp x)
               (equal (already-parsed-svex-eval$-inv x env) t)))

    (defthm already-parsed-svex-eval$-inv-of-cons
      (equal (already-parsed-svex-eval$-inv (cons (cons x y) rest) env)
             (and (equal (sv::Svex-eval$ x env)
                         (sv::Svex-eval$ y env))
                  (already-parsed-svex-eval$-inv rest env))))

    (defthm already-parsed-svex-eval$-inv-of-hons-assoc-equal
      (implies (and (HONS-ASSOC-EQUAL SVEX ALREADY-PARSED)
                    (already-parsed-svex-eval$-inv ALREADY-PARSED env))
               (equal (sv::Svex-eval$ (CDR (HONS-ASSOC-EQUAL SVEX ALREADY-PARSED)) env)
                      (sv::Svex-eval$ svex env)))))

  (define already-parsed-p (alist)
    (if (atom alist)
        (symbolp alist)
      (and (consp (car alist))
           (sv::Svex-p (caar alist))
           (sv::Svex-p (cdar alist))
           (already-parsed-p (cdr alist))))
    ///
    (defthm already-parsed-p-of-cons
      (equal (already-parsed-p (cons (cons x y) rest))
             (and (sv::Svex-p x)
                  (sv::Svex-p y)
                  (already-parsed-p rest))))

    (defthm already-parsed-p-of-hons-assoc-equal
      (implies (and (HONS-ASSOC-EQUAL SVEX ALREADY-PARSED)
                    (ALREADY-PARSED-P ALREADY-PARSED))
               (SV::SVEX-P (CDR (HONS-ASSOC-EQUAL SVEX ALREADY-PARSED)))))))

(defines find-s-from-found-c-in-svex-aux
  :verify-guards nil

  :prepwork ((Local
              (in-theory (enable sv::svex-call->fn)))

             (define find-s-from-found-c-in-svex-aux-counter ()
               nil
               ///
               (profile 'find-s-from-found-c-in-svex-aux-counter))

             (define svex-apply$-for-bitxor/and/or-meta2 (arg1 arg2
                                                               &key
                                                               ((bit-fn symbolp) 'bit-fn))
               :returns (res-svex sv::svex-p :hyp (and (force (sv::svex-p arg1))
                                                       (force (sv::svex-p arg2))))
               :inline t
               (b* ((res
                     (cond ((equal bit-fn 'sv::bitand)
                            (cond ((or (equal arg1 0)
                                       (equal arg2 0))
                                   0)
                                  ((equal arg1 -1)
                                   (create-unfloat-for-adder-fnc  arg2))
                                  ((equal arg2 -1)
                                   (create-unfloat-for-adder-fnc  arg1))
                                  (t (hons-list 'sv::bitand arg1 arg2))))
                           ((equal bit-fn 'sv::bitor)
                            (cond ((or (equal arg1 -1)
                                       (equal arg2 -1))
                                   -1)
                                  ((equal arg1 0)
                                   (create-unfloat-for-adder-fnc  arg2))
                                  ((equal arg2 0)
                                   (create-unfloat-for-adder-fnc  arg1))
                                  (t (hons-list 'sv::bitor arg1 arg2))))
                           (t
                            (cond ((equal arg1 0)
                                   (create-unfloat-for-adder-fnc  arg2))
                                  ((equal arg2 0)
                                   (create-unfloat-for-adder-fnc  arg1))
                                  (t (hons-list 'sv::bitxor arg1 arg2))))))
                    ;; TODO: clean ones in a better way here...
                    ;;(res (case-match res (('sv::bitxor 1 ('sv::bitxor 1 x)) x) (& res)))
                    )
                 res)
               ///
               (defret <fn>-is-correct
                 (implies (warrants-for-adder-pattern-match)
                          (equal (sv::svex-eval$ res-svex env)
                                 (cond ((equal bit-fn 'sv::bitand)
                                        (sv::4vec-bitand (sv::svex-eval$ arg1 env)
                                                         (sv::svex-eval$ arg2 env)))
                                       ((equal bit-fn 'sv::bitor)
                                        (sv::4vec-bitor (sv::svex-eval$ arg1 env)
                                                        (sv::svex-eval$ arg2 env)))
                                       (t
                                        (sv::4vec-bitxor (sv::svex-eval$ arg1 env)
                                                         (sv::svex-eval$ arg2 env))))))
                 :hints (("Goal"
                          :expand ((:free (args)
                                          (sv::svex-apply 'sv::bitxor args))
                                   (:free (args)
                                          (sv::svex-apply 'sv::bitand args))
                                   (:free (args)
                                          (sv::svex-apply 'sv::bitor args))
                                   (:free (args)
                                          (sv::svex-apply 'sv::unfloat args))
                                   (:free (x)
                                          (sv::4vec-bitor -1 x))
                                   (:free (x)
                                          (sv::3vec-bitor -1 x)))
                          :in-theory (e/d (sv::svex-call->fn
                                           sv::svex-call->args
                                           SV::SVEXLIST-EVAL$)
                                          ()))))

               )

             (define find-s-from-found-c-bitxor/and-args (args
                                                          &key
                                                          ((bit-fn symbolp) 'bit-fn))
               :returns (res sv::svex-p :hyp (and (force (sv::Svexlist-p args))
                                                  (or (equal bit-fn 'sv::bitand)
                                                      (equal bit-fn 'sv::bitor)
                                                      (equal bit-fn 'sv::bitxor))))
               (cond
                ((atom args)
                 (if (equal bit-fn 'sv::bitand) -1 0))
                ((atom (cdr args))
                 (create-unfloat-for-adder-fnc (car args)))
                ((atom (cddr args))
                 (hons-list bit-fn
                            (car args)
                            (cadr args)))
                (t
                 (hons-list bit-fn
                            (find-s-from-found-c-bitxor/and-args (cdr args))
                            (car args))))
               ///
               (defret <fn>-is-correct
                 (implies (warrants-for-adder-pattern-match)
                          (and (implies (equal bit-fn 'sv::bitand)
                                        (equal (sv::Svex-eval$ res env)
                                               (svl::svex-eval$-bitand-lst args env)))
                               (implies (equal bit-fn 'sv::bitxor)
                                        (equal (sv::Svex-eval$ res env)
                                               (svl::svex-eval$-bitxor-lst args env)))
                               (implies (equal bit-fn 'sv::bitor)
                                        (equal (sv::Svex-eval$ res env)
                                               (svl::svex-eval$-bitor-lst args env)))))
                 :hints (("Goal"
                          :in-theory (e/d (SV::SVEX-CALL->FN
                                           SV::SVEX-CALL->args
                                           SV::SVEX-APPLY)
                                          ()))))))

  (define find-s-from-found-c-in-svex-aux ((svex sv::svex-p)
                                           (exploded-args-and-args-alist exploded-args-and-args-alist-p)
                                           &key
                                           ((already-parsed already-parsed-p) 'already-parsed)
                                           ((adder-type symbolp) 'adder-type)
                                           ((config svl::svex-reduce-config-p) 'config)
                                           ((column acl2::maybe-integerp) 'column)
                                           ((limit natp) 'limit))
    ;;:measure (sv::Svex-count svex)
    :measure (nfix limit)
    :returns (mv (res)
                 (res-already-parsed))
    :no-function t
    (if (zp limit) ;; proving the measure is not easy so I will use memoize-partial
        (mv svex already-parsed)
      (let ((limit (1- limit)))
        (sv::svex-case
         svex
         :quote (mv svex already-parsed)
         :var   (mv svex already-parsed)
         :call
         (b* ((parsed? (hons-get svex already-parsed))
              ((when parsed?)
               (mv (cdr parsed?) already-parsed))
              ((when (and*-exec column
                                (eq svex.fn 'sv::concat)
                                (svl::equal-len svex.args 3)
                                (natp (first svex.args))))
               (b* ((size (first svex.args))
                    ((mv second already-parsed)
                     (find-s-from-found-c-in-svex-aux (second svex.args) exploded-args-and-args-alist))
                    ((mv third already-parsed)
                     (find-s-from-found-c-in-svex-aux (third svex.args) exploded-args-and-args-alist
                                                      :column (+ column size)))
                    (res (hons-list 'sv::concat size second third)))
                 (mv res
                     (hons-acons svex res already-parsed))))

              ((unless (cond ((eq adder-type 'ha-c) (bitand-pattern-p svex))
                             ((eq adder-type 'ha+1-c) (bitor-pattern-p svex))
                             (t (bitxor-pattern-p svex))))
               (b* (;; bitand  and bitor is likely a part  of carry logic. This
                    ;; will  mess up  with column  calculation.  So  let's just
                    ;; increase column a lot so it gets thrown away.
                    ((when (and*-exec column
                                      (member-eq svex.fn '(sv::bitand sv::bitor))))
                     (mv svex already-parsed))
                    ;; under a carry, we will know to be checking a previous column.
                    ;; this is not a great system though...
                    (column (and*-exec column
                                       (- column
                                          (acl2::bool->bit
                                           (member-eq svex.fn '(ha-c-chain fa-c-chain ha+1-c-chain))))))
                    ((mv args already-parsed)
                     (find-s-from-found-c-in-svexlist-aux svex.args exploded-args-and-args-alist))
                    (res (sv::svex-call svex.fn args)))
                 (mv res (hons-acons svex res already-parsed))))

              (bit-fn svex.fn)

              ;; first see if anything in the xor chain appears as an argument to an orphan fa-c
              ;; explore1-res will be list of all 3 args. or 2 args if working for ha-c
              ((exploded-args-and-args x)
               (find-s-from-found-c-in-svex-aux-explore svex exploded-args-and-args-alist nil))

              ((unless (and*-exec x.args x.exploded-args))
               (b* (((mv args already-parsed)
                     (find-s-from-found-c-in-svexlist-aux svex.args exploded-args-and-args-alist))
                    (res (sv::svex-call svex.fn args)))
                 (mv res (hons-acons svex res already-parsed))))

              ((mv rest-bitxor/and remaining-exploded-args)
               (find-s-from-found-c-in-svex-aux-remove svex x.exploded-args))

              ((unless (and*-exec
                        (implies (equal adder-type 'ha-c) ;; do not allow borrowing elements for ha-c..
                                 (not remaining-exploded-args))
                        (implies (equal adder-type 'ha+1-c) ;; do not allow borrowing elements for ha+1-c..
                                 (not remaining-exploded-args))
                        (integer-listp remaining-exploded-args)

                        ;; what that extra elements are allowed os controlled in find-s-from-found-c-in-svex-aux-explore2
                        ;; restriction is integer-listp because only then repeated elements in bitxor are simplified away to 0.
                        ))
               ;; this should never happend (hopefully?)
               (b* (((mv args already-parsed)
                     (find-s-from-found-c-in-svexlist-aux svex.args exploded-args-and-args-alist))
                    (res (sv::svex-call svex.fn args)))
                 (mv res (hons-acons svex res already-parsed))))

              (rest-bitxor/and (if remaining-exploded-args
                                   (svex-apply$-for-bitxor/and/or-meta2
                                    ;; 1 comes from the only allowed value of remaining-exploded-args.
                                    ;; possibly, this can be extended to anything..
                                    (lst-to-bitxor/and-chain remaining-exploded-args)
                                    rest-bitxor/and)
                                 rest-bitxor/and))

              (- (find-s-from-found-c-in-svex-aux-counter))
              ((mv rest1 already-parsed)
               (find-s-from-found-c-in-svex-aux rest-bitxor/and exploded-args-and-args-alist))
              ((mv args already-parsed)
               (find-s-from-found-c-in-svexlist-aux x.args exploded-args-and-args-alist))
              (result
               (svex-apply$-for-bitxor/and/or-meta2 rest1 (find-s-from-found-c-bitxor/and-args args))))
           (mv result (hons-acons svex result already-parsed)))))))

  (define find-s-from-found-c-in-svexlist-aux ((lst sv::Svexlist-p)
                                               (exploded-args-and-args-alist
                                                exploded-args-and-args-alist-p)
                                               &key
                                               ((already-parsed already-parsed-p) 'already-parsed)
                                               ((adder-type symbolp) 'adder-type)
                                               ((config svl::svex-reduce-config-p) 'config)
                                               ((column acl2::maybe-integerp) 'column)
                                               ((limit natp) 'limit))
    ;;:measure (sv::svexlist-count lst)
    :measure (nfix limit)
    :returns (mv (res-lst)
                 (res-already-parsed))
    :no-function t
    (if (zp limit) ;; proving the measure is not easy so I will use memoize-partial
        (mv lst already-parsed)
      (let ((limit (1- limit)))
        (if (atom lst)
            (mv nil already-parsed)
          (b* (((mv cur already-parsed) (find-s-from-found-c-in-svex-aux (car lst) exploded-args-and-args-alist))
               ((mv res already-parsed) (find-s-from-found-c-in-svexlist-aux (cdr lst) exploded-args-and-args-alist)))
            (mv (hons cur res) already-parsed))))))
  ///

  (local
   (in-theory (disable acl2::bool->bit
                       MEMBER-EQUAL)))

  (defret-mutual return-type-of-<fn>
    (defret return-type-of-<fn>
      (implies (and (sv::Svex-p svex)
                    (exploded-args-and-args-alist-p exploded-args-and-args-alist)
                    (already-parsed-p already-parsed))
               (and (sv::svex-p res)
                    (already-parsed-p res-already-parsed)))
      :fn find-s-from-found-c-in-svex-aux)
    (defret return-type-of-<fn>
      (implies (and (sv::Svexlist-p lst)
                    (exploded-args-and-args-alist-p exploded-args-and-args-alist)
                    (already-parsed-p already-parsed))
               (and (sv::Svexlist-p res-lst)
                    (already-parsed-p res-already-parsed)))
      :fn find-s-from-found-c-in-svexlist-aux))

  (local
   (defthm bitxor-pattern-of-svex-call-of-bitxor
     (bitxor-pattern-p (sv::svex-call 'sv::bitxor
                                      (list x y)))
     :hints (("Goal"
              :in-theory (e/d (SV::SVEX-CALL bitxor-pattern-p) ())))))

  (local
   (defthm bitand-pattern-of-svex-call-of-bitxor
     (bitand-pattern-p (sv::svex-call 'sv::bitand
                                      (list x y)))
     :hints (("Goal"
              :in-theory (e/d (SV::SVEX-CALL bitand-pattern-p) ())))))

  (local
   (defthm bitor-pattern-of-svex-call-of-bitor
     (bitor-pattern-p (sv::svex-call 'sv::bitor (list x y)))
     :hints (("Goal"
              :in-theory (e/d (sv::svex-call bitor-pattern-p) ())))))

  (verify-guards find-s-from-found-c-in-svex-aux-fn
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ()))))

  ;;(memoize 'find-s-from-found-c-in-svex-aux-fn :condition '(eq (sv::svex-kind svex) :call))

  #|(acl2::memoize-partial
  ((find-s-from-found-c-in-svex-aux* find-s-from-found-c-in-svex-aux-fn)
  (find-s-from-found-c-in-svexlist-aux* find-s-from-found-c-in-svexlist-aux-fn
  :condition nil)))|#

  (local
   (include-book "std/basic/inductions" :DIR :SYSTEM))

  (local
   (defthmd svex-eval$-bitxor-lst-when-svexlist-evals-are-equal
     (implies (and (equal (sv::Svexlist-eval$ lst1 env)
                          (sv::Svexlist-eval$ lst2 env))
                   (syntaxp (not (lexorder lst2 lst1))))
              (equal (svl::svex-eval$-bitxor-lst lst1 env)
                     (svl::svex-eval$-bitxor-lst lst2 env)))
     :hints (("Goal"
              :induct (acl2::cdr-cdr-induct lst1 lst2)
              :do-not-induct t
              :expand ((SV::SVEXLIST-EVAL$ LST2 ENV))
              :in-theory (e/d (sv::Svexlist-eval$
                               svl::svex-eval$-bitxor-lst)
                              ())))))

  (local
   (defthmd svex-eval$-bitand-lst-when-svexlist-evals-are-equal
     (implies (and (equal (sv::Svexlist-eval$ lst1 env)
                          (sv::Svexlist-eval$ lst2 env))
                   (syntaxp (not (lexorder lst2 lst1))))
              (equal (svl::svex-eval$-bitand-lst lst1 env)
                     (svl::svex-eval$-bitand-lst lst2 env)))
     :hints (("Goal"
              :induct (acl2::cdr-cdr-induct lst1 lst2)
              :do-not-induct t
              :expand ((SV::SVEXLIST-EVAL$ LST2 ENV))
              :in-theory (e/d (sv::Svexlist-eval$
                               svl::svex-eval$-bitand-lst)
                              ())))))

  (local
   (defthmd svex-eval$-bitor-lst-when-svexlist-evals-are-equal
     (implies (and (equal (sv::Svexlist-eval$ lst1 env)
                          (sv::Svexlist-eval$ lst2 env))
                   (syntaxp (not (lexorder lst2 lst1))))
              (equal (svl::svex-eval$-bitor-lst lst1 env)
                     (svl::svex-eval$-bitor-lst lst2 env)))
     :hints (("Goal"
              :induct (acl2::cdr-cdr-induct lst1 lst2)
              :do-not-induct t
              :expand ((sv::svexlist-eval$ lst2 env))
              :in-theory (e/d (sv::Svexlist-eval$
                               svl::svex-eval$-bitor-lst)
                              ())))))

  (local
   (defret svex-eval$-bitxor-lst-when-svexlist-evals-are-equal-special
     (implies (equal (sv::svexlist-eval$ res-lst env)
                     (sv::svexlist-eval$ lst env))
              (equal (svl::svex-eval$-bitxor-lst res-lst env)
                     (svl::svex-eval$-bitxor-lst lst env)))
     :fn find-s-from-found-c-in-svexlist-aux
     :hints (("Goal"
              :in-theory (e/d (svex-eval$-bitxor-lst-when-svexlist-evals-are-equal) ())))))

  (local
   (defret svex-eval$-bitand-lst-when-svexlist-evals-are-equal-special
     (implies (equal (sv::svexlist-eval$ res-lst env)
                     (sv::svexlist-eval$ lst env))
              (equal (svl::svex-eval$-bitand-lst res-lst env)
                     (svl::svex-eval$-bitand-lst lst env)))
     :fn find-s-from-found-c-in-svexlist-aux
     :hints (("Goal"
              :in-theory (e/d (svex-eval$-bitand-lst-when-svexlist-evals-are-equal) ())))))

  (local
   (defret svex-eval$-bitor-lst-when-svexlist-evals-are-equal-special
     (implies (equal (sv::svexlist-eval$ res-lst env)
                     (sv::svexlist-eval$ lst env))
              (equal (svl::svex-eval$-bitor-lst res-lst env)
                     (svl::svex-eval$-bitor-lst lst env)))
     :fn find-s-from-found-c-in-svexlist-aux
     :hints (("Goal"
              :in-theory (e/d (svex-eval$-bitor-lst-when-svexlist-evals-are-equal) ())))))

  (defret-mutual <fn>-correct
    (defret <fn>-is-correct
      (implies (and (force (sv::svex-p svex))
                    (force (warrants-for-adder-pattern-match))
                    (force (exploded-args-and-args-alist-p exploded-args-and-args-alist))
                    (force (exploded-args-and-args-alist-inv
                            exploded-args-and-args-alist env
                            :bit-fn (cond ((equal adder-type 'ha-c) 'sv::bitand)
                                          ((equal adder-type 'ha+1-c) 'sv::bitor)
                                          (t 'sv::bitxor))))
                    (force (already-parsed-svex-eval$-inv already-parsed env))
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    )
               (and (equal (sv::svex-eval$ res env)
                           (sv::svex-eval$ svex env))
                    (already-parsed-svex-eval$-inv res-already-parsed env)))
      :fn find-s-from-found-c-in-svex-aux)
    (defret <fn>-is-correct
      (implies (and (force (sv::svexlist-p lst))
                    (force (warrants-for-adder-pattern-match))
                    (force (exploded-args-and-args-alist-p exploded-args-and-args-alist))
                    (force (exploded-args-and-args-alist-inv
                            exploded-args-and-args-alist
                            env
                            :bit-fn (cond ((equal adder-type 'ha-c) 'sv::bitand)
                                          ((equal adder-type 'ha+1-c) 'sv::bitor)
                                          (t 'sv::bitxor))))
                    (force (already-parsed-svex-eval$-inv already-parsed env))
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config)))
               (and (equal (sv::svexlist-eval$ res-lst env)
                           (sv::svexlist-eval$ lst env))
                    (already-parsed-svex-eval$-inv res-already-parsed env)))
      :fn find-s-from-found-c-in-svexlist-aux)
    :otf-flg t
    :hints (("goal"
             :expand ((:free (x) (sv::svex-apply$ 'fa-s-chain x))
                      (:free (x) (sv::svex-apply$ 'ha-c-chain x))
                      (:free (x) (sv::svex-apply$ 'sv::bitxor x))
                      (:free (x) (sv::svex-apply 'sv::bitxor x))
                      (:free (x) (sv::svex-apply 'sv::bitor x))
                      (:free (x) (sv::svex-apply 'sv::bitand x))
                      (sv::svexlist-eval$ (cdr svex) env)
                      (sv::svexlist-eval$ (cddr svex) env)
                      (find-s-from-found-c-in-svexlist-aux  lst exploded-args-and-args-alist)
                      (find-s-from-found-c-in-svex-aux  svex exploded-args-and-args-alist)
                      )
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-call->args
                              sv::svexlist-eval$
                              fa-s-chain
                              ha-c-chain
                              ACL2::MERGE-SORT-LEXORDER
                              ACL2::MERGE-LEXORDER)
                             (integer-listp
                              sv::svexlist-eval$-when-consp
                              acl2::integer-listp-of-cons))))))

(define find-s-from-found-c-in-svex-alist-aux ((alist sv::svex-alist-p)
                                               (exploded-args-and-args-alist exploded-args-and-args-alist-p)
                                               &key
                                               ((already-parsed already-parsed-p) ''find-s-from-found-c-in-svex-alist-aux)
                                               ((adder-type symbolp) 'adder-type)
                                               (track-column? 'track-column?)
                                               ((config svl::svex-reduce-config-p) 'config))
  :returns (mv res res-already-parsed)
  :verify-guards nil
  (if (atom alist)
      (mv nil (progn$ ;; (cw "(len already-parsed): ~p0~%" (len already-parsed))
               ;; (cw "(len cleaned already-parsed): ~p0~%" (len (fast-alist-clean already-parsed)))
               (fast-alist-free already-parsed)))
    (b* ((column (and track-column? 0))
         ((mv x already-parsed)
          (find-s-from-found-c-in-svex-aux (cdar alist) exploded-args-and-args-alist :limit (expt 2 20)))
         ((mv rest already-parsed)
          (find-s-from-found-c-in-svex-alist-aux (cdr alist) exploded-args-and-args-alist :already-parsed already-parsed)))
      (mv (acons (caar alist) x rest) already-parsed)))
  ///

  (defret return-val-of-<fn>
    (implies (and (sv::Svex-alist-p alist)
                  (exploded-args-and-args-alist-p exploded-args-and-args-alist)
                  (already-parsed-p already-parsed))
             (and (sv::Svex-alist-p res)
                  (alistp res)
                  (already-parsed-p res-already-parsed))))

  (verify-guards find-s-from-found-c-in-svex-alist-aux-fn)

  (defret <fn>-is-correct
    (implies (and (force (sv::svex-alist-p alist))
                  (force (warrants-for-adder-pattern-match))
                  (force (exploded-args-and-args-alist-p exploded-args-and-args-alist))
                  (force (exploded-args-and-args-alist-inv
                          exploded-args-and-args-alist env
                          :bit-fn (cond ((equal adder-type 'ha-c) 'sv::bitand)
                                        ((equal adder-type 'ha+1-c) 'sv::bitor)
                                        (t 'sv::bitxor))))
                  (force (already-parsed-svex-eval$-inv already-parsed env))
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config)))
             (and (equal (sv::svex-alist-eval$ res env)
                         (sv::svex-alist-eval$ alist env))
                  (already-parsed-svex-eval$-inv res-already-parsed env)))
    :hints (("Goal"
             :in-theory (e/d (sv::svex-alist-eval$) ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection alistp-of-of-fast-alist-clean
  (defthm alistp-of-of-fast-alist-fork
    (implies (and (alistp x)
                  (alistp last))
             (alistp (fast-alist-fork x last))))

  (defthm alistp-of-last
    (implies (alistp x)
             (alistp (last x))))

  (defthm alistp-of-cdr
    (implies (alistp x)
             (alistp (cdr x))))

  (defthm alistp-of-of-fast-alist-clean
    (implies (force (alistp x))
             (alistp (fast-alist-clean x)))))

(defsection pattern-alist-p-of-of-fast-alist-clean
  (defthm pattern-alist-p-of-of-fast-alist-fork
    (implies (and (pattern-alist-p x)
                  (pattern-alist-p last))
             (pattern-alist-p (fast-alist-fork x last))))

  (defthm pattern-alist-p-of-last
    (implies (pattern-alist-p x)
             (pattern-alist-p (last x))))

  (defthm pattern-alist-p-of-cdr
    (implies (pattern-alist-p x)
             (pattern-alist-p (cdr x))))

  (defthm pattern-alist-p-of-of-fast-alist-clean
    (implies (force (pattern-alist-p x))
             (pattern-alist-p (fast-alist-clean x)))))

;; (bitand/or/xor-cancel-repeated fn term1 term2)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection simplify-to-find-fa-c-patterns

  ;; Goal is to attempting to simplify  svexes locally until they reveal a fa-c
  ;; pattern. If it does, then simplification  is left and the found pattern is
  ;; wrapped with "ID"  svex-op in order to prevent  other simplifications from
  ;; messing with it.

  (defconst *simplify-to-find-fa-c-patterns-limit*
    8)

  ;; memoizing this helps a little because of repetitive work
  (memoize 'svl::bitand/or/xor-cancel-repeated)

  (define simplify-to-find-fa-c-patterns-aux ((x sv::Svex-p)
                                              (limit natp)
                                              &key
                                              ((strength integerp) 'strength)
                                              (skip 'nil)
                                              ((skip-arg natp) '0)
                                              (inside-out 'inside-out)
                                              ((env) 'env)
                                              ((context rp-term-listp) 'context)
                                              ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (res sv::svex-p :hyp (sv::svex-p x))
                 there-is-more)
    :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
    :measure (acl2::nat-list-measure (list limit (if skip 0 1)))
    :verify-guards :after-returns
    :guard-debug t
    (if (zp limit)
        (mv x t)
      (sv::svex-case
       x
       :var (mv x nil)
       :quote (mv x nil)
       :call
       (cond ((and (or (equal x.fn 'sv::bitor)
                       (equal x.fn 'sv::bitand)
                       (equal x.fn 'sv::bitxor))
                   (svl::equal-len x.args 2))
              (b* (((when (and (not skip)
                               (not inside-out)
                               (= skip-arg 0)))
                    (let* ((new-x (svl::bitand/or/xor-cancel-repeated
                                   x.fn (first x.args) (second x.args)
                                   :leave-depth strength
                                   :nodes-to-skip-alist nil)))
                      (simplify-to-find-fa-c-patterns-aux new-x limit :skip t)))

                   ((mv arg1 there-is-more1)
                    (if (= skip-arg 1)
                        (mv (first x.args) nil)
                      (simplify-to-find-fa-c-patterns-aux (first x.args) (1- limit))))
                   ((mv arg2 there-is-more2)
                    (if (= skip-arg 2)
                        (mv (second x.args) nil)
                      (simplify-to-find-fa-c-patterns-aux (second x.args) (1- limit))))
                   (new-x (ex-adder-fnc-from-unfloat
                           (if (and inside-out
                                    (= skip-arg 0))
                               (svl::bitand/or/xor-cancel-repeated
                                x.fn arg1 arg2
                                :leave-depth strength
                                :nodes-to-skip-alist nil)
                             (svl::bitand/or/xor-simple-constant-simplify
                              x.fn arg1 arg2 :config config)))))
                (mv new-x (or there-is-more1
                              there-is-more2))))
             (t (mv x nil)))))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-p x)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (warrants-for-adder-pattern-match))
               (equal
                (sv::svex-eval$ res (rp-evlt env-term a))
                (sv::svex-eval$ x (rp-evlt env-term a))))
      :hints (("Goal"
               :in-theory (e/d (sv::svex-call->args
                                SV::SVEX-CALL->fn
                                SV::SVEX-APPLY)
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux))))))

  (define simplify-to-find-fa-c-patterns-iter ((x sv::Svex-p)
                                               (limit natp)
                                               &key
                                               ((strength integerp) 'strength)
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
    :guard (and (<= limit *simplify-to-find-fa-c-patterns-limit*)
                (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config)))
    :returns (mv (new-x sv::svex-p :hyp (sv::svex-p x))
                 (found))
    :prepwork ((local
                (use-arithmetic-5 t)))
    (if (zp limit)
        (mv x nil)
      (b* (((mv simplified there-is-more1)
            (simplify-to-find-fa-c-patterns-aux
             x (+ *simplify-to-find-fa-c-patterns-limit* (- limit) 1)
             :inside-out nil))
           ((when (equal simplified x))
            (simplify-to-find-fa-c-patterns-iter x (1- limit)))
           (fa-c-patterns (look-for-fa-c-chain-pattern simplified))

           #|(- (and (case-match x (('sv::bitor
           ('sv::bitand
           ('sv::bitxor 1 ('sv::?* . &))
           ('sv::bitxor ('sv::bitxor . &) &))
           &)
           t))
           (cwe "x: ~p0, simplified: ~p1, fa-c-patterns: ~p2~%"
           x simplified fa-c-patterns)))|#

           ((when fa-c-patterns)
            (mv simplified t))

           #|((unless (aggressive-find-adders-in-svex))
           (if there-is-more1
           (mv simplified nil)
           (simplify-to-find-fa-c-patterns-iter x (1- limit))))|#

           ;; Try also simplifying from inside-out
           ((mv simplified there-is-more2)
            (simplify-to-find-fa-c-patterns-aux
             x (+ *simplify-to-find-fa-c-patterns-limit* (- limit) 1)
             :inside-out t))
           (fa-c-patterns (look-for-fa-c-chain-pattern simplified))
           ((when fa-c-patterns)
            (mv simplified t))

           ;; Another attempt but this time skip one of the bitor args.
           ((mv simplified &)
            (simplify-to-find-fa-c-patterns-aux
             x (+ *simplify-to-find-fa-c-patterns-limit* (- limit) 1)
             :inside-out t
             :skip-arg 1))
           (fa-c-patterns (look-for-fa-c-chain-pattern simplified))
           ((when fa-c-patterns)
            (mv simplified t))

           ;;; Now skip simplification of the other arg.
           ((mv simplified &)
            (simplify-to-find-fa-c-patterns-aux
             x (+ *simplify-to-find-fa-c-patterns-limit* (- limit) 1)
             :inside-out t
             :skip-arg 2))
           (fa-c-patterns (look-for-fa-c-chain-pattern simplified))
           ((when fa-c-patterns)
            (mv simplified t))

           ((unless (or there-is-more1 there-is-more2))
            (mv simplified nil)))
        (simplify-to-find-fa-c-patterns-iter x (1- limit))))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-p x)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (warrants-for-adder-pattern-match))
               (equal
                (sv::svex-eval$ new-x (rp-evlt env-term a))
                (sv::svex-eval$ x (rp-evlt env-term a))))
      :fn simplify-to-find-fa-c-patterns-iter
      :hints (("Goal"
               :expand ((simplify-to-find-fa-c-patterns-iter x limit))
               :in-theory (e/d (simplify-to-find-fa-c-patterns-iter)
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux))))))

  (defines simplify-to-find-fa-c-patterns
    :verify-guards nil
    (define simplify-to-find-fa-c-patterns ((x sv::Svex-p)
                                            &key
                                            ((strength integerp) 'strength)
                                            ((env) 'env)
                                            ((context rp-term-listp) 'context)
                                            ((config svl::svex-reduce-config-p) 'config))
      :measure (sv::svex-count x)
      :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
      :returns (res sv::svex-p :hyp (sv::svex-p x))
      (sv::svex-case
       x
       :var x
       :quote x
       :call
       (b* ((x.args (simplify-to-find-fa-c-patterns-list x.args))
            (x (sv::svex-call x.fn x.args))
            ((unless (equal x.fn 'sv::bitor)) ;; no need to look for fa-c patterns if x is not bitor.
             x)
            ((mv new-x found)
             (simplify-to-find-fa-c-patterns-iter x
                                                  *simplify-to-find-fa-c-patterns-limit*))

            ;; (& (and (not found)
            ;;         (case-match x
            ;;           (('sv::bitor ('sv::bitand x ('sv::bitxor 1 ('sv::bitxor x z)))
            ;;                        ('sv::bitand & ('sv::bitxor x z)))
            ;;            (list x z)))
            ;;         (cwe "WARNING!!! A known fa-c pattern is missed. For x: ~p0. New-x: ~p1" x new-x)))

            )
         ;; wrapping with id so that other simplification attempts do not corrupt this found pattern.
         (if found
             (sv::svex-call 'sv::id (hons-list new-x))
           x))))

    (define simplify-to-find-fa-c-patterns-list ((lst sv::Svexlist-p)
                                                 &key
                                                 ((strength integerp) 'strength)
                                                 ((env) 'env)
                                                 ((context rp-term-listp) 'context)
                                                 ((config svl::svex-reduce-config-p) 'config))
      :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
      :measure (sv::svexlist-count lst)
      :returns (res sv::svexlist-p :hyp (sv::svexlist-p lst))
      (if (atom lst)
          nil
        (hons (simplify-to-find-fa-c-patterns (car lst))
              (simplify-to-find-fa-c-patterns-list (cdr lst)))))
    ///
    (verify-guards simplify-to-find-fa-c-patterns-fn)

    (memoize 'simplify-to-find-fa-c-patterns-fn
             ;; :condition '(eq (sv::svex-kind x) :call)
             )

    (local
     (defthm id-of-bitor-lemma
       (equal (sv::svex-apply 'id (list (sv::svex-apply 'sv::bitor args)))
              (sv::svex-apply 'sv::bitor args))
       :hints (("Goal"
                :in-theory (e/d (sv::svex-apply) ())))))

    (defret-mutual svex-eval$-correctness
      (defret <fn>-is-correct
        (implies (and (sv::svex-p x)
                      (rp::rp-term-listp context)
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (warrants-for-adder-pattern-match))
                 (equal
                  (sv::svex-eval$ res (rp-evlt env-term a))
                  (sv::svex-eval$ x (rp-evlt env-term a))))
        :fn simplify-to-find-fa-c-patterns)
      (defret <fn>-is-correct
        (implies (and (sv::svexlist-p lst)
                      (rp::rp-term-listp context)
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (warrants-for-adder-pattern-match))
                 (equal
                  (sv::svexlist-eval$ res (rp-evlt env-term a))
                  (sv::svexlist-eval$ lst (rp-evlt env-term a))))
        :fn simplify-to-find-fa-c-patterns-list)
      :mutual-recursion simplify-to-find-fa-c-patterns
      :hints (("Goal"
               :in-theory (e/d ()
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux))))))

  (define simplify-to-find-fa-c-patterns-alist ((alist sv::Svex-alist-p)
                                                &key
                                                ((strength integerp) 'strength)
                                                ((env) 'env)
                                                ((context rp-term-listp) 'context)
                                                ((config svl::svex-reduce-config-p) 'config))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
    :guard (not (svl::svex-reduce-config->skip-bitor/and/xor-repeated config))
    (if (atom alist)
        nil
      (acons (caar alist)
             (simplify-to-find-fa-c-patterns (hons-copy (cdar alist)))
             (simplify-to-find-fa-c-patterns-alist (cdr alist))))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-alist-p alist)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (warrants-for-adder-pattern-match))
               (equal
                (sv::svex-alist-eval$ res (rp-evlt env-term a))
                (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
      :fn simplify-to-find-fa-c-patterns-alist
      :hints (("Goal"
               :in-theory (e/d (sv::svex-alist-eval$)
                               (eval-and-all
                                rp::rp-term-listp
                                falist-consistent-aux)))))))

;; (rp::simplify-to-find-fa-c-patterns #!SV'(bitxor other
;;                                                  (bitor (bitor (bitand x y) (bitor (bitand x y) (bitand y z)))
;;                                                         (bitand x z)))
;;                                     :context nil
;;                                     :env nil
;;                                     :config nil)
;; ;; returns:
;; (BITXOR OTHER
;;         (ID (BITOR (BITOR (BITAND X Y) (BITAND Y Z))
;;                    (BITAND X Z))))

(progn
  (define count-newly-found-adders-in-pattern-alist-aux (fn-lst adder-type (full-lst true-listp))
    ;; look for a pair of ha with the same column value.
    (if (atom fn-lst)
        nil
      (b* ((x (car fn-lst))
           ((unless (consp x))
            (count-newly-found-adders-in-pattern-alist-aux (cdr fn-lst) adder-type full-lst))
           (fn (car x))
           (column (cdr x))
           ((when (and (eq adder-type 'ha)
                       (or (and (eq fn 'ha-c-chain)
                                (member-equal (cons 'ha-s-chain column)
                                              full-lst))
                           (and (eq fn 'ha-s-chain)
                                (member-equal (cons 'ha-c-chain column)
                                              full-lst))
                           (and (eq fn 'ha+1-c-chain)
                                (member-equal (cons 'ha+1-s-chain column)
                                              full-lst))
                           (and (eq fn 'ha+1-s-chain)
                                (member-equal (cons 'ha+1-c-chain column)
                                              full-lst)))))
            t))
        (count-newly-found-adders-in-pattern-alist-aux (cdr fn-lst) adder-type full-lst))))

  (define count-newly-found-adders-in-pattern-alist ((pattern-alist pattern-alist-p)
                                                     &key
                                                     (track-column? 'track-column?)
                                                     ((adder-type symbolp) 'adder-type))
    (if (atom pattern-alist)
        0
      (+ (b* ((fn-list (cdar pattern-alist)))
           (if (cond (track-column?
                      (and (member-eq :new fn-list)
                           (count-newly-found-adders-in-pattern-alist-aux fn-list adder-type fn-list)))
                     ((eq adder-type 'ha)
                      (or (subsetp-eq '(:new ha-c-chain ha-s-chain)
                                      fn-list)
                          (subsetp-eq '(:new ha+1-c-chain ha+1-s-chain)
                                      fn-list)))
                     ((eq adder-type 'fa)
                      (subsetp-eq '(:new fa-c-chain)
                                  fn-list)))
               1 0))
         (count-newly-found-adders-in-pattern-alist (cdr pattern-alist))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Try  to wrap  booth encoding  logic (partial  products) with  ID to  prevent
;; oversimplification.  Strategy: Look for  half-adder patters. Likely (but not
;; guaranteed), the  partial products will  first end  up in shared  bitand and
;; bitxor logic.

(defines wrap-pp-with-id-aux
  :verify-guards nil
  (define wrap-pp-with-id-aux ((x sv::svex-p)
                               (args-alist alistp))
    :returns (mv (res sv::svex-p :hyp (sv::svex-p x))
                 wrapped)
    :measure (sv::svex-count x)
    (sv::svex-case
     x
     :var (mv x nil)
     :quote (mv x nil)
     :call (b* (((mv args wrapped) (wrap-pp-with-id-lst-aux x.args args-alist))
                ((when wrapped) (mv (sv::svex-call x.fn args) t))
                ((when (hons-get x args-alist))
                 (mv (sv::svex-call 'id (hons-list x)) t)))
             (mv x nil))))
  (define wrap-pp-with-id-lst-aux ((lst sv::svexlist-p)
                                   (args-alist alistp))
    :returns (mv (res sv::svexlist-p :hyp (sv::svexlist-p lst))
                 wrapped)
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        (mv nil nil)
      (b* (((mv cur w1) (wrap-pp-with-id-aux (car lst) args-alist))
           ((mv rest w2) (wrap-pp-with-id-lst-aux (cdr lst) args-alist)))
        (mv (hons cur rest)
            (or w1 w2)))))
  ///
  (verify-guards wrap-pp-with-id-aux)

  (defret-mutual <fn>-is-correct
    (defret <fn>-is-correct
      (equal (sv::Svex-eval$ res env)
             (sv::Svex-eval$ x env))
      :fn wrap-pp-with-id-aux)
    (defret <fn>-is-correct
      (equal (sv::Svexlist-eval$ res env)
             (sv::Svexlist-eval$ lst env))
      :fn wrap-pp-with-id-lst-aux)
    :hints (("Goal"
             :Expand ((wrap-pp-with-id-aux nil args-alist)
                      (wrap-pp-with-id-aux x args-alist)
                      (wrap-pp-with-id-lst-aux lst args-alist))
             :in-theory (e/d (SV::SVEX-APPLY)
                             ()))))

  (memoize 'wrap-pp-with-id-aux
           ;; :condition '(eq (sv::svex-kind x) :call)
           )
  )

(define wrap-pp-with-id-alist-aux ((svex-alist sv::svex-alist-p)
                                   (args-alist alistp))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  :verify-guards :after-returns
  (if (atom svex-alist)
      svex-alist
    (acons (caar svex-alist)
           (b* (((mv res &)
                 (wrap-pp-with-id-aux (cdar svex-alist) args-alist)))
             res)
           (wrap-pp-with-id-alist-aux (cdr svex-alist) args-alist)))
  ///
  (defret <fn>-is-correct
    (equal (sv::Svex-alist-eval$ res env)
           (sv::Svex-alist-eval$ svex-alist env))
    :fn wrap-pp-with-id-alist-aux
    :hints (("Goal"
             :in-theory (e/d (sv::svex-alist-eval$) ())))))

(define wrap-pp-with-id-process-pattern-alist ((pattern-alist pattern-alist-p))
  :returns (res alistp)
  (if (atom pattern-alist)
      nil
    (b* ((cur-args (caar pattern-alist))
         (cur-patterns (cdar pattern-alist))
         ((unless (and (svl::equal-len cur-args 2)
                       (subsetp-equal '(ha-s-chain ha-c-chain)
                                      cur-patterns)))
          (wrap-pp-with-id-process-pattern-alist (cdr pattern-alist))))
      (hons-acons
       (first cur-args)
       nil
       (hons-acons (second cur-args)
                   nil
                   (wrap-pp-with-id-process-pattern-alist (cdr pattern-alist)))))))

(define wrap-pp-with-id-alist ((svex-alist sv::svex-alist-p)
                               &key
                               ((env) 'env)
                               ((context rp-term-listp) 'context)
                               ((config svl::svex-reduce-config-p) 'config))
  :Returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  (b* (((unless (aggressive-find-adders-in-svex))
        svex-alist)
       (- (cw "- Before searching for adders, let's try to wrap partial products with ID to prevent oversimplification during adder pattern finding.~%~%"))
       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex-alist svex-alist :adder-type 'ha :track-column? nil))
       (pattern-alist (fast-alist-clean pattern-alist))
       (args-alist (wrap-pp-with-id-process-pattern-alist pattern-alist))
       (- (fast-alist-free pattern-alist))
       (res (wrap-pp-with-id-alist-aux svex-alist args-alist))
       (- (fast-alist-free args-alist))
       (- (clear-memoize-table 'wrap-pp-with-id-aux)))
    res)
  ///
  (defret <fn>-is-correct
    (equal (sv::Svex-alist-eval$ res free-env)
           (sv::Svex-alist-eval$ svex-alist free-env))
    :fn wrap-pp-with-id-alist
    :hints (("Goal"
             :in-theory (e/d (sv::svex-alist-eval$) ())))))

(defines extract-svex-from-id
  :verify-guards nil
  :hints (("Goal"
           :expand ((SV::SVEX-COUNT X))
           :in-theory (e/d (SV::SVEX-CALL->ARGS)
                           ())))

  (define extract-svex-from-id ((x sv::svex-p))
    :returns (res sv::svex-p :hyp (sv::svex-p x))
    :measure (sv::svex-count x)
    (sv::svex-case
     x
     :var x
     :quote x
     :call
     (case-match x
       (('id x) (extract-svex-from-id x))
       (& (sv::Svex-call x.fn (extract-svex-from-id-lst x.args))))))

  (define extract-svex-from-id-lst ((lst sv::svexlist-p))
    :returns (res sv::svexlist-p :hyp (sv::svexlist-p lst))
    :measure (sv::svexlist-count lst)
    (if (atom lst)
        nil
      (hons (extract-svex-from-id (car lst))
            (extract-svex-from-id-lst (cdr lst)))))
  ///
  (verify-guards extract-svex-from-id)

  (defret-mutual <fn>-is-correct
    (defret <fn>-is-correct
      (equal (sv::Svex-eval$ res env)
             (sv::Svex-eval$ x env))
      :fn extract-svex-from-id)
    (defret <fn>-is-correct
      (equal (sv::Svexlist-eval$ res env)
             (sv::Svexlist-eval$ lst env))
      :fn extract-svex-from-id-lst)
    :hints (("Goal"
             :Expand ((extract-svex-from-id nil)
                      (extract-svex-from-id-lst nil)
                      (extract-svex-from-id x)
                      (extract-svex-from-id-lst lst))
             :in-theory (e/d (SV::SVEX-CALL->FN
                              SV::SVEX-CALL->ARGS
                              SV::SVEX-APPLY)
                             ()))))

  (memoize 'extract-svex-from-id
           ;; :condition '(eq (sv::svex-kind x) :call)
           )
  )

(define extract-svex-from-id-alist ((svex-alist sv::svex-alist-p))
  :Returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  (if (atom svex-alist)
      nil
    (acons (caar svex-alist)
           (extract-svex-from-id (cdar svex-alist))
           (extract-svex-from-id-alist (cdr svex-alist))))
  ///
  (defret <fn>-is-correct
    (equal (sv::Svex-alist-eval$ res env)
           (sv::Svex-alist-eval$ svex-alist env))
    :fn extract-svex-from-id-alist
    :hints (("Goal"
             :expand ((SV::SVEX-ALIST-EVAL NIL ENV))
             :in-theory (e/d (sv::svex-alist-eval$) ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Correct fa-c/s-chain arguments

(define create-fa-c-chain-instance (arg1 arg2 arg3)
  :inline t
  :returns (res sv::svex-p :hyp (and (sv::svex-p arg1)
                                     (sv::svex-p arg2)
                                     (sv::svex-p arg3))
                :hints (("Goal"
                         :in-theory (e/d (ACL2::MERGE-SORT-LEXORDER
                                          ACL2::MERGE-LEXORDER)
                                         ()))))
  (b* (((list arg1 arg2 arg3)
        (acl2::merge-sort-lexorder (list arg1 arg2 arg3))))
    (hons-list 'fa-c-chain 0 arg1 arg2 arg3))
  ///
  (defret <fn>-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-eval$ res env)
                    (fa-c-chain 0
                                (sv::svex-eval$ arg1 env)
                                (sv::svex-eval$ arg2 env)
                                (sv::svex-eval$ arg3 env))))
    :hints (("Goal"
             :in-theory (e/d (fa-c-chain
                              sv::svex-call->args
                              sv::svex-call->fn
                              sv::svex-apply$
                              acl2::merge-lexorder
                              acl2::merge-sort-lexorder)
                             ())))))

(define zero-fa-c-chain-extra-arg ((svex sv::svex-p)
                                   &key
                                   ((env) 'env)
                                   ((context rp-term-listp) 'context)
                                   ((config svl::svex-reduce-config-p) 'config))
  :Returns (res sv::svex-p :hyp (sv::svex-p svex))
  :prepwork ((local
              (in-theory (e/d (ACL2::MERGE-LEXORDER
                               acl2::merge-sort-lexorder)
                              ()))))
  :inline t
  (case-match svex
    (('fa-c-chain extra-arg arg1 arg2 arg3)
     (b* (((unless (valid-fa-c-chain-args-p extra-arg arg1))
           (progn$ (raise "valid-fa-c-chain-args-p failed for: ~p0~%" svex)
                   svex))
          ((unless (or (equal extra-arg 0)
                       (and* (svl::bitp-of-svex arg1)
                             (svl::bitp-of-svex arg2)
                             (svl::bitp-of-svex arg3))))
           (progn$ (cwe "bitp check in rp::zero-fa-c-chain-extra-arg ~p0 failed.~%"
                        (list (or (svl::bitp-of-svex arg1) arg1)
                              (or (svl::bitp-of-svex arg2) arg2)
                              (or (svl::bitp-of-svex arg3) arg3)))
                   svex))
          ((list arg1 arg2 arg3)
           (acl2::merge-sort-lexorder (list arg1 arg2 arg3)))
          ((when (and* (equal arg1 0)
                       (equal arg2 0)))
           0)
          ;; extract when one of the args is 1.
          ((when (and (equal arg1 1)
                      (svl::bitp-of-svex arg2)
                      (svl::bitp-of-svex arg3)))
           (ex-adder-fnc-from-unfloat
            (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor arg2 arg3)))
          ((when (equal arg1 0))
           (ex-adder-fnc-from-unfloat
            (svl::bitand/or/xor-simple-constant-simplify 'sv::bitand arg2 arg3))))
       (sv::svex-call 'fa-c-chain (hons-list 0 arg1 arg2 arg3))))
    (& svex))
  ///

  (local
   (defthm fa-c-chain-commute-args
     (and (equal (fa-c-chain 0 y x z)
                 (fa-c-chain 0 x y z))
          (equal (fa-c-chain 0 x z y)
                 (fa-c-chain 0 x y z)))
     :hints (("Goal"
              :in-theory (e/d (fa-c-chain) ())))))

  (local
   (defthm |(FA-C-CHAIN 0 0 0 x)|
     (equal (FA-C-CHAIN 0 0 0 x)
            0)
     :hints (("Goal"
              :in-theory (e/d (FA-C-CHAIN c-spec) ())))))

  (local
   (defthm |(FA-C-CHAIN 0 0 x y)|
     (equal (FA-C-CHAIN 0 0 x y)
            (sv::4vec-bitand x y))
     :hints (("Goal"
              :in-theory (e/d (FA-C-CHAIN c-spec) ())))))

  (local
   (defthm c-spec-of-two-zeros
     (implies (bitp x)
              (and (equal (c-spec (list 0 x 0)) 0)
                   (equal (c-spec (list x 0 0)) 0)
                   (equal (c-spec (list 0 0 x)) 0)))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthm c-spec-of-one-zeros
     (implies (and (bitp x)
                   (bitp y))
              (and (equal (c-spec (list 0 x y)) (sv::4vec-bitand x y))
                   (equal (c-spec (list x y 0)) (sv::4vec-bitand x y))
                   (equal (c-spec (list y 0 x)) (sv::4vec-bitand x y))))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthm when-one-arg-of-fa-c-chain-is-1
     (implies (and (bitp x)
                   (bitp y))
              (and (equal (c-spec (list x 1 y))
                          (sv::4vec-bitor x y))
                   (equal (c-spec (list 1 x y))
                          (sv::4vec-bitor x y))
                   (equal (c-spec (list x y 1))
                          (sv::4vec-bitor x y))))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthm 3vec-fix-of-bitp
     (implies (bitp x)
              (equal (sv::3vec-fix x)
                     x))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthm SV::4VEC-PART-SELECt-of-bitp
     (implies (bitp x)
              (equal (sv::4vec-part-select 0 1 x)
                     x))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (defret <fn>-correct
    (implies (and (sv::svex-p svex)
                  (rp::rp-term-listp context)
                  (rp::valid-sc env-term a)
                  (rp::eval-and-all context a)
                  (rp::falist-consistent-aux env env-term)
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (svl::integerp-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->integerp-extns config))
                  (warrants-for-adder-pattern-match))
             (equal (sv::Svex-eval$ res (rp-evlt env-term a))
                    (sv::Svex-eval$ svex (rp-evlt env-term a))))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (SV::SVEX-APPLY
                              ACL2::MERGE-LEXORDER
                              ACL2::MERGE-SORT-LEXORDER
                              SV::SVEX-CALL->FN
                              SV::SVEX-QUOTE->VAL
                              SV::SVEX-APPLY$
                              SV::SVEX-CALL->ARGS)
                             ())))))

(defines global-zero-fa-c-chain-extra-arg
  :verify-guards nil
  (define global-zero-fa-c-chain-extra-arg ((svex sv::svex-p)
                                            &key
                                            ((env) 'env)
                                            ((context rp-term-listp) 'context)
                                            ((config svl::svex-reduce-config-p) 'config))
    :measure (sv::Svex-count svex)
    :Returns (res sv::svex-p :hyp (sv::svex-p svex))
    (sv::svex-case
     svex
     :var svex
     :quote svex
     :call (zero-fa-c-chain-extra-arg
            (sv::Svex-call svex.fn
                           (global-zero-fa-c-chain-extra-arg-lst svex.args)))))
  (define global-zero-fa-c-chain-extra-arg-lst ((lst sv::svexlist-p)
                                                &key
                                                ((env) 'env)
                                                ((context rp-term-listp) 'context)
                                                ((config svl::svex-reduce-config-p) 'config))
    :measure (sv::Svexlist-count lst)
    :Returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    (if (atom lst)
        nil
      (hons (global-zero-fa-c-chain-extra-arg (car lst))
            (global-zero-fa-c-chain-extra-arg-lst (cdr lst)))))
  ///
  (verify-guards global-zero-fa-c-chain-extra-arg-fn)
  (defret-mutual <fn>-is-correct
    (defret <fn>-correct
      (implies (and (sv::svex-p svex)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (warrants-for-adder-pattern-match))
               (equal (sv::Svex-eval$ res (rp-evlt env-term a))
                      (sv::Svex-eval$ svex (rp-evlt env-term a))))
      :fn global-zero-fa-c-chain-extra-arg)
    (defret <fn>-correct
      (implies (and (sv::svexlist-p lst)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (warrants-for-adder-pattern-match))
               (equal (sv::Svexlist-eval$ res-lst (rp-evlt env-term a))
                      (sv::Svexlist-eval$ lst (rp-evlt env-term a))))
      :fn global-zero-fa-c-chain-extra-arg-lst)
    :hints (("Goal"
             :do-not-induct t
             :expand ((global-zero-fa-c-chain-extra-arg svex)
                      (global-zero-fa-c-chain-extra-arg-lst lst)
                      (global-zero-fa-c-chain-extra-arg-lst nil))
             :in-theory (e/d () ()))))
  (memoize 'global-zero-fa-c-chain-extra-arg
           ;; :condition '(eq (sv::svex-kind svex) :call)
           )
  )

(define global-zero-fa-c-chain-extra-arg-alist ((alist sv::svex-alist-p)
                                                &key
                                                ((env) 'env)
                                                ((context rp-term-listp) 'context)
                                                ((config svl::svex-reduce-config-p) 'config))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      nil
    (acons (caar alist)
           (global-zero-fa-c-chain-extra-arg (cdar alist))
           (global-zero-fa-c-chain-extra-arg-alist (cdr alist))))
  ///
  (defret <fn>-is-correct
    (implies (and (sv::svex-alist-p alist)
                  (rp-term-listp context)
                  (valid-sc env-term a)
                  (eval-and-all context a)
                  (falist-consistent-aux env env-term)
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (svl::integerp-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->integerp-extns config))
                  (force (warrants-for-adder-pattern-match)))
             (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                    (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
    :hints (("goal"
             :do-not-induct t
             :induct (global-zero-fa-c-chain-extra-arg-alist alist)
             :in-theory (e/d (sv::svex-alist-eval$)
                             ())))))

(defsection fix-order-of-fa/ha-chain-args
  ;; After replacements,  ordered-ness of  arguments might change,  which might
  ;; prevent patterns  from being found  when looking more carefully.   So This
  ;; function goes around and reorders arguments in fa-s and ha-s arguments.

  (local
   (defthm nth-of-svex
     (implies (and (sv::svexlist-p x)
                   (natp i)
                   (< i (len x)))
              (sv::svex-p (nth i x)))))

  (local
   (defthm SVEX-COUNT-lemma
     (implies (and ;;(sv::Svex-p x)
                   (or (EQUAL (CAR X) 'HA-S-CHAIN)
                       (EQUAL (CAR X) 'HA-c-CHAIN)
                       (EQUAL (CAR X) 'HA+1-S-CHAIN)
                       (EQUAL (CAR X) 'HA+1-c-CHAIN)))
              (and (< (SV::SVEX-COUNT (CADDR X))
                      (SV::SVEX-COUNT X))
                   (< (SV::SVEX-COUNT (CADR X))
                      (SV::SVEX-COUNT X))
                   (< (SV::SVEX-COUNT (CADddR X))
                      (SV::SVEX-COUNT X))))
     :hints (("Goal"
              :expand ((SV::SVEX-COUNT X))
              :in-theory (e/d (sv::svex-kind
                               SV::SVEX-CALL->ARGS)
                              ())))))

  (defines fix-order-of-fa/ha-chain-args
    :verify-guards nil

    (define fix-order-of-fa/ha-chain-args ((x sv::svex-p)
                                           &key
                                           ((env) 'env)
                                           ((context rp-term-listp) 'context)
                                           ((config svl::svex-reduce-config-p) 'config))
      :measure (sv::svex-count x)
      :returns (res)
      (sv::svex-case
       x
       :var x
       :quote x
       :call (case-match x
               (('fa-s-chain & & &)
                (b* ((lst1 (fix-order-of-fa/ha-chain-args-lst x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1))
                     ((list first second third)
                      (list (nth 0 lst2) (nth 1 lst2) (nth 2 lst2)))
                     #|((when (and* (equal first 0)
                     (equal second 0)))
                     (create-unfloat-for-adder-fnc third))|#
                     ((when (integerp first))
                      ;; extract when one argument of fa-s-chain is 1 or 0.

                      (ex-adder-fnc-from-unfloat
                       (svl::bitand/or/xor-simple-constant-simplify
                        'sv::bitxor
                        first
                        (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor second third)))

                      #|(svl::svex-reduce-w/-env-apply
                      'sv::bitxor
                      (hons-list first
                      (svl::svex-reduce-w/-env-apply 'sv::bitxor
                      (hons-list second third))))|#))
                  (sv::svex-call x.fn lst2)))
               (('ha-s-chain a b)
                (b* (((when (or* (integerp a) (integerp b)))
                      (b* ((a (fix-order-of-fa/ha-chain-args a))
                           (b (fix-order-of-fa/ha-chain-args b)))
                        (ex-adder-fnc-from-unfloat
                         (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor a b))))
                     (lst1 (fix-order-of-fa/ha-chain-args-lst x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1))
                     ((when (equal (nth 0 lst2) 0))
                      (create-unfloat-for-adder-fnc (nth 1 lst2))))
                  (sv::svex-call x.fn lst2)))
               (('ha-c-chain a b)
                (b* (((when (or* (integerp a) (integerp b)))
                      (b* ((a (fix-order-of-fa/ha-chain-args a))
                           (b (fix-order-of-fa/ha-chain-args b)))
                        (ex-adder-fnc-from-unfloat
                         (svl::bitand/or/xor-simple-constant-simplify 'sv::bitand a b))))
                     (lst1 (fix-order-of-fa/ha-chain-args-lst x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1))
                     ((when (equal (nth 0 lst2) 0))
                      0))
                  (sv::svex-call x.fn lst2)))

               (('ha+1-c-chain a b)
                (b* (((when (or* (integerp a) (integerp b)))
                      (b* ((a (fix-order-of-fa/ha-chain-args a))
                           (b (fix-order-of-fa/ha-chain-args b)))
                        (ex-adder-fnc-from-unfloat
                         (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor a b))))
                     (lst1 (fix-order-of-fa/ha-chain-args-lst x.args))
                     (lst2 (acl2::merge-sort-lexorder lst1)))
                  (sv::svex-call x.fn lst2)))

               (('ha+1-s-chain m a b)
                ;; first arg of ha+1-s-chain should be method, therefore, a constant at all times.
                (b* (((when (and*-exec (or* (integerp a)
                                            (integerp b))
                                       (natp m)))
                      (b* ((a (fix-order-of-fa/ha-chain-args a))
                           (b (fix-order-of-fa/ha-chain-args b)))
                        (cond ((= m 10) (ex-adder-fnc-from-unfloat
                                         (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor a b)))
                              ((= m 0) (sv::svex-call 'sv::bitnot
                                                      (hons-list
                                                       (ex-adder-fnc-from-unfloat
                                                        (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor a b)))))
                              (t (ex-adder-fnc-from-unfloat
                                  (svl::bitand/or/xor-simple-constant-simplify
                                   'sv::bitxor
                                   1
                                   (ex-adder-fnc-from-unfloat
                                    (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor a b))))))))
                     (lst1 (fix-order-of-fa/ha-chain-args-lst (cdr x.args)))
                     (lst2 (acl2::merge-sort-lexorder lst1)))
                  (sv::svex-call x.fn (cons (car x.args) lst2))))
               (('sv::bitxor & &)
                (b* ((first (fix-order-of-fa/ha-chain-args (first x.args)))
                     (second (fix-order-of-fa/ha-chain-args (second x.args))))
                  (svl::bitand/or/xor-simple-constant-simplify 'sv::bitxor first second)))
               (('sv::bitand & &)
                (b* ((first (fix-order-of-fa/ha-chain-args (first x.args)))
                     (second (fix-order-of-fa/ha-chain-args (second x.args))))
                  (svl::bitand/or/xor-simple-constant-simplify 'sv::bitand first second)))
               (&
                (b* ((res (sv::svex-call x.fn
                                         (fix-order-of-fa/ha-chain-args-lst x.args)))
                     (res (zero-fa-c-chain-extra-arg res))
                     (res (ex-adder-fnc-from-unfloat res)))
                  res)))))
    (define fix-order-of-fa/ha-chain-args-lst ((lst sv::svexlist-p)
                                               &key
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
      :measure (sv::svexlist-count lst)
      :returns (res )
      (if (atom lst)
          nil
        (hons (fix-order-of-fa/ha-chain-args (car lst))
              (fix-order-of-fa/ha-chain-args-lst (cdr lst)))))

    ///

    (defret len-of-<fn>
      (equal (len res)
             (len lst))
      :fn fix-order-of-fa/ha-chain-args-lst)

    (defret-mutual svex-p-of-<fn>
      (defret svex-p-of-<fn>
        (implies (sv::svex-p x)
                 (sv::svex-p res))
        :fn fix-order-of-fa/ha-chain-args)
      (defret svexlist-p-of-<fn>
        (implies (sv::svexlist-p lst)
                 (sv::svexlist-p res))
        :fn fix-order-of-fa/ha-chain-args-lst)
      :hints (("Goal"
               :in-theory (e/d (SV::SVEX-CALL->ARGS) ()))))

    (verify-guards fix-order-of-fa/ha-chain-args-fn
      :hints (("Goal"
               :in-theory (e/d (SV::SVEX-CALL->ARGS) ()))))

    (memoize 'fix-order-of-fa/ha-chain-args-fn
             ;; :condition '(eq (sv::svex-kind x) :call)
             )

    (local
     (defthm svex-eval$-of-natp
       (implies (natp x)
                (equal (SV::SVEX-EVAL$ x env)
                       x))
       :hints (("Goal"
                :in-theory (e/d (SV::SVEX-QUOTE->VAL) ())))))

    (defret-mutual <fn>-is-correct
      (defret <fn>-is-correct
        (implies (and (sv::svex-p x)
                      (rp::rp-term-listp context)
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (warrants-for-adder-pattern-match))
                 (equal (sv::svex-eval$ res (rp-evlt env-term a))
                        (sv::svex-eval$ x (rp-evlt env-term a))))
        :fn fix-order-of-fa/ha-chain-args)
      (defret <fn>-is-correct
        (implies (and (sv::svexlist-p lst)
                      (rp::rp-term-listp context)
                      (rp::valid-sc env-term a)
                      (rp::eval-and-all context a)
                      (rp::falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (warrants-for-adder-pattern-match))
                 (equal (sv::svexlist-eval$ res (rp-evlt env-term a))
                        (sv::svexlist-eval$ lst (rp-evlt env-term a))))
        :fn fix-order-of-fa/ha-chain-args-lst)
      :hints (("Goal"
               :do-not-induct t
               :expand (;;(warrants-for-adder-pattern-match)
                        (:free (fn args)
                               (sv::Svex-kind (cons fn args)))
                        (:free (args)
                               (sv::svex-apply$ 'ha-s-chain args))
                        (:free (args)
                               (sv::svex-apply$ 'ha+1-s-chain args))
                        (:free (args)
                               (sv::svex-apply$ 'ha+1-c-chain args))
                        (:free (args)
                               (sv::svex-apply$ 'ha-c-chain args))
                        (:free (args)
                               (sv::svex-apply$ 'fa-s-chain args))
                        (:free (args)
                               (sv::svex-apply 'sv::bitxor args))
                        (:free (args)
                               (sv::svex-apply 'sv::bitnot args))
                        (:free (args)
                               (sv::svex-apply 'sv::bitor args))
                        (:free (args)
                               (sv::svex-apply 'sv::bitand args))
                        (acl2::merge-sort-lexorder (cdr x))
                        (fix-order-of-fa/ha-chain-args-lst lst)
                        (fix-order-of-fa/ha-chain-args x))
               :in-theory (e/d (SV::SVEX-QUOTE->VAL
                                acl2::merge-lexorder
                                acl2::merge-sort-lexorder
                                ha-s-chain
                                ha+1-s-chain
                                ha+1-c-chain
                                fa-s-chain
                                HA-C-CHAIN
                                sv::svex-call->fn
                                sv::svex-call->args)
                               (nth
                                ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                SV::SVEX-KIND$INLINE
                                ACL2::SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP
                                (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                                (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                                (:DEFINITION ACL2::APPLY$-BADGEP)
                                (:REWRITE ACL2::NATP-OF-CAR-WHEN-NAT-LISTP)
                                (:DEFINITION NAT-LISTP)
                                ACL2::INTEGERP-OF-CAR-WHEN-INTEGER-LISTP

                                warrants-for-adder-pattern-match
                                (:e warrants-for-adder-pattern-match)
                                ;;cons-equal
                                member-equal
                                VALID-SC
                                ;;evens
                                ;;cons-equal
                                ))))))

  (define fix-order-of-fa/ha-chain-args-alist ((alist sv::svex-alist-p)
                                               &key
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
    (if (atom alist)
        nil
      (acons (caar alist)
             (fix-order-of-fa/ha-chain-args (cdar alist))
             (fix-order-of-fa/ha-chain-args-alist (cdr alist))))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-alist-p alist)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                      (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
      :fn fix-order-of-fa/ha-chain-args-alist
      :hints (("Goal"
               :in-theory (e/d (SV::SVEX-ALIST-EVAL$) ()))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Vector adders.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simplification for carry select adder

(define csel-branch (svex)
  :returns (mv (test sv::Svex-p :hyp (sv::Svex-p svex))
               (then sv::Svex-p :hyp (sv::Svex-p svex))
               (else sv::Svex-p :hyp (sv::Svex-p svex))
               valid)
  (case-match svex
    (('sv::bitor ('sv::bitand b ('sv::Bitxor 1 y))
                 ('sv::bitand a y))
     (mv y a b t))
    (('sv::bitor ('sv::bitand a y)
                 ('sv::bitand b ('sv::Bitxor 1 y)))
     (mv y a b t))
    (('sv::? test a b)
     (mv test a b t))
    (& (mv 0 0 0 nil)))
  ///
  (defret <fn>-is-correct
    (implies (and valid
                  (bitp (sv::svex-eval$ test env))
                  (bitp (sv::svex-eval$ then env))
                  (bitp (sv::svex-eval$ else env)))
             (and (implies (case-split
                            (equal (sv::svex-eval$ test env) 1))
                           (equal (sv::svex-eval$ then env)
                                  (sv::svex-eval$ svex env)))
                  (implies (not (equal (sv::svex-eval$ test env) 1))
                           (equal (sv::svex-eval$ else env)
                                  (sv::svex-eval$ svex env)))))
    :hints (("Goal"
             :in-theory (e/d (SV::SVEX-APPLY
                              SV::SVEX-CALL->FN
                              SV::SVEX-CALL->args)
                             ())))))

(local
 (defthm subsetp-equal-of-intersection-equal
   (and (subsetp-equal (intersection-equal x y)
                       x)
        (subsetp-equal (intersection-equal x y)
                       y))))

(local
 (defthm fa-c-chain-reorder
   (and (equal (fa-c-chain 0 y x z)
               (fa-c-chain 0 x y z))
        (equal (fa-c-chain 0 x z y)
               (fa-c-chain 0 x y z)))
   :hints (("Goal"
            :in-theory (e/d (fa-c-chain) ())))))

(local
 (defthm fa-s-chain-reorder
   (and (equal (fa-s-chain y x z)
               (fa-s-chain x y z))
        (equal (fa-s-chain x z y)
               (fa-s-chain x y z)))
   :hints (("Goal"
            :in-theory (e/d (fa-s-chain) ())))))

(define get-two-common-one-diff (lst1 lst2)
  :returns (mv (c1 sv::svex-p :hyp (sv::svexlist-p lst1))
               (c2 sv::svex-p :hyp (sv::svexlist-p lst1))
               (o1 sv::svex-p :hyp (sv::svexlist-p lst1))
               (o2 sv::svex-p :hyp (sv::svexlist-p lst2))
               valid)
  (b* (((unless (and* (svl::equal-len lst1 3)
                      (svl::equal-len lst2 3)))
        (mv 0 0 0 0 nil))
       ((unless (and* (no-duplicatesp-equal lst1)
                      (no-duplicatesp-equal lst2)))
        (mv 0 0 0 0 nil))
       (inter (intersection-equal lst1 lst2))
       ((unless (svl::equal-len inter 2))
        (mv 0 0 0 0 nil))
       (t0 (set-difference-equal lst1 inter))
       (e0 (set-difference-equal lst2 inter))
       ((unless (and* (svl::equal-len t0 1)
                      (svl::equal-len e0 1)))
        (mv 0 0 0 0 nil)))
    (mv (first inter)
        (second inter)
        (car t0)
        (car e0)
        t))
  ///
  (local
   (in-theory (e/d ()
                   (;;member-equal
                    ;;intersection-equal
                    acl2::member-equal-newvar-components-2
                    acl2::true-list-listp-implies-true-listp-xxx
                    true-list-listp
                    true-listp
                    svexlist-p-implies-true-listp
                    acl2::true-listp-of-car-when-true-list-listp
                    acl2::true-list-listp-of-cons
                    cdr-of-x-is-svexlist-p-when-kind-is-svex-fn-call
                    sv::svexlist-p-of-cdr-when-svexlist-p
                    (:rewrite sv::svex-p-of-car-when-svexlist-p)
                    (:rewrite
                     sv::svexlist-p-of-car-when-svexlistlist-p)
                    (:rewrite
                     sv::svexlistlist-p-of-cdr-when-svexlistlist-p)
                    acl2::member-equal-newvar-components-1
                    acl2::loop$-as
                    default-car
                    acl2::cdr-loop$-as-tuple
                    acl2::car-loop$-as-tuple
                    set-difference-equal
                    (:type-prescription member-equal)
                    (:definition acl2::empty-loop$-as-tuplep)
                    acl2::member-equal-newvar-components-3
                    (:type-prescription acl2::loop$-as)
                    (:definition sv::svex-kind$inline)
                    default-cdr))))

  (defret measure-lemma
    (implies valid
             (and (< (cons-count c1)
                     (cons-count lst1))
                  (< (cons-count c2)
                     (cons-count lst1))
                  (< (cons-count o1)
                     (cons-count lst1))
                  (< (cons-count c1)
                     (cons-count lst2))
                  (< (cons-count c2)
                     (cons-count lst2))
                  (< (cons-count o2)
                     (cons-count lst2))))
    :rule-classes (:linear :rewrite)
    :hints (("goal"
             :expand ((:free (x) (set-difference-equal (cdr lst2) x))
                      (:free (x) (set-difference-equal (cddr lst2) x))
                      (:free (x) (set-difference-equal lst2 x))
                      (:free (x) (set-difference-equal (cdr lst1) x))
                      (:free (x) (set-difference-equal (cddr lst1) x))
                      (:free (x) (set-difference-equal lst1 x))
                      (intersection-equal lst1 lst2)
                      (intersection-equal (cdr lst1) lst2))
             :in-theory (e/d (svl::equal-len
                              intersection-equal
                              cons-count)
                             ()))))

  (defret <fn>-is-correct
    (implies (and valid
                  ;;(bitp (sv::svex-eval$ c1 env))
                  ;;(bitp (sv::svex-eval$ c2 env))
                  )
             (and
              (equal (fa-c-chain 0
                                 (sv::svex-eval$ c1 env)
                                 (sv::svex-eval$ c2 env)
                                 (sv::svex-eval$ o1 env))
                     (fa-c-chain 0
                                 (sv::svex-eval$ (first lst1) env)
                                 (sv::svex-eval$ (second lst1) env)
                                 (sv::svex-eval$ (third lst1) env)))
              (equal (fa-s-chain (sv::svex-eval$ c1 env)
                                 (sv::svex-eval$ c2 env)
                                 (sv::svex-eval$ o1 env))
                     (fa-s-chain (sv::svex-eval$ (first lst1) env)
                                 (sv::svex-eval$ (second lst1) env)
                                 (sv::svex-eval$ (third lst1) env)))
              (equal (fa-c-chain 0
                                 (sv::svex-eval$ c1 env)
                                 (sv::svex-eval$ c2 env)
                                 (sv::svex-eval$ o2 env))
                     (fa-c-chain 0
                                 (sv::svex-eval$ (first lst2) env)
                                 (sv::svex-eval$ (second lst2) env)
                                 (sv::svex-eval$ (third lst2) env)))
              (equal (fa-s-chain (sv::svex-eval$ c1 env)
                                 (sv::svex-eval$ c2 env)
                                 (sv::svex-eval$ o2 env))
                     (fa-s-chain (sv::svex-eval$ (first lst2) env)
                                 (sv::svex-eval$ (second lst2) env)
                                 (sv::svex-eval$ (third lst2) env)))))
    :hints (("goal"
             :expand ((svl::equal-len (cddr lst1) 1)
                      (svl::equal-len (cdr lst1) 2)
                      (svl::equal-len lst1 3)
                      (svl::equal-len (cddr lst2) 1)
                      (svl::equal-len (cdr lst2) 2)
                      (svl::equal-len lst2 3)
                      (:free (then else)
                             (intersection-equal (cdr then) (cdr else)))
                      (member-equal (cadr lst1) lst2)
                      (member-equal (caddr lst1) lst2)
                      (member-equal (car lst1) lst2)
                      (member-equal (cadr lst1) (cdr lst2))
                      (member-equal (caddr lst1) (cdr lst2))
                      (member-equal (car lst1) (cdr lst2))
                      (member-equal (cadr lst1) (cddr lst2))
                      (member-equal (caddr lst1) (cddr lst2))
                      (member-equal (car lst1) (cddr lst2))
                      (member-equal (cadr lst1) (cdddr lst2))
                      (member-equal (caddr lst1) (cdddr lst2))
                      (member-equal (car lst1) (cdddr lst2))
                      (:free (x)
                             (set-difference-equal lst2 x))
                      (:free (x)
                             (set-difference-equal (cdr lst2) x))
                      (:free (x)
                             (set-difference-equal (cddr lst2) x))
                      (:free (x)
                             (set-difference-equal lst1 x))
                      (:free (x)
                             (set-difference-equal nil x))
                      (:free (x)
                             (set-difference-equal (cdr lst1) x))
                      (:free (x)
                             (set-difference-equal (cddr lst1) x))
                      )
             :in-theory (e/d (and*
                              bitp
                              ;;set-difference-equal
                              svl::equal-len
                              )
                             ())))))

(with-output :off :all
  :on (error summary)
  :gag-mode nil
  (define csel-simplify-end-at-bitand ((test sv::svex-p)
                                       (then sv::Svex-p)
                                       (else sv::svex-p)
                                       &key

                                       ((env) 'env)
                                       ((context rp-term-listp) 'context)
                                       ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                (sv::svex-p then)
                                                (sv::svex-p else)))
                 valid)

    (cond
     ((and* (bitand-pattern-p else)
            (bitor-pattern-p then))
      (b* (((list e1 e2) (cdr else))
           ((list t1 t2) (cdr then))
           ((unless (or (and* (equal e1 t1) (equal e2 t2))
                        (and* (equal e1 t2) (equal e2 t1))))
            (mv 0 nil))
           ((unless (and* (svl::bitp-of-svex e1)
                          (svl::bitp-of-svex e2)
                          (svl::bitp-of-svex test)))
            (progn$ (or (svl::bitp-of-svex e1)
                        (cwe "bitp failing on e1: ~p0~%" e1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e1)
                             (svl::width-of-svex e1)))
                    (or (svl::bitp-of-svex e2)
                        (cwe "bitp failing on e2 ~p0~%" e2)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e2)
                             (svl::width-of-svex e2)))
                    (or (svl::bitp-of-svex test)
                        (cwe "bitp failing on test: ~p0~%" test)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex test)
                             (svl::width-of-svex test)))
                    (raise "Bitp check failed at last step~%")
                    (mv 0 nil)))
           (new-args (hons-list 0 test e1 e2)))
        (mv (sv::svex-call 'fa-c-chain new-args)
            t)))
     (t (mv 0 nil)))))

(with-output :off :all
  :on (error summary)
  :gag-mode nil
  (define csel-simplify-end-at-bitxor ((test sv::svex-p)
                                       (then sv::Svex-p)
                                       (else sv::svex-p)
                                       &key
                                       ((env) 'env)
                                       ((context rp-term-listp) 'context)
                                       ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                (sv::svex-p then)
                                                (sv::svex-p else)))
                 valid)
    (cond
     ((and* (bitxor-pattern-p else)
            (or (ha+1-s-chain-pattern-2-p then)
                (ha+1-s-chain-pattern-3-p then)))
      (b* (((list e1 e2) (cdr else))
           ((mv t1 t2) (cond ((ha+1-s-chain-pattern-2-p then)
                              (ha+1-s-chain-pattern-2-body
                               then
                               (b* (((mv t1 t2 &) (look-for-ha+1-s-chain-pattern-aux x y z)))
                                 (mv t1 t2))))
                             (t
                              (ha+1-s-chain-pattern-3-body
                               then
                               (b* (((mv t1 t2 &) (look-for-ha+1-s-chain-pattern-aux x y z)))
                                 (mv t1 t2))))))
           ((unless (or (and* (equal e1 t1) (equal e2 t2))
                        (and* (equal e1 t2) (equal e2 t1))))
            (mv 0 nil))
           ((unless (and* (svl::bitp-of-svex e1) ;; maybe remove
                          (svl::bitp-of-svex e2) ;; maybe remove
                          (svl::bitp-of-svex test)))
            (progn$ (or (svl::bitp-of-svex e1)
                        (cwe "bitp failing on e1: ~p0~%" e1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e1)
                             (svl::width-of-svex e1)))
                    (or (svl::bitp-of-svex e2)
                        (cwe "bitp failing on e2 ~p0~%" e2)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e2)
                             (svl::width-of-svex e2)))
                    (or (svl::bitp-of-svex test)
                        (cwe "bitp failing on test: ~p0~%" test)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex test)
                             (svl::width-of-svex test)))
                    (raise "Bitp check failed at last step~%")
                    (mv 0 nil)))
           (new-args (hons-list test e1 e2)))
        (mv (sv::svex-call 'fa-s-chain new-args)
            t)))
     (t (mv 0 nil)))))

(with-output :off :all
  :on (error summary)
  :gag-mode nil
  (define csel-simplify-end-at-special-bitxor ((test sv::svex-p)
                                               (then sv::Svex-p)
                                               (else sv::svex-p)
                                               &key
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                (sv::svex-p then)
                                                (sv::svex-p else)))
                 valid)
    (cond
     ((and* (fa-s-chain-itself-pattern-p then)
            (bitxor-pattern-p else))
      (b* (((list e1 e2) (cdr else))
           ((list t1 t2 t3) (cdr then))
           ((mv o1 valid)
            (cond ((equal e1 t1)
                   (cond ((equal e2 t2)
                          (mv t3 t))
                         ((equal e2 t3)
                          (mv t2 t))
                         (t (mv 0 nil))))
                  ((equal e1 t2)
                   (cond ((equal e2 t1)
                          (mv t3 t))
                         ((equal e2 t3)
                          (mv t1 t))
                         (t (mv 0 nil))))
                  ((equal e1 t3)
                   (cond ((equal e2 t1)
                          (mv t2 t))
                         ((equal e2 t2)
                          (mv t1 t))
                         (t (mv 0 nil))))
                  (t (mv 0 nil))))
           ((Unless valid)
            (mv 0 nil))

           ((unless (and* ;;(svl::bitp-of-svex then) ;; redundant but helps the proofs
                     ;;(svl::bitp-of-svex else) ;; redundant but helps the proofs
                     (svl::bitp-of-svex e1)
                     (svl::bitp-of-svex e2)
                     (svl::bitp-of-svex o1)
                     (svl::bitp-of-svex test)))
            (progn$ (or (svl::bitp-of-svex e1)
                        (cwe "bitp failing on e1: ~p0~%" e1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e1)
                             (svl::width-of-svex e1)))
                    (or (svl::bitp-of-svex e2)
                        (cwe "bitp failing on e2: ~p0~%" e2)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e2)
                             (svl::width-of-svex e2)))
                    (or (svl::bitp-of-svex o1)
                        (cwe "bitp failing on o1: ~p0~%" o1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex o1)
                             (svl::width-of-svex o1)))
                    (or (svl::bitp-of-svex test)
                        (cwe "bitp failing on test: ~p0~%" test)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex test)
                             (svl::width-of-svex test)))
                    (raise "Bitp check failed at last step~%")
                    (mv 0 nil)))
           (new-inner-arg (hons-list 'sv::bitand test o1))
           (new-args (hons-list new-inner-arg e1 e2)))
        (mv (sv::svex-call 'fa-s-chain new-args)
            t)))
     (t (mv 0 nil)))))

(with-output :off :all
  :on (error summary)
  :gag-mode nil
  (define csel-simplify-end-at-special-bitand ((test sv::svex-p)
                                               (then sv::Svex-p)
                                               (else sv::svex-p)
                                               &key
                                               ((env) 'env)
                                               ((context rp-term-listp) 'context)
                                               ((config svl::svex-reduce-config-p) 'config))
    :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                (sv::svex-p then)
                                                (sv::svex-p else)))
                 valid)
    (cond
     ((and* (fa-c-chain-itself-pattern-p then)
            (bitand-pattern-p else))
      (b* (((list m t1 t2 t3) (cdr then))
           ((list e1 e2) (cdr else))
           ((Unless (valid-fa-c-chain-args-p m t1))
            (mv 0 nil))
           ((mv o1 valid)
            (cond ((equal e1 t1)
                   (cond ((equal e2 t2)
                          (mv t3 t))
                         ((equal e2 t3)
                          (mv t2 t))
                         (t (mv 0 nil))))
                  ((equal e1 t2)
                   (cond ((equal e2 t1)
                          (mv t3 t))
                         ((equal e2 t3)
                          (mv t1 t))
                         (t (mv 0 nil))))
                  ((equal e1 t3)
                   (cond ((equal e2 t1)
                          (mv t2 t))
                         ((equal e2 t2)
                          (mv t1 t))
                         (t (mv 0 nil))))
                  (t (mv 0 nil))))
           ((Unless valid)
            (mv 0 nil))

           ((unless (and* ;;(svl::bitp-of-svex then) ;; redundant but helps the proofs
                     ;;(svl::bitp-of-svex else) ;; redundant but helps the proofs
                     (svl::bitp-of-svex e1)
                     (svl::bitp-of-svex e2)
                     (svl::bitp-of-svex o1)
                     (svl::bitp-of-svex test)))
            (progn$ (or (svl::bitp-of-svex e1)
                        (cwe "bitp failing on e1: ~p0~%" e1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e1)
                             (svl::width-of-svex e1)))
                    (or (svl::bitp-of-svex e2)
                        (cwe "bitp failing on e2: ~p0~%" e2)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex e2)
                             (svl::width-of-svex e2)))
                    (or (svl::bitp-of-svex o1)
                        (cwe "bitp failing on o1: ~p0~%" o1)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex o1)
                             (svl::width-of-svex o1)))
                    (or (svl::bitp-of-svex test)
                        (cwe "bitp failing on test: ~p0~%" test)
                        (cwe "integerp: ~p0 width:~p1~%"
                             (svl::integerp-of-svex test)
                             (svl::width-of-svex test)))
                    (raise "Bitp check failed at last step~%")
                    (mv 0 nil)))
           (new-inner-arg (hons-list 'sv::bitand test o1))
           (new-args (hons-list 0 new-inner-arg e1 e2)))
        (mv (sv::svex-call 'fa-c-chain new-args)
            t)))
     (t (mv 0 nil)))))

(with-output
  :off :all
  :on (summary error)
  :gag-mode nil
  (defines csel-simplify
    ;; splitting into multiple functions to reduce casepslits and speed up proofs
    (define csel-simplify-fa-c ((test sv::svex-p)
                                (then sv::Svex-p)
                                (else sv::svex-p)
                                &key
                                ((limit natp) '(1- limit))
                                ((env) 'env)
                                ((context rp-term-listp) 'context)
                                ((config svl::svex-reduce-config-p) 'config))
      :measure (nfix limit)
      :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                  (sv::svex-p then)
                                                  (sv::svex-p else)))
                   valid)
      :verify-guards nil

      (cond ((zp limit)
             (mv 0 nil))
            ((and* (fa-c-chain-itself-pattern-p then)
                   (fa-c-chain-itself-pattern-p else))
             (b* (((unless (and* (valid-fa-c-chain-args-p (first (cdr then))
                                                          (second (cdr then)))
                                 (valid-fa-c-chain-args-p (first (cdr else))
                                                          (second (cdr else)))))
                   (mv 0 nil))

                  ((mv c1 c2 o1 o2 valid)
                   (get-two-common-one-diff (cddr then)
                                            (cddr else)))
                  ((unless valid)
                   (mv 0 nil))
                  ((mv rest-svex valid)
                   (csel-simplify test o1 o2))
                  ((unless valid)
                   (mv 0 nil))
                  ((unless (and* (svl::bit-listp-of-svex (cddr then))
                                 (svl::bit-listp-of-svex (cddr else))))
                   (progn$ (raise "Bitp check failed under fa-c-chain-pattern-p~%")
                           (mv 0 nil)))
                  (new-args (hons-list 0 rest-svex c1 c2)))
               (mv (sv::svex-call 'fa-c-chain new-args)
                   t)))
            (t (mv 0 nil))))

    (define csel-simplify-fa-s ((test sv::svex-p)
                                (then sv::Svex-p)
                                (else sv::svex-p)
                                &key
                                ((limit natp) '(1- limit))
                                ((env) 'env)
                                ((context rp-term-listp) 'context)
                                ((config svl::svex-reduce-config-p) 'config))

      :measure (nfix limit)
      :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                  (sv::svex-p then)
                                                  (sv::svex-p else)))
                   valid)

      (cond ((zp limit)
             (mv 0 nil))
            ((and* (or (fa-s-chain-itself-pattern-p then)
                       (fa-s-chain-pattern-1-p then)
                       (fa-s-chain-pattern-2-p then))
                   (or (fa-s-chain-itself-pattern-p else)
                       (fa-s-chain-pattern-1-p else)
                       (fa-s-chain-pattern-2-p else)))
             (b* ((then-args (cond ((fa-s-chain-itself-pattern-p then)
                                    (cdr then))
                                   ((fa-s-chain-pattern-1-p then)
                                    (fa-s-chain-pattern-1-body then
                                                               (list x y z)))
                                   ((fa-s-chain-pattern-2-p then)
                                    (fa-s-chain-pattern-2-body then
                                                               (list x y z)))))
                  (else-args (cond ((fa-s-chain-itself-pattern-p else)
                                    (cdr else))
                                   ((fa-s-chain-pattern-1-p else)
                                    (fa-s-chain-pattern-1-body else
                                                               (list x y z)))
                                   ((fa-s-chain-pattern-2-p else)
                                    (fa-s-chain-pattern-2-body else
                                                               (list x y z)))))

                  ((mv c1 c2 o1 o2 valid)
                   (get-two-common-one-diff then-args
                                            else-args))
                  ((unless valid)
                   (mv 0 nil))
                  ((mv rest-svex valid)
                   (csel-simplify test o1 o2))
                  ((unless valid)
                   (mv 0 nil))
                  ((unless (and* (svl::bit-listp-of-svex then-args)
                                 (svl::bit-listp-of-svex else-args)))
                   (progn$ (raise "Bitp check failed under fa-s-chain-pattern-p~%")
                           (mv 0 nil)))
                  (new-args (hons-list rest-svex c1 c2)))
               (mv (sv::svex-call 'fa-s-chain new-args)
                   t)))
            (t (mv 0 nil))))

    (define csel-simplify-ha-s ((test sv::svex-p)
                                (then sv::Svex-p)
                                (else sv::svex-p)
                                &key
                                ((limit natp) '(1- limit))
                                ((env) 'env)
                                ((context rp-term-listp) 'context)
                                ((config svl::svex-reduce-config-p) 'config))

      :measure (nfix limit)
      :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                  (sv::svex-p then)
                                                  (sv::svex-p else)))
                   valid)

      (cond ((zp limit)
             (mv 0 nil))
            ((and* (bitxor-pattern-p then)
                   (bitxor-pattern-p else))
             (b* (((list t1 t2) (cdr then))
                  ((list e1 e2) (cdr else))
                  ((mv c eo to valid)
                   (cond ((equal e1 t1)
                          (mv e1 e2 t2 t))
                         ((equal e1 t2)
                          (mv e1 e2 t1 t))
                         ((equal e2 t1)
                          (mv e2 e1 t2 t))
                         ((equal e2 t2)
                          (mv e2 e1 t1 t))
                         (t (mv 0 0 0 nil))))
                  ((unless valid) (mv 0 nil))
                  ((mv rest-svex valid)
                   (csel-simplify test to eo))
                  ((unless valid) (mv 0 nil))
                  ((unless (and* (svl::bit-listp-of-svex (cdr then))
                                 (svl::bit-listp-of-svex (cdr else))))
                   (progn$ (raise "Bitp check failed under bitxor-pattern-p~%")
                           (mv 0 nil)))
                  (new-args (hons-list rest-svex c)))
               (mv (sv::svex-call 'sv::bitxor new-args)
                   t)))
            (t (mv 0 nil))))

    (define csel-simplify-ha-c ((test sv::svex-p)
                                (then sv::Svex-p)
                                (else sv::svex-p)
                                &key
                                ((limit natp) '(1- limit))
                                ((env) 'env)
                                ((context rp-term-listp) 'context)
                                ((config svl::svex-reduce-config-p) 'config))

      :measure (nfix limit)
      :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                  (sv::svex-p then)
                                                  (sv::svex-p else)))
                   valid)

      (cond ((zp limit)
             (mv 0 nil))
            ((and* (bitand-pattern-p then)
                   (bitand-pattern-p else))
             (b* (((list t1 t2) (cdr then))
                  ((list e1 e2) (cdr else))
                  ((mv c eo to valid)
                   (cond ((equal e1 t1)
                          (mv e1 e2 t2 t))
                         ((equal e1 t2)
                          (mv e1 e2 t1 t))
                         ((equal e2 t1)
                          (mv e2 e1 t2 t))
                         ((equal e2 t2)
                          (mv e2 e1 t1 t))
                         (t (mv 0 0 0 nil))))
                  ((unless valid) (mv 0 nil))
                  ((mv rest-svex valid)
                   (csel-simplify test to eo))
                  ((unless valid) (mv 0 nil))
                  ((unless (and* (svl::bit-listp-of-svex (cdr then))
                                 (svl::bit-listp-of-svex (cdr else))))
                   (progn$ (raise "Bitp check failed under bitxor-pattern-p~%")
                           (mv 0 nil)))
                  (new-args (hons-list rest-svex c)))
               (mv (sv::svex-call 'sv::bitand new-args)
                   t)))
            (t (mv 0 nil))))

    (define csel-simplify ((test sv::svex-p)
                           (then sv::Svex-p)
                           (else sv::svex-p)
                           &key
                           ((limit natp) '(1- limit))
                           ((env) 'env)
                           ((context rp-term-listp) 'context)
                           ((config svl::svex-reduce-config-p) 'config))

      :measure (nfix limit)
      :returns (mv (new-svex sv::svex-p :hyp (and (sv::svex-p test)
                                                  (sv::svex-p then)
                                                  (sv::svex-p else)))
                   valid)
      :verify-guards nil

      (cond ((zp limit)
             (mv 0 nil))
            (t (b* (((mv new-svex valid) (csel-simplify-fa-c test then else))
                    ((when valid) (mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-fa-s test then else))
                    ((when valid)(mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-ha-s test then else))
                    ((when valid)(mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-ha-c test then else))
                    ((when valid)(mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-end-at-bitand test then else))
                    ((when valid) (mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-end-at-bitxor test then else))
                    ((when valid) (mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-end-at-special-bitxor test then else))
                    ((when valid) (mv new-svex valid))

                    ((mv new-svex valid) (csel-simplify-end-at-special-bitand test then else))
                    ((when valid) (mv new-svex valid))
                    )
                 (mv 0 nil)))))
    ///

    (local
     (defthm dummy-lemma
       (implies (and (sv::svex-p then)
                     (or (fa-c-chain-itself-pattern-p then)
                         (fa-s-chain-itself-pattern-p then)
                         (bitxor-PATTERN-P then)
                         (bitand-PATTERN-P then)))
                (SV::SVEXLIST-P (CDR THEN)))
       :hints (("Goal"
                :in-theory (e/d (sv::svex-p
                                 sv::Svex-kind
                                 sv::svex-call->args
                                 sv::svex-call->fn)
                                ())))))

    (local
     (defthm svexlist-p-of-cdr
       (implies (sv::Svexlist-p lst)
                (sv::Svexlist-p (cdr lst)))))

    (verify-guards csel-simplify-fn
      :hints (("Goal"
               :do-not-induct t
               :in-theory (e/d (sv::svex-p-of-car-when-svexlist-p)
                               (valid-fa-c-chain-args-p)))))

    #|(local
    (defthmd bitp-of-svex-eval$-casesplit-trigger ;
    (implies (and (sv::svex-p svex) ;
    (rp::rp-term-listp context) ;
    (rp::valid-sc env-term a) ;
    (rp::eval-and-all context a) ;
    (rp::falist-consistent-aux env env-term) ;
    (svl::width-of-svex-extn-correct$-lst ;
    (svl::svex-reduce-config->width-extns config)) ;
    (svl::integerp-of-svex-extn-correct$-lst ;
    (svl::svex-reduce-config->integerp-extns config))) ;
    (equal (svl::bitp-of-svex svex) ;
    (and (hide (svl::bitp-of-svex svex)) ;
    (bitp (sv::Svex-eval$ svex (rp-evlt env-term a)))))) ;
    :hints (("Goal" ;
    :expand (hide (svl::bitp-of-svex svex )) ;
    :in-theory (e/d () ())))))|#

    (local
     (defthm dummy-svex-lemma
       (implies (and (sv::svex-p x)
                     (FA-C-CHAIN-ITSELF-PATTERN-P x))
                (and (SV::SVEX-P (CAR (CDDDDR x)))
                     (SV::SVEX-P (CAR (CDDDR x)))
                     (SV::SVEX-P (CAR (CDDR x)))
                     (SV::SVEX-P (CAR (CDR x)))))
       :hints (("Goal"
                :expand ((sv::svex-p x))
                :in-theory (e/d (sv::svex-p) ())))))

    (local
     (defthm c-spec-of-1-when-bitp
       (implies (and (bitp x)
                     (bitp y))
                (and (equal (c-spec (list 1 x y))
                            (logior x y))
                     (equal (c-spec (list 0 x y))
                            (logand x y))))
       :hints (("Goal"
                :in-theory (e/d (bitp) ())))))

    (local
     (defthm fa-c-chain-when-valid-args
       (implies (and (valid-fa-c-chain-args-p m x)
                     (bitp (SV::SVEX-EVAL$ x env))
                     (bitp (SV::SVEX-EVAL$ y env))
                     (bitp (SV::SVEX-EVAL$ z env)))
                (equal (FA-C-CHAIN (SV::SVEX-EVAL$ m env)
                                   (SV::SVEX-EVAL$ x env)
                                   (SV::SVEX-EVAL$ y env)
                                   (SV::SVEX-EVAL$ z env))
                       (FA-C-CHAIN 0
                                   (SV::SVEX-EVAL$ x env)
                                   (SV::SVEX-EVAL$ y env)
                                   (SV::SVEX-EVAL$ z env))))
       :hints (("Goal"
                :in-theory (e/d (bitp
                                 SV::SVEX-QUOTE->VAL
                                 fa-c-chain)
                                ())))))

    (local
     (defthm bitp-of-logior/and/c-spec
       (implies (and (bitp x)
                     (bitp y))
                (and (bitp (logior x y))
                     (bitp (logxor x y))
                     (bitp (logand x y))
                     (implies (bitp z)
                              (bitp (c-spec (list x y z))))
                     (implies (bitp z)
                              (bitp (s-spec (list x y z))))))
       :hints (("Goal"
                :in-theory (e/d (bitp) ())))))

    (defret <fn>-is-correct-bitp
      (implies (and valid
                    (sv::Svex-p test)
                    (sv::Svex-p then)
                    (sv::Svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-bitand
      :hints (("Goal"
               :in-theory (e/d (csel-simplify-end-at-bitand
                                SVL::BIT-LISTP-OF-SVEX-FN
                                SV::SVEX-APPLY
                                SV::SVEX-APPLY$
                                SV::SVEX-CALL->FN SV::SVEX-CALL->args
                                SVL::BIT-LISTP-OF-SVEX
                                )
                               (valid-fa-c-chain-args-p
                                ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                SYMBOL-LISTP
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$-LST
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (defret <fn>-is-correct-bitp
      (implies (and valid
                    (sv::Svex-p test)
                    (sv::Svex-p then)
                    (sv::Svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-bitxor
      :hints (("Goal"
               :in-theory (e/d (ha+1-s-chain-pattern-2-p
                                csel-simplify-end-at-bitxor
                                SVL::BIT-LISTP-OF-SVEX-FN
                                SV::SVEX-APPLY
                                SV::SVEX-APPLY$
                                SV::SVEX-CALL->FN SV::SVEX-CALL->args
                                SVL::BIT-LISTP-OF-SVEX
                                )
                               (valid-fa-c-chain-args-p
                                ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                SYMBOL-LISTP
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$-LST
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (defret <fn>-is-correct-bitp
      (implies (and valid
                    (sv::Svex-p test)
                    (sv::Svex-p then)
                    (sv::Svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-special-bitxor
      :hints (("Goal"
               :in-theory (e/d (csel-simplify-end-at-special-bitxor
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex
                                )
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (defret <fn>-is-correct-bitp
      (implies (and valid
                    (sv::Svex-p test)
                    (sv::Svex-p then)
                    (sv::Svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                    (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-special-bitand
      :hints (("Goal"
               :in-theory (e/d (csel-simplify-end-at-special-bitand
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex
                                )
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (defret-mutual implies-args-are-bitp
      (defret <fn>-is-correct-bitp
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-fa-c)
      (defret <fn>-is-correct-bitp
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-fa-s)
      (defret <fn>-is-correct-bitp
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-ha-s)
      (defret <fn>-is-correct-bitp
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-ha-c)
      (defret <fn>-is-correct-bitp
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (and (bitp (sv::svex-eval$ test (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ then (rp-evlt env-term a)))
                      (bitp (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify)
      :hints (("Goal"
               :expand ((csel-simplify-fa-c test then else
                                            :limit limit)
                        (csel-simplify-fa-s test then else
                                            :limit limit)
                        (csel-simplify-ha-s test then else
                                            :limit limit)
                        (csel-simplify-ha-c test then else
                                            :limit limit)
                        (csel-simplify test then else
                                       :limit limit))
               :do-not-induct t
               :in-theory (e/d (;;bitp
                                SVL::BIT-LISTP-OF-SVEX-FN
                                SV::SVEX-APPLY
                                SV::SVEX-APPLY$
                                SV::SVEX-CALL->FN SV::SVEX-CALL->args
                                SVL::BIT-LISTP-OF-SVEX
                                ;;bitp-of-svex-eval$-casesplit-trigger
                                ;;bitp
                                )
                               (;;WARRANTS-FOR-ADDER-PATTERN-MATCH
                                valid-fa-c-chain-args-p
                                ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                SYMBOL-LISTP
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$-LST
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (local
     (defthm s-spec-to-logxor
       (implies (and (bitp x)
                     (bitp y)
                     (bitp z))
                (equal (s-spec (list x y z))
                       (logxor x y z)))
       :hints (("Goal"
                :in-theory (e/d (bitp) ())))))

    (local
     (defthm 4vec-fncs-to-logops-when-bitp
       (implies (and (bitp x)
                     (bitp y))
                (and (equal (sv::4vec-bitxor x y) (logxor x y))
                     (equal (sv::4vec-bitor x y) (logior x y))
                     (equal (sv::4vec-bitand x y) (logand x y))))
       :hints (("Goal"
                :in-theory (e/d () (bitp))))))

    (defret <fn>-is-correct
      (implies (and valid
                    (sv::svex-p test)
                    (sv::svex-p then)
                    (sv::svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                      (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                          (sv::svex-eval$ then (rp-evlt env-term a))
                        (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-bitxor
      :hints (("goal"
               :in-theory (e/d (HA+1-S-CHAIN-PATTERN-2-P
                                csel-simplify-end-at-bitxor
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex)
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (defret <fn>-is-correct
      (implies (and valid
                    (sv::svex-p test)
                    (sv::svex-p then)
                    (sv::svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                      (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                          (sv::svex-eval$ then (rp-evlt env-term a))
                        (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-bitand
      :hints (("goal"
               :in-theory (e/d (csel-simplify-end-at-bitand
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex)
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))

    (Local
     (defthm loghead-1-of-bitp
       (Implies (bitp x)
                (equal (loghead 1 x) x))))

    (defret <fn>-is-correct
      (implies (and valid
                    (sv::svex-p test)
                    (sv::svex-p then)
                    (sv::svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                      (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                          (sv::svex-eval$ then (rp-evlt env-term a))
                        (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-special-bitxor
      :hints (("goal"
               :in-theory (e/d (csel-simplify-end-at-special-bitxor
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex)
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                ACL2::LOGAND-WITH-MASK)))))

    (local
     (defthm c-spec-of-0
       (and (equal (c-spec (list x y 0))
                   (c-spec (list x y)))
            (equal (c-spec (list x 0 y))
                   (c-spec (list x y)))
            (equal (c-spec (list 0 x y))
                   (c-spec (list x y))))
       :hints (("Goal"
                :in-theory (e/d (SUM sum-list c-spec) ())))))

    (local
     (defthm c-spec-logand-equiv
       (implies (and (bitp x)
                     (bitp y))
                (equal (equal (c-spec (list x y))
                              (logand x y))
                       t))
       :hints (("Goal"
                :in-theory (e/d (bitp) ())))))

    (defret <fn>-is-correct
      (implies (and valid
                    (sv::svex-p test)
                    (sv::svex-p then)
                    (sv::svex-p else)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                      (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                          (sv::svex-eval$ then (rp-evlt env-term a))
                        (sv::svex-eval$ else (rp-evlt env-term a)))))
      :fn csel-simplify-end-at-special-bitand
      :hints (("goal"
               :in-theory (e/d (csel-simplify-end-at-special-bitand
                                svl::bit-listp-of-svex-fn
                                sv::svex-apply
                                sv::svex-apply$
                                sv::svex-call->fn sv::svex-call->args
                                svl::bit-listp-of-svex)
                               (valid-fa-c-chain-args-p
                                acl2::symbolp-of-car-when-symbol-listp
                                symbol-listp
                                svl::width-of-svex-extn-correct$-lst
                                svl::width-of-svex-extn-correct$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                ACL2::LOGAND-WITH-MASK)))))

    (defret-mutual evals-correctly
      (defret <fn>-is-correct
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                        (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                            (sv::svex-eval$ then (rp-evlt env-term a))
                          (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-fa-c)
      (defret <fn>-is-correct
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                        (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                            (sv::svex-eval$ then (rp-evlt env-term a))
                          (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-fa-s)
      (defret <fn>-is-correct
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                        (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                            (sv::svex-eval$ then (rp-evlt env-term a))
                          (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-ha-s)
      (defret <fn>-is-correct
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                        (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                            (sv::svex-eval$ then (rp-evlt env-term a))
                          (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify-ha-c)
      (defret <fn>-is-correct
        (implies (and valid
                      (sv::Svex-p test)
                      (sv::Svex-p then)
                      (sv::Svex-p else)
                      (rp-term-listp context)
                      (valid-sc env-term a)
                      (eval-and-all context a)
                      (falist-consistent-aux env env-term)
                      (svl::width-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->width-extns config))
                      (svl::integerp-of-svex-extn-correct$-lst
                       (svl::svex-reduce-config->integerp-extns config))
                      (force (warrants-for-adder-pattern-match)))
                 (equal (sv::svex-eval$ new-svex (rp-evlt env-term a))
                        (if (equal (sv::svex-eval$ test (rp-evlt env-term a)) 1)
                            (sv::svex-eval$ then (rp-evlt env-term a))
                          (sv::svex-eval$ else (rp-evlt env-term a)))))
        :fn csel-simplify)
      :hints (("Goal"
               :expand ((csel-simplify-fa-c test then else
                                            :limit limit)
                        (csel-simplify-fa-s test then else
                                            :limit limit)
                        (csel-simplify-ha-s test then else
                                            :limit limit)
                        (csel-simplify-ha-c test then else
                                            :limit limit)
                        (csel-simplify test then else
                                       :limit limit))
               :do-not-induct t
               :in-theory (e/d (;;bitp
                                SVL::BIT-LISTP-OF-SVEX-FN
                                SV::SVEX-APPLY
                                SV::SVEX-APPLY$
                                SV::SVEX-CALL->FN SV::SVEX-CALL->args
                                SVL::BIT-LISTP-OF-SVEX
                                ;;bitp-of-svex-eval$-casesplit-trigger
                                ;;bitp
                                )
                               (;;WARRANTS-FOR-ADDER-PATTERN-MATCH

                                ;;BITP-OF-SVEX-EVAL$-CASESPLIT-TRIGGER

                                valid-fa-c-chain-args-p
                                ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP
                                SYMBOL-LISTP
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$-LST
                                SVL::WIDTH-OF-SVEX-EXTN-CORRECT$
                                intersection-equal
                                rp-term-listp
                                falist-consistent-aux
                                valid-sc
                                eval-and-all
                                )))))))

(define csel-simplify-main ((svex sv::svex-p)
                            &key
                            ((env) 'env)
                            ((context rp-term-listp) 'context)
                            ((config svl::svex-reduce-config-p) 'config))
  :returns (res sv::svex-p :hyp (sv::svex-p svex))
  (b* (((mv test then else valid)
        (csel-branch svex))
       ((unless valid)
        svex)
       ((mv new-svex valid)
        (csel-simplify test then else :limit *large-number*)))
    (if valid
        new-svex
      svex))
  ///
  (defret <fn>-is-correct
    (implies (and (sv::Svex-p svex)
                  (rp-term-listp context)
                  (valid-sc env-term a)
                  (eval-and-all context a)
                  (falist-consistent-aux env env-term)
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (svl::integerp-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->integerp-extns config))
                  (force (warrants-for-adder-pattern-match)))
             (and (equal (sv::svex-eval$ res (rp-evlt env-term a))
                         (sv::svex-eval$ svex (rp-evlt env-term a)))
                  ))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d ()
                             ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Simplification for paralel-prefix logic

(define ppx-mergeable-precheck--collect-fa-c-args (svex)
  :returns (list-of-fa-c-args)
  (case-match svex
    (('sv::bitor x y)
     (append (ppx-mergeable-precheck--collect-fa-c-args x)
             (ppx-mergeable-precheck--collect-fa-c-args y)))
    (('sv::id x)
     (ppx-mergeable-precheck--collect-fa-c-args x))
    (('fa-c-chain & x y z)
     (list (list svex x y z)))
    (('ha-c-chain x y)
     (list (list svex x y 0)))
    (('sv::bitand x y)
     (list (list svex x y 0))))
  ///
  (defret svex-p-lemma-of-<fn>
    (implies (sv::Svex-p svex)
             (sv::svexlistlist-p list-of-fa-c-args))))

(define ppx-mergeable-find-matching-m2-aux (x y collected-fa-c-args)
  :returns (mv (foundp booleanp)
               (fa-c-term sv::Svex-p :hyp (sv::svexlistlist-p collected-fa-c-args)))
  (if (atom collected-fa-c-args)
      (mv nil 0)
    (b* (((unless (svl::equal-len (car collected-fa-c-args) 4))
          (ppx-mergeable-find-matching-m2-aux x y (cdr collected-fa-c-args)))
         ((list fa-c-term arg1 arg2 arg3) (car collected-fa-c-args))
         ((when (or (and (equal x arg1)
                         (or (equal y arg2)
                             (equal y arg3)))
                    (and (equal x arg2)
                         (or (equal y arg1)
                             (equal y arg3)))
                    (and (equal x arg3)
                         (or (equal y arg1)
                             (equal y arg2)))))
          (mv t fa-c-term)))
      (ppx-mergeable-find-matching-m2-aux x y (cdr collected-fa-c-args)))))

(define ppx-mergeable-find-matching-m2 ((svex sv::Svex-p)
                                        collected-fa-c-args
                                        &key
                                        ((config svl::svex-reduce-config-p)
                                         'config))
  ;; Given a collected-fa-c-args, finds and extracts a matching m2 term from a given bitand list.
  :returns (mv (foundp booleanp)
               (remaining-bitand sv::svex-p :hyp (sv::Svex-p svex))
               (m2-term sv::Svex-p :hyp (sv::Svex-p svex))
               (fa-c-term sv::Svex-p :hyp (sv::svexlistlist-p collected-fa-c-args)))
  :verify-guards :after-returns
  (case-match svex
    (('sv::bitand x y)
     (b* (((mv foundp rest-bitand m2-term fa-c-term)
           (ppx-mergeable-find-matching-m2 x collected-fa-c-args))
          ((when foundp)
           (mv foundp
               (ex-adder-fnc-from-unfloat
                (svl::bitand/or/xor-simple-constant-simplify 'sv::bitand rest-bitand y))
               m2-term fa-c-term))
          ((mv foundp rest-bitand m2-term fa-c-term)
           (ppx-mergeable-find-matching-m2 y collected-fa-c-args))
          ((when foundp)
           (mv foundp
               (ex-adder-fnc-from-unfloat
                (svl::bitand/or/xor-simple-constant-simplify 'sv::bitand rest-bitand x))
               m2-term fa-c-term)))
       (mv nil 0 0 0)))
    (('sv::bitxor x y)
     (b* (((mv found fa-c-term)
           (ppx-mergeable-find-matching-m2-aux x y collected-fa-c-args)))
       (mv found -1 svex fa-c-term)))
    (('sv::bitor x y) ;; instead of XOR, OR can work too.
     (b* (((mv found fa-c-term)
           (ppx-mergeable-find-matching-m2-aux x y collected-fa-c-args)))
       (mv found -1 svex fa-c-term)))
    (('ha-s-chain x y)
     (b* (((mv found fa-c-term)
           (ppx-mergeable-find-matching-m2-aux x y collected-fa-c-args)))
       (mv found -1 svex fa-c-term)))
    (('sv::id x)
     (ppx-mergeable-find-matching-m2 x collected-fa-c-args))
    (&
     (mv nil 0 0 0)))

  ///

  (defret <fn>-is-correct
    (implies (and (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (sv::svex-p svex)
                  (warrants-for-adder-pattern-match)
                  foundp
                  )
             (equal (sv::4vec-bitand (sv::svex-eval$ remaining-bitand env)
                                     (sv::svex-eval$ m2-term env))
                    (sv::svex-eval$ svex env)))
    :hints (("Goal"
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-apply$
                              sv::svex-apply
                              ha-s-chain
                              sv::svex-call->args)
                             ()))))

  )

(define ppx-mergeable-extract-matching-m2 ((svex sv::Svex-p)
                                           collected-fa-c-args
                                           &key
                                           ((config svl::svex-reduce-config-p) 'config))
  :verify-guards :after-returns
  :returns (mv (foundp booleanp)
               (remaining-bitor sv::Svex-p :hyp (sv::Svex-p svex))
               (remaining-bitand sv::svex-p :hyp (sv::Svex-p svex))
               (m2-term sv::Svex-p :hyp (sv::Svex-p svex))
               (fa-c-term sv::Svex-p :hyp (sv::svexlistlist-p collected-fa-c-args)))
  (case-match svex
    (('sv::bitor x y)
     (b* (((mv foundp remaining-bitand m2-term fa-c-term)
           (ppx-mergeable-find-matching-m2 svex collected-fa-c-args))
          ((when foundp)
           (mv foundp 0 remaining-bitand m2-term fa-c-term))

          ((mv foundp remaining-bitor remaining-bitand m2-term fa-c-term)
           (ppx-mergeable-extract-matching-m2 x collected-fa-c-args))
          ((when foundp)
           (mv foundp
               (ex-adder-fnc-from-unfloat
                (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor remaining-bitor y))
               remaining-bitand m2-term fa-c-term))
          ((mv foundp remaining-bitor remaining-bitand m2-term fa-c-term)
           (ppx-mergeable-extract-matching-m2 y collected-fa-c-args))
          ((when foundp)
           (mv foundp
               (ex-adder-fnc-from-unfloat
                (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor remaining-bitor x))
               remaining-bitand m2-term fa-c-term)))
       (mv nil svex 0 0 0)))
    ((fn & &)
     (b* (((unless (or (equal fn 'sv::bitxor)
                       (equal fn 'sv::bitand)
                       (equal fn 'ha-s-chain)
                       (equal fn 'ha-c-chain)))
           (mv nil svex 0 0 0))
          ((mv foundp remaining-bitand m2-term fa-c-term)
           (ppx-mergeable-find-matching-m2 svex collected-fa-c-args)))
       (mv foundp 0 remaining-bitand m2-term fa-c-term)))
    (('sv::id x)
     (ppx-mergeable-extract-matching-m2 x collected-fa-c-args))
    (& (mv nil svex 0 0 0)))
  ///

  (defret <fn>-is-correct
    (implies (and (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (sv::svex-p svex)
                  (warrants-for-adder-pattern-match)
                  foundp
                  )
             (equal (sv::4vec-bitor (sv::svex-eval$ remaining-bitor env)
                                    (sv::4vec-bitand (sv::svex-eval$ remaining-bitand env)
                                                     (sv::svex-eval$ m2-term env)))
                    (sv::svex-eval$ svex env)))
    :hints (("Goal"
             :in-theory (e/d (sv::svex-call->fn
                              sv::svex-apply$
                              sv::svex-apply
                              ha-s-chain ha-c-chain
                              sv::svex-call->args)
                             ())))))

(local
 (defthm SVEX-QUOTE->VAL-when-integerp
   (implies (integerp x)
            (equal (sv::SVEX-QUOTE->VAL x) x))
   :hints (("Goal"
            :in-theory (e/d (sv::SVEX-QUOTE->VAL) ())))))

(define ppx-mergeable-node-pull-common-args (m2-term fa-c-term)
  :returns (mv success
               m2-regular-type-p
               (shared-arg1 sv::Svex-p :hyp (sv::Svex-p m2-term))
               (shared-arg2 sv::Svex-p :hyp (sv::Svex-p m2-term))
               (other-arg sv::Svex-p :hyp (sv::Svex-p fa-c-term)))
  (b* (((mv success m2-regular-type-p m2-arg1 m2-arg2)
        (case-match m2-term
          (('sv::bitxor x y)
           (mv t t x y))
          (('ha-s-chain x y)
           (mv t t x y))
          (('sv::bitor x y)
           (mv t nil x y))
          (& (mv nil nil 0 0))))
       ((unless success)
        (mv nil nil 0 0 0))
       ((mv success fa-c-arg1 fa-c-arg2 fa-c-arg3)
        (case-match fa-c-term
          (('fa-c-chain m x y z) (mv (valid-fa-c-chain-args-p m x)
                                     x y z))
          (('sv::bitand x y) (mv t x y 0))
          (('ha-c-chain x y) (mv t x y 0))
          (& (mv nil 0 0 0))))
       ((unless success)
        (mv nil nil 0 0 0))
       ((mv success shared-arg1 shared-arg2 other-arg)
        (cond ((or* (and* (equal fa-c-arg1 m2-arg1)
                          (equal fa-c-arg2 m2-arg2))
                    (and* (equal fa-c-arg1 m2-arg2)
                          (equal fa-c-arg2 m2-arg1)))
               (mv t m2-arg1 m2-arg2 fa-c-arg3))
              ((or* (and* (equal fa-c-arg1 m2-arg1)
                          (equal fa-c-arg3 m2-arg2))
                    (and* (equal fa-c-arg1 m2-arg2)
                          (equal fa-c-arg3 m2-arg1)))
               (mv t m2-arg1 m2-arg2 fa-c-arg2))
              ((or* (and* (equal fa-c-arg2 m2-arg1)
                          (equal fa-c-arg3 m2-arg2))
                    (and* (equal fa-c-arg2 m2-arg2)
                          (equal fa-c-arg3 m2-arg1)))
               (mv t m2-arg1 m2-arg2 fa-c-arg1))
              (t (mv nil 0 0 0)))))
    (mv success m2-regular-type-p shared-arg1 shared-arg2 other-arg))
  ///

  (defret <fn>-is-correct
    (implies (and success
                  (warrants-for-adder-pattern-match))
             (and (implies (and (bitp (sv::svex-eval$ shared-arg1 env))
                                (bitp (sv::svex-eval$ shared-arg2 env))
                                (case-split m2-regular-type-p))
                           (equal (s-spec (list (sv::svex-eval$ shared-arg1 env)
                                                (sv::svex-eval$ shared-arg2 env)))
                                  (sv::svex-eval$ m2-term env)))

                  (implies (and (bitp (sv::svex-eval$ shared-arg1 env))
                                (bitp (sv::svex-eval$ shared-arg2 env))
                                (not m2-regular-type-p))
                           (equal
                            (binary-or (sv::svex-eval$ shared-arg1 env)
                                       (sv::svex-eval$ shared-arg2 env))
                            (sv::svex-eval$ m2-term env)))

                  (implies (and (bitp (sv::svex-eval$ shared-arg1 env))
                                (bitp (sv::svex-eval$ shared-arg2 env))
                                (bitp (sv::svex-eval$ other-arg env)))
                           (equal (c-spec (list (sv::svex-eval$ shared-arg1 env)
                                                (sv::svex-eval$ shared-arg2 env)
                                                (sv::svex-eval$ other-arg env)))
                                  (sv::svex-eval$ fa-c-term env)))))
    :hints (("Goal"
             :in-theory (e/d (or*
                              bitp
                              SV::SVEX-APPLY$
                              SV::SVEX-CALL->FN
                              SV::SVEX-CALL->args)
                             ()))))

  #|(defret <fn>-is-correct-2
  (implies (and success
  (warrants-for-adder-pattern-match))
  (implies (and (bitp (sv::svex-eval$ shared-arg1 env))
  (bitp (sv::svex-eval$ shared-arg2 env))
  (equal other-arg -1))
  (equal (fa-c-chain 0
  (sv::svex-eval$ shared-arg1 env)
  (sv::svex-eval$ shared-arg2 env)
  -1)
  (sv::svex-eval$ fa-c-term env))))
  :hints (("Goal"
  :in-theory (e/d (or*
  bitp
  SV::SVEX-APPLY$
  SV::SVEX-CALL->FN
  SV::SVEX-CALL->args)
  ()))))|#
  )

(local
 (defthm 4vec-bitor-of-minus1
   (equal (sv::4vec-bitor -1 x)
          -1)
   :hints (("Goal"
            :in-theory (e/d (SV::3VEC-BITOR
                             sv::4vec-bitor)
                            ())))))

(define ppx-simplify-mergeable-node-simplify-args ((remaining-bitor sv::Svex-p)
                                                   (fa-c-arg1 sv::Svex-p)
                                                   (fa-c-arg2 sv::Svex-p)
                                                   (fa-c-arg3 sv::Svex-p)
                                                   &key
                                                   ((env) 'env)
                                                   ((context rp-term-listp) 'context)
                                                   ((config svl::svex-reduce-config-p) 'config))
  (b* ((svl::under-xor nil)
       (svl::leave-depth 2)
       (leaves (svl::bitand/or/xor-collect-leaves remaining-bitor 'sv::bitor))
       (svl::nodes-to-skip-alist nil)
       ((mv fa-c-arg1 &) (svl::bitand/bitor-cancel-repeated-aux fa-c-arg1 leaves 0))
       ((mv fa-c-arg2 &) (svl::bitand/bitor-cancel-repeated-aux fa-c-arg2 leaves 0))
       ((mv fa-c-arg3 &) (svl::bitand/bitor-cancel-repeated-aux fa-c-arg3 leaves 0)))
    (mv fa-c-arg1 fa-c-arg2 fa-c-arg3)))

(define ppx-simplify-mergeable-node ((svex sv::svex-p)
                                     &key
                                     ((limit natp) 'limit)
                                     ((env) 'env)
                                     ((context rp-term-listp) 'context)
                                     ((config svl::svex-reduce-config-p) 'config))
  :measure (nfix limit)
  :no-function t
  :Returns (res-svex sv::svex-p :hyp (sv::svex-p svex))
  :verify-guards :after-returns
  (if (zp limit) ;; proving the measure is not easy so I will use memoize-partial
      svex
    (let ((limit (1- limit)))
      (b* (((unless (and (consp svex)
                         (equal (car svex) 'sv::bitor)
                         (svl::equal-len (cdr svex) 2)))
            svex)

           (pattern-fn-call-list (look-for-fa-c-chain-pattern svex))
           ((when (consp pattern-fn-call-list))
            (b* ((pattern-fn-call (pull-the-first-applicable-adder-pattern nil pattern-fn-call-list nil))
                 ((unless pattern-fn-call)
                  svex)
                 ((pattern-fn-call x) pattern-fn-call)
                 (svex (pattern-call x)))
              (zero-fa-c-chain-extra-arg svex)))

           (collected-fa-c-args (ppx-mergeable-precheck--collect-fa-c-args svex))
           ((mv found remaining-bitor remaining-bitand m2-term fa-c-term)
            (ppx-mergeable-extract-matching-m2 svex collected-fa-c-args))
           ((unless found)
            (b* (;; if not found try simplifing first
                 #|((mv new-svex &) ;; NOTE: THIS MAY NEVER BE USEFUL.
                 (simplify-to-find-fa-c-patterns-aux
                 x 5 :strength 2
                 :inside-out t))|#
                 (new-svex (svl::bitand/or/xor-cancel-repeated
                            'sv::bitor (first (cdr svex)) (second (cdr svex))
                            :leave-depth 5
                            :nodes-to-skip-alist nil))
                 (simp-changed (not (equal new-svex svex)))
                 (new-new-svex (if simp-changed
                                   (ppx-simplify-mergeable-node new-svex)
                                 new-svex))
                 ((when (not (equal new-new-svex new-svex)))
                  new-new-svex)
                 ;; if here, it means svl::bitand/or/xor-cancel-repeated didn't
                 ;; help.
                 ((mv common-terms pulled-svex)
                  (svl::bitor-of-and-pull-commons-aux svex
                                                      :leave-depth 5
                                                      :collect-from-arg1 nil))
                 ((mv common-terms pulled-svex)
                  (if common-terms
                      (mv common-terms pulled-svex)
                    ;; try again but collect from the first arg this time.
                    (svl::bitor-of-and-pull-commons-aux svex
                                                        :leave-depth 5
                                                        :collect-from-arg1 t)))
                 ((unless common-terms) svex)
                 (new-svex (ppx-simplify-mergeable-node pulled-svex))
                 ((when (equal new-svex pulled-svex)) svex))
              (svl::bitand/or/xor-simple-constant-simplify
               'sv::bitand common-terms new-svex)))
           ((mv remove-success remaining-bitor)
            (svl::bitor-remove-node remaining-bitor fa-c-term))
           ((unless remove-success) svex)

           (remaining-bitor (ex-adder-fnc-from-unfloat remaining-bitor))

           ((mv success & shared-arg1 shared-arg2 other-arg)
            (ppx-mergeable-node-pull-common-args m2-term fa-c-term))

           ((unless success) svex)

           ((Unless (and (svl::bitp-of-svex other-arg)
                         (svl::bitp-of-svex remaining-bitor)
                         (or (svl::bitp-of-svex remaining-bitand)
                             #|(equal remaining-bitand -1)|#)
                         (svl::bitp-of-svex shared-arg1)
                         (svl::bitp-of-svex shared-arg2)))
            (progn$ (cwe "Failed: ~p0. remaining-bitor: ~p1 remaining-bitand: ~p2 ~%Config:~p3,context:~p4,env:~p5"
                         (list (cons :other-arg (svl::bitp-of-svex other-arg))
                               (cons :remaining-bitor (svl::bitp-of-svex remaining-bitor))
                               (cons :remaining-bitand (svl::bitp-of-svex remaining-bitand))
                               (cons :shared-arg1 (svl::bitp-of-svex shared-arg1))
                               (cons :shared-arg2 (svl::bitp-of-svex shared-arg2)))
                         remaining-bitor remaining-bitand
                         config context env)
                    svex))

           (new-inner-bitor (ex-adder-fnc-from-unfloat
                             (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor
                                                                          other-arg
                                                                          remaining-bitand)))
           #|((mv shared-arg1 shared-arg2 new-inner-bitor)
           (ppx-simplify-mergeable-node-simplify-args remaining-bitor shared-arg1 shared-arg2 new-inner-bitor))|#

           (new-inner-bitor (ppx-simplify-mergeable-node new-inner-bitor))

           #|((mv shared-arg1 shared-arg2 new-inner-bitor)
           (ppx-simplify-mergeable-node-simplify-args remaining-bitor shared-arg1 shared-arg2 new-inner-bitor))|#

           (new-fa-c-chain (create-fa-c-chain-instance shared-arg1 shared-arg2 new-inner-bitor))

           ;; TODO:
           ;; MAYBE I SHOULD TRY CLEARING  THE ARGS OF NEW-FA-C-CHAIN HERE WITH
           ;; REPEATED    CHECK    (svl::bitand/or/xor-cancel-repeated)    FROM
           ;; REMAINING-BITOR TO HELP THE CONSTANT 1 PROPAGATION CASE......
           ;; IDEALLY BEFORE THE RECURSIVE CALL.....

           (new-bitor (ex-adder-fnc-from-unfloat
                       (svl::bitand/or/xor-simple-constant-simplify 'sv::bitor
                                                                    remaining-bitor
                                                                    new-fa-c-chain))))
        (ppx-simplify-mergeable-node new-bitor))))
  ///

  (local
   (defthmd bitp-of-svex-eval$-casesplit-trigger
     (implies (and (sv::svex-p svex)
                   (rp::rp-term-listp context)
                   (rp::valid-sc env-term a)
                   (rp::eval-and-all context a)
                   (rp::falist-consistent-aux env env-term)
                   (svl::width-of-svex-extn-correct$-lst
                    (svl::svex-reduce-config->width-extns config))
                   (svl::integerp-of-svex-extn-correct$-lst
                    (svl::svex-reduce-config->integerp-extns config)))
              (equal (svl::bitp-of-svex svex )
                     (and (hide (svl::bitp-of-svex svex))
                          (bitp (sv::Svex-eval$ svex (rp-evlt env-term a))))))
     :hints (("Goal"
              :expand (hide (svl::bitp-of-svex svex ))
              :in-theory (e/d () ())))))

  (local
   (defthm ppx-merge-lemma
     (implies (and (bitp x)
                   (bitp y)
                   (bitp z1)
                   (bitp z2))
              (and (equal (c-spec (list x y (sv::4vec-bitor z2 z1)))
                          (sv::4vec-bitor (c-spec (list x y z1))
                                          (sv::4vec-bitand
                                           (if (mv-nth ;; m2-term can be bitxor
                                                ;; or bitor. This helps with a
                                                ;; nice caseplit between the two.
                                                1
                                                (ppx-mergeable-node-pull-common-args
                                                 (mv-nth 3
                                                         (ppx-mergeable-extract-matching-m2
                                                          svex
                                                          (ppx-mergeable-precheck--collect-fa-c-args svex)))
                                                 (mv-nth 4
                                                         (ppx-mergeable-extract-matching-m2
                                                          svex
                                                          (ppx-mergeable-precheck--collect-fa-c-args svex)))))

                                               (s-spec (list x y))
                                             (binary-or x y))
                                           z2)))
                   #|(equal (sv::4vec-bitor (c-spec (list x y z1))
                   (sv::4vec-bitand (b-or x y)
                   z2))
                   (sv::4vec-bitor (c-spec (list x y z1))
                   (sv::4vec-bitand (ha-s-chain x y)
                   z2)))|#))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (defret <fn>-is-correct
    (implies (and (sv::svex-p svex)
                  (rp::rp-term-listp context)
                  (rp::valid-sc env-term a)
                  (rp::eval-and-all context a)
                  (rp::falist-consistent-aux env env-term)
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (svl::integerp-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->integerp-extns config))
                  (force (warrants-for-adder-pattern-match)))
             (equal (sv::svex-eval$ res-svex (rp-evlt env-term a))
                    (sv::svex-eval$ svex (rp-evlt env-term a))))
    :hints (("Goal"
             :do-not-induct t
             :induct (ppx-simplify-mergeable-node svex)
             :expand ((:free (args) (sv::svex-apply 'sv::bitor args))
                      (:free (args) (sv::svex-apply$ 'sv::bitor args))
                      (:free (args) (sv::svex-apply 'sv::bitand args)))
             :in-theory (e/d (;;ppx-mergeable-node-pull-common-args
                              or*
                              sv::svex-call->fn
                              ;;sv::svex-apply$
                              ;;sv::svex-apply
                              ;;ha-s-chain
                              sv::svex-call->args
                              ;;bitp
                              )
                             ()))
            (and stable-under-simplificationp
                 '(:use ((:instance look-for-fa-c-chain-pattern-correct-pattern
                                    (pattern (pull-the-first-applicable-adder-pattern
                                              nil (look-for-fa-c-chain-pattern svex) nil))
                                    (env (rp-evlt env-term a)))
                         ;; unnecessary but just in case:
                         (:instance look-for-fa-c-chain-pattern-correct-pattern
                                    (pattern (pull-the-first-applicable-adder-pattern
                                              nil (look-for-fa-c-chain-pattern svex) nil))
                                    (env env)))
                        )))
    ))

(defines ppx-simplify
  :verify-guards nil
  (define ppx-simplify ((svex sv::svex-p)
                        &key
                        ((env) 'env)
                        ((context rp-term-listp) 'context)
                        ((config svl::svex-reduce-config-p) 'config))
    :returns (res-svex sv::svex-p :hyp (sv::svex-p svex))
    :measure (sv::Svex-count svex)
    (sv::svex-case
     svex
     :var svex
     :quote svex
     :call (b* ((args (ppx-simplify-lst svex.args))
                (new-svex (sv::svex-call svex.fn args))
                (new-svex (csel-simplify-main new-svex))
                (bitor-p (case-match new-svex (('sv::bitor & &) t)))
                ;; WARNING: TODO: DANGEROUS TO DO THIS HERE!!!!!!!!
                ;; But this may help with the case where a constant 1 is propagated
                ;; in the ppx adders...
                #|(new-svex (if bitor-p
                (svl::bitand/or/xor-cancel-repeated
                'sv::bitor (first (cdr new-svex)) (second (cdr new-svex))
                :leave-depth 1)
                new-svex))|#)
             (if bitor-p
                 (ppx-simplify-mergeable-node new-svex :limit 10000)
               new-svex))))
  (define ppx-simplify-lst ((lst sv::svexlist-p)
                            &key
                            ((env) 'env)
                            ((context rp-term-listp) 'context)
                            ((config svl::svex-reduce-config-p) 'config))
    :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        nil
      (hons (ppx-simplify (car lst))
            (ppx-simplify-lst (cdr lst)))))
  ///
  (verify-guards ppx-simplify-fn)

  (memoize 'ppx-simplify-fn
           ;; :condition '(eq (sv::svex-kind svex) :call)
           )

  (defret-mutual ppx-simplify-correct
    (defret <fn>-is-correct
      (implies (and (sv::svex-p svex)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svex-eval$ res-svex (rp-evlt env-term a))
                      (sv::svex-eval$ svex (rp-evlt env-term a))))
      :fn ppx-simplify)
    (defret <fn>-is-correct
      (implies (and (sv::svexlist-p lst)
                    (rp-term-listp context)
                    (valid-sc env-term a)
                    (eval-and-all context a)
                    (falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match)))
               (equal (sv::svexlist-eval$ res-lst (rp-evlt env-term a))
                      (sv::svexlist-eval$ lst (rp-evlt env-term a))))
      :fn ppx-simplify-lst)
    :hints (("Goal"
             :do-not-induct t
             :expand ((ppx-simplify-lst nil)
                      (ppx-simplify svex)
                      (ppx-simplify-lst lst)
                      (:free (args) (SV::SVEX-APPLY 'SV::BITOR args)))
             :in-theory (e/d (SV::SVEX-CALL->ARGS
                              SV::SVEX-CALL->fn)
                             (csel-simplify-main-is-correct)))
            (and stable-under-simplificationp
                 '(:use (:instance csel-simplify-main-is-correct
                                   (svex
                                    (sv::svex-call (car svex)
                                                   (ppx-simplify-lst (cdr svex)))))))))

  )

(define ppx-simplify-alist ((alist sv::svex-alist-p)
                            &key
                            ((env) 'env)
                            ((context rp-term-listp) 'context)
                            ((config svl::svex-reduce-config-p) 'config))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
  (if (atom alist)
      nil
    (acons (caar alist)
           (ppx-simplify (cdar alist))
           (ppx-simplify-alist (cdr alist))))
  ///
  (defret <fn>-is-correct
    (implies (and (sv::svex-alist-p alist)
                  (rp-term-listp context)
                  (valid-sc env-term a)
                  (eval-and-all context a)
                  (falist-consistent-aux env env-term)
                  (svl::width-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->width-extns config))
                  (svl::integerp-of-svex-extn-correct$-lst
                   (svl::svex-reduce-config->integerp-extns config))
                  (force (warrants-for-adder-pattern-match)))
             (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                    (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
    :hints (("goal"
             :do-not-induct t
             :induct (ppx-simplify-alist alist)
             :in-theory (e/d (sv::svex-alist-eval$)
                             ())))))

#|(ppx-simplify-mergeable-node
'(SV::BITOR
(SV::BITAND
(SV::BITAND
(sv::bitxor x y)
o5)
o6)
(FA-C-CHAIN
1 (HA-C-CHAIN o4 o3)
x
y))
:limit 1000
:config nil)|#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (define rw-adder-corner-case ((svex sv::svex-p)
;;                               &key
;;                               ((env) 'env)
;;                               ((context rp-term-listp) 'context)
;;                               ((config svl::svex-reduce-config-p) 'config))
;;   :Returns (mv (res sv::svex-p :hyp (sv::svex-p svex))
;;                changed)
;;   :prepwork ((create-case-match-macro negated-fa-c-chain-0
;;                                       ('SV::BITAND
;;                                        ('SV::BITAND ('SV::BITXOR 1 x)
;;                                                    ('SV::BITXOR 1 y))
;;                                        ('SV::BITXOR 1 z)))
;;              (create-case-match-macro negated-fa-c-chain-1
;;                                       ('SV::BITAND ('SV::BITXOR 1 ('sv::bitand ('sv::bitor x y) z))
;;                                                    ('SV::BITXOR 1 ('sv::bitand x y)))))
;;   (cond ((negated-fa-c-chain-0-p svex)
;;          (negated-fa-c-chain-0-body
;;           svex
;;           (mv (hons-copy `(sv::bitxor 1 (sv::bitor (sv::bitor ,x ,y),z)))
;;               t)))
;;         ((negated-fa-c-chain-1-p svex)
;;          (negated-fa-c-chain-1-body
;;           svex
;;           (mv (hons-copy `(sv::bitxor 1 (sv::bitor (sv::bitand (sv::bitor ,x ,y) ,z)
;;                                                    (sv::bitand ,x ,y))))
;;               t)))
;;         (t
;;          (mv svex nil))))

;; (defines rw-adder-corner-cases
;;   :verify-guards nil
;;   (define rw-adder-corner-cases ((svex sv::svex-p)
;;                                  &key
;;                                  ((env) 'env)
;;                                  ((context rp-term-listp) 'context)
;;                                  ((config svl::svex-reduce-config-p) 'config))
;;     :measure (sv::Svex-count svex)
;;     :returns (res sv::svex-p :hyp (sv::svex-p svex))
;;     (sv::svex-case
;;      svex
;;      :var svex
;;      :quote svex
;;      :call (b* (((mv new-svex changed)
;;                  (rw-adder-corner-case svex))
;;                 ((when changed)
;;                  (rw-adder-corner-cases new-svex)))
;;             (sv::Svex-call svex.fn
;;                            (rw-adder-corner-cases-lst svex.args)))))
;;   (define rw-adder-corner-cases-lst ((lst sv::svexlist-p)
;;                                                 &key
;;                                                 ((env) 'env)
;;                                                 ((context rp-term-listp) 'context)
;;                                                 ((config svl::svex-reduce-config-p) 'config))
;;     :measure (sv::Svexlist-count lst)
;;     :Returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
;;     (if (atom lst)
;;         nil
;;       (hons (rw-adder-corner-cases (car lst))
;;             (rw-adder-corner-cases-lst (cdr lst)))))
;;   ///
;;   (verify-guards rw-adder-corner-cases-fn)
;;   (defret-mutual <fn>-is-correct
;;     (defret <fn>-correct
;;       (implies (and (sv::svex-p svex)
;;                     (rp::rp-term-listp context)
;;                     (rp::valid-sc env-term a)
;;                     (rp::eval-and-all context a)
;;                     (rp::falist-consistent-aux env env-term)
;;                     (svl::width-of-svex-extn-correct$-lst
;;                      (svl::svex-reduce-config->width-extns config))
;;                     (svl::integerp-of-svex-extn-correct$-lst
;;                      (svl::svex-reduce-config->integerp-extns config))
;;                     (warrants-for-adder-pattern-match))
;;                (equal (sv::Svex-eval$ res (rp-evlt env-term a))
;;                       (sv::Svex-eval$ svex (rp-evlt env-term a))))
;;       :fn rw-adder-corner-cases)
;;     (defret <fn>-correct
;;       (implies (and (sv::svexlist-p lst)
;;                     (rp::rp-term-listp context)
;;                     (rp::valid-sc env-term a)
;;                     (rp::eval-and-all context a)
;;                     (rp::falist-consistent-aux env env-term)
;;                     (svl::width-of-svex-extn-correct$-lst
;;                      (svl::svex-reduce-config->width-extns config))
;;                     (svl::integerp-of-svex-extn-correct$-lst
;;                      (svl::svex-reduce-config->integerp-extns config))
;;                     (warrants-for-adder-pattern-match))
;;                (equal (sv::Svexlist-eval$ res-lst (rp-evlt env-term a))
;;                       (sv::Svexlist-eval$ lst (rp-evlt env-term a))))
;;       :fn rw-adder-corner-cases-lst)
;;     :hints (("Goal"
;;              :do-not-induct t
;;              :expand ((rw-adder-corner-cases svex)
;;                       (rw-adder-corner-cases-lst lst)
;;                       (rw-adder-corner-cases-lst nil))
;;              :in-theory (e/d () ()))))
;;   (memoize 'rw-adder-corner-cases
;;            :condition '(eq (sv::svex-kind svex) :call))
;;   )

;; (define rw-adder-corner-cases-alist ((alist sv::svex-alist-p)
;;                                                 &key
;;                                                 ((env) 'env)
;;                                                 ((context rp-term-listp) 'context)
;;                                                 ((config svl::svex-reduce-config-p) 'config))
;;   :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
;;   (if (atom alist)
;;       nil
;;     (acons (caar alist)
;;            (rw-adder-corner-cases (cdar alist))
;;            (rw-adder-corner-cases-alist (cdr alist))))
;;   ///
;;   (defret <fn>-is-correct
;;     (implies (and (sv::svex-alist-p alist)
;;                   (rp-term-listp context)
;;                   (valid-sc env-term a)
;;                   (eval-and-all context a)
;;                   (falist-consistent-aux env env-term)
;;                   (svl::width-of-svex-extn-correct$-lst
;;                    (svl::svex-reduce-config->width-extns config))
;;                   (svl::integerp-of-svex-extn-correct$-lst
;;                    (svl::svex-reduce-config->integerp-extns config))
;;                   (force (warrants-for-adder-pattern-match)))
;;              (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
;;                     (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
;;     :hints (("goal"
;;              :do-not-induct t
;;              :induct (rw-adder-corner-cases-alist alist)
;;              :in-theory (e/d (sv::svex-alist-eval$)
;;                              ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod find-f/h-adders-state
  ((pp-id-cleaned :default nil)
   (reduce-bit-negations :default nil)
   (track-column? integerp :default -1)

   (only-quick-search :default nil)
   (skip-vector-adder :default nil)
   (skip-light-simplify :default nil)
   )
  :layout :fulltree
  ;;:hons t
  )

(with-output
  :off :all
  :gag-mode :goals
  :on (error summary)
  (define find-f/h-adders-in-svex-alist ((svex-alist sv::svex-alist-p)
                                         (limit natp)
                                         &key
                                         ((adder-type symbolp) 'adder-type)
                                         ((env) 'env)
                                         ((context rp-term-listp) 'context)
                                         ((config svl::svex-reduce-config-p) 'config)
                                         ((find-f/h-adders-state find-f/h-adders-state-p)
                                          'find-f/h-adders-state))

    :prepwork
    ((defconst *find-f/h-adders-in-svex-alist-limit*
       50)
     (local
      (in-theory (disable fast-alist-clean))))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
    :measure (nfix limit)
    (b* (;; gather some basics
         ((find-f/h-adders-state tstate) find-f/h-adders-state)
         (adder-str (If (eq adder-type 'ha) "half-adder" "full-adder"))
         (pass-num (+ 1 (- limit) *find-f/h-adders-in-svex-alist-limit*))
         (track-column? (posp tstate.track-column?))
         (find-f/h-adders-state (change-find-f/h-adders-state tstate
                                                              :track-column? (1- tstate.track-column?)))

         ((when (zp limit))
          (progn$
           (cw "----
WARNING: Iteration limit of ~p0 is reached. Will not parse again for ~s1 patterns. Either there is an unexpected infinite loop, or the iteration limit may need to be increased.
----~%"
               *find-f/h-adders-in-svex-alist-limit* adder-str)
           svex-alist))
         (first-pass? (= pass-num 1))
         (- (and first-pass?
                 (cw "--- Searching for ~s0 patterns now. ~%" adder-str)))
         (- (cw "-- Pass #~p0:~%" pass-num))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; maybe clean up a bit before moving on. Simplification might have messed up with argument orders.
         (svex-alist (if (or* (> pass-num 1) (eq adder-str 'ha))
                         (b* ((svex-alist (global-zero-fa-c-chain-extra-arg-alist svex-alist))
                              (svex-alist (fix-order-of-fa/ha-chain-args-alist svex-alist)))
                           svex-alist)
                       svex-alist))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Perform quick search.
         ;;(-    (clear-memoize-table     'adder-pattern-match))    ;;    maybe
         ;;unnecessary. taking it out becuase large booth encodings will have a
         ;;lot of rep
         ((mv pattern-alist &)
          (gather-adder-patterns-in-svex-alist svex-alist))
         (new-svex-alist (replace-adder-patterns-in-svex-alist svex-alist))
         (pattern-alist (fast-alist-clean pattern-alist))
         (replaced-pattern-cnt (count-newly-found-adders-in-pattern-alist pattern-alist))
         (- (cw "- Quick search found and replaced ~p0 ~s1 patterns. ~%" replaced-pattern-cnt adder-str))

         (- (and (equal replaced-pattern-cnt 0)
                 (not (equal svex-alist new-svex-alist))
                 (cw "-> Even though statistics showed 0 new pattern match, some of the other missed patterns have actually been replaced. ~%")))

         ((when tstate.only-quick-search)
          (progn$ (fast-alist-free pattern-alist)
                  (if (equal svex-alist new-svex-alist)
                      new-svex-alist
                    (find-f/h-adders-in-svex-alist new-svex-alist (1- limit)))))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Only for the first pass of FA, also do an vector adder search.
         ;; This is not necessary but can  help with performance by reducing pass
         ;; count.
         ((mv new-svex-alist2 find-f/h-adders-state)
          (b* (((when tstate.skip-vector-adder)
                (mv new-svex-alist find-f/h-adders-state))
               ((Unless (and first-pass? (eq adder-type 'fa)))
                (mv new-svex-alist find-f/h-adders-state))

               (- (cw "- Looking and rewriting for vector adder patterns... ~%"))
               (new-svex-alist2 (ppx-simplify-alist new-svex-alist))
               (vector-adder-changed (not (equal new-svex-alist2 new-svex-alist)))
               (- (if vector-adder-changed
                      (cw "-> Success! Rewriting for vector adder made some changes. Let's make another pass. ~%")
                    (cw "-> No change from vector adder simplification. ~%")))
               (find-f/h-adders-state (change-find-f/h-adders-state tstate
                                                                    :skip-vector-adder t)))
            (mv new-svex-alist2 find-f/h-adders-state)))
         ((unless (equal svex-alist new-svex-alist2))
          (progn$ (fast-alist-free pattern-alist)
                  (find-f/h-adders-in-svex-alist new-svex-alist2 (1- limit))))

         ;; TODO: to prevent  consing, can do some preliminary check  here for if
         ;; there exists xor chains OR maybe fa-* functions under or gates.

         ;; TODO:  HERE I  can look  for bitxors  with at  least 3  elements to
         ;; decide if any fa-s/ha-s might be mising before consing below..

         (- (cw "- Now will look  more carefully if we ~
 missed any ~s0-s pattern that  has a found counterpart ~s0-c pattern...~%"
                adder-str))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Carefully looking for fa/ha-s patterns:

         (exploded-args-and-args-alist (process-fa/ha-c-chain-pattern-args pattern-alist nil))
         ((mv new-svex-alist &)
          (find-s-from-found-c-in-svex-alist-aux svex-alist exploded-args-and-args-alist))
         (- (fast-alist-free exploded-args-and-args-alist))
         ((Unless (equal new-svex-alist svex-alist))
          (progn$ (cw "-> Success! Some missed ~s0-s patterns are found and their shape is ~
       updated. This will reveal more ~s0 patterns during quick search. So will ~
       now do another pass. There might be an overlap in the statistics below. ~%"
                      adder-str)
                  (fast-alist-free pattern-alist)
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))
         (- (cw "-> Careful search did not reveal any new ~s0-s. ~%" adder-str))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Carefully looking for ha-c, ha+1-c patterns:
         (careful-look-for-ha-c (equal adder-type 'ha))
         (- (fast-alist-free pattern-alist))
         (new-svex-alist
          (and careful-look-for-ha-c
               (b* ((- (cw "- Now will look  more carefully if we missed any ha-c/ha+1-c pattern that  has a found counterpart ha-s/ha+1-s patterns...~%"
                           adder-str))
                    (exploded-args-and-args-alist (process-fa/ha-c-chain-pattern-args
                                                   pattern-alist
                                                   nil
                                                   :adder-type 'ha-c))
                    ((mv svex-alist &)
                     (find-s-from-found-c-in-svex-alist-aux svex-alist exploded-args-and-args-alist
                                                            :adder-type 'ha-c))
                    (- (fast-alist-free exploded-args-and-args-alist))

                    (exploded-args-and-args-alist (process-fa/ha-c-chain-pattern-args
                                                   pattern-alist
                                                   nil
                                                   :adder-type 'ha+1-c))
                    ((mv svex-alist &)
                     (find-s-from-found-c-in-svex-alist-aux svex-alist exploded-args-and-args-alist
                                                            :adder-type 'ha+1-c))
                    (- (fast-alist-free exploded-args-and-args-alist)))
                 svex-alist)))
         ((Unless (or (not careful-look-for-ha-c)
                      (hons-equal new-svex-alist svex-alist)))
          (progn$ (cw "-> Success! Some missed ~s0-c patterns are found and their shape is ~
       updated. This will reveal more ~s0 patterns during quick search. So will ~
       now do another pass. There might be an overlap in the statistics below. ~%"
                      adder-str)
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))
         (- (and careful-look-for-ha-c
                 (cw "-> Careful search did not reveal any new ~s0-c. ~%" adder-str)))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Vector adder simplification
         ((mv svex-alist find-f/h-adders-state exit?)
          (b* (((when tstate.skip-vector-adder)
                (mv svex-alist find-f/h-adders-state nil))
               (- (cw "- Looking and rewriting for vector adder patterns... ~%"))
               (new-svex-alist (ppx-simplify-alist svex-alist))
               (vector-adder-changed (not (equal new-svex-alist svex-alist)))
               (- (if vector-adder-changed
                      (cw "-> Success! Rewriting for vector adder made some changes. Let's make another pass. ~%")
                    (cw "-> No change from vector adder simplification. ~%")))
               (find-f/h-adders-state (change-find-f/h-adders-state tstate
                                                                    :skip-vector-adder t)))
            (mv new-svex-alist find-f/h-adders-state vector-adder-changed)))
         ((when exit?)
          (find-f/h-adders-in-svex-alist svex-alist (1- limit)))

         ((when (and*-exec (equal adder-type 'ha)
                           (not tstate.skip-light-simplify)))
          (b* ((- (cw "- Let's run a light-weight bitand/xor/or simplification.~%"))
               (new-svex-alist (svl::light-svex-alist-simplify-bitand/or/xor svex-alist))
               ;; so that light simplify is run only once..
               (find-f/h-adders-state (change-find-f/h-adders-state tstate
                                                                    :skip-light-simplify t))
               ((when (not (equal new-svex-alist svex-alist)))
                (progn$ (cw "-> Light-weight simplification made some changes. Let's make another pass. ~%")
                        (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))
               (- (cw "-> No change from light-weight simplification. ~%"))

               ((when track-column?)
                (b* ((- (cw "~%-- Going to try again with less restrictions... ~%"))
                     (find-f/h-adders-state (change-find-f/h-adders-state tstate
                                                                          :track-column? 0)))
                  (find-f/h-adders-in-svex-alist svex-alist (1- limit)))))
            svex-alist))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Do not move forward unless fa
         ((unless (equal adder-type 'fa))
          (b* (((Unless track-column?) svex-alist)
               (- (cw "- Going to try again with less restrictions... ~%"))
               (find-f/h-adders-state (change-find-f/h-adders-state tstate
                                                                    :track-column? 0)))
            (find-f/h-adders-in-svex-alist svex-alist (1- limit))))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Local simplification to reveal fa-c patterns
         (- (cw "- Let's see if local bitxor/or/and simplification can reveal more fa-c patterns... ~%"))
         (config (svl::change-svex-reduce-config ;; make sure config is set correctly.
                  config :skip-bitor/and/xor-repeated nil))

         ;;(- (design_res-broken svex-alist "before simplify-to-find-fa-c-patterns-alist"))

         (new-svex-alist (simplify-to-find-fa-c-patterns-alist svex-alist :strength 0))

         ;;(- (design_res-broken new-svex-alist "after simplify-to-find-fa-c-patterns-alist"))

         ((Unless (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "-> Success! some fa-c patterns are revealed. Let's make another pass.~%")
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))

         (- (and
             (aggressive-find-adders-in-svex)
             (cw "- Nothing. Let's increase local simplification strength from 0 to 1 and try again. ~%")))
         (new-svex-alist (if (aggressive-find-adders-in-svex)
                             (simplify-to-find-fa-c-patterns-alist svex-alist :strength 1)
                           svex-alist))
         ((Unless (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "-> Success! some fa-c patterns are revealed. Let's make another pass.~%")
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))

         (- (and
             (aggressive-find-adders-in-svex)
             (cw "- Nothing. Let's increase local simplification strength from 1 to 4 and try again. ~%")))
         (new-svex-alist (if (aggressive-find-adders-in-svex)
                             (simplify-to-find-fa-c-patterns-alist svex-alist :strength 4)
                           svex-alist))
         ((Unless (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "-> Success! some fa-c patterns are revealed. Let's make another pass.~%")
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))

         (- (cw "-> Nothing found from local simplifications. ~%"))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Push in negations
         (- (and tstate.reduce-bit-negations
                 (cw "- Will try to see if we can shrink the svexes by reducing negations~%")))
         (new-svex-alist (if tstate.reduce-bit-negations
                             (svl::svex-alist-reduce-bit-negations svex-alist)
                           svex-alist))
         ((Unless (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "-> Some negation chains are reduced. ~%")
                  (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))
         (- (and tstate.reduce-bit-negations
                 (cw "-> No change from negation compresions~%")))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; ;; RW  corner cases
         ;; (- (cw "- Will try to see if we can rewrite some known patterns~%"))
         ;; (new-svex-alist (rw-adder-corner-cases-alist svex-alist))
         ;; ((Unless (hons-equal new-svex-alist svex-alist))
         ;;  (progn$ (cw "-> Some known patterns are cleaned. ~%")
         ;;          (find-f/h-adders-in-svex-alist new-svex-alist (1- limit))))
         ;; (- (cw "-> No change from known pattern rw. ~%"))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Clean out IDs that possible came from wrapping PP with IDs stage.
         ((unless (or (not (aggressive-find-adders-in-svex))
                      tstate.pp-id-cleaned))
          (b*  ((find-f/h-adders-state (change-find-f/h-adders-state find-f/h-adders-state
                                                                     :pp-id-cleaned t))
                (- (cw "- Let's run a light-weight bitand/xor/or simplification.~%"))
                (svex-alist (svl::light-svex-alist-simplify-bitand/or/xor svex-alist))
                (- (cw "- Let's extract from IDs and make another pass. ~%"))
                (svex-alist (extract-svex-from-id-alist svex-alist))
                )
            (find-f/h-adders-in-svex-alist svex-alist (1- limit))))

         ;; ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
         ;; Global simplification unless disabled.
         ((unless (find-adders-global-bitand/or/xor-simplification-enabled))
          (progn$ (cw "- Skipping global simplification because it is disabled at this stage with (enable-find-adders-global-bitand/or/xor-simplification nil). Ending the search.~%")
                  svex-alist))
         (- (cw "- Let's try global bitxor/and/or simplification. ~%"))
         (new-svex-alist (svl::light-svex-alist-simplify-bitand/or/xor svex-alist))
         ((when (hons-equal new-svex-alist svex-alist))
          (progn$ (cw "-> Global bitxor/and/or simplification did not change anything. Ending the search.~%")
                  svex-alist))
         (- (cw "-> Global bitxor/and/or simplification made some changes. Let's make another pass. ~%"))

         ;; find-s-from-found-c-in-svex-alist-aux  may  cause  new  simplify-able
         ;; patterns to  occur. but not sure  if something less general  would be
         ;; useful here. TODO: investigate.
         #|(new-svex-alist (svl::svex-alist-simplify-bitand/or/xor  new-svex-alist
         :config config))|#

         )
      (find-f/h-adders-in-svex-alist new-svex-alist (1- limit)))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-alist-p svex-alist)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (force (warrants-for-adder-pattern-match))

                    (or (equal adder-type 'ha)
                        (equal adder-type 'fa))
                    )
               (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                      (sv::svex-alist-eval$ svex-alist (rp-evlt env-term a))))
      :hints (("Goal"
               ;;:do-not-induct t
               :expand (;;(find-f/h-adders-in-svex-alist svex-alist limit)
                        (exploded-args-and-args-alist-inv nil (rp-evlt env-term a)))
               :in-theory (e/d ()
                               (valid-sc
                                valid-sc-subterms
                                rp-trans
                                rp-term-listp
                                rp-trans-lst
                                eval-and-all
                                falist-consistent-aux
                                ex-from-rp)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; (defines remove-ha-under-gates
;;   :verify-guards nil
;;   (define remove-ha-under-gates ((svex sv::svex-p)
;;                                  (under-gate booleanp))
;;     :returns (res-svex sv::svex-p :hyp (sv::svex-p svex))
;;     :measure (sv::Svex-count svex)
;;     (sv::svex-case
;;      svex
;;      :var svex
;;      :quote svex
;;      :call (b* ((under-gate-for-args (or* (eq svex.fn 'sv::bitor)
;;                                           (eq svex.fn 'sv::bitand)
;;                                           (and* under-gate
;;                                                 (eq svex.fn 'sv::bitxor))))
;;                 (args (remove-ha-under-gates-lst svex.args under-gate-for-args)))
;;              (cond ((not under-gate)
;;                     (sv::svex-call svex.fn args))
;;                    ((and* (eq svex.fn 'ha-s-chain)
;;                           (svl::equal-len svex.args 2))
;;                     (sv::svex-call 'sv::bitxor args))
;;                    ((and* (eq svex.fn 'ha-c-chain)
;;                           (svl::equal-len svex.args 2))
;;                     (sv::svex-call 'sv::bitand args))
;;                    ((and* (eq svex.fn 'ha+1-c-chain)
;;                           (svl::equal-len svex.args 2))
;;                     (sv::svex-call 'sv::bitor args))
;;                    ((and* (eq svex.fn 'ha+1-s-chain)
;;                           (svl::equal-len svex.args 3)
;;                           (integerp (car svex.args)))
;;                     (if (equal (car svex.args) 0)
;;                         (sv::Svex-call 'sv::Bitnot
;;                                        (hons-list (sv::svex-call 'sv::bitxor (cdr args))))
;;                       (sv::Svex-call 'sv::bitxor
;;                                      (hons-list 1
;;                                                 (sv::svex-call 'sv::bitxor (cdr args))))))
;;                    (t (sv::svex-call svex.fn args))))))

;;   (define remove-ha-under-gates-lst ((lst sv::svexlist-p)
;;                                      (under-gate booleanp))
;;     :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
;;     :measure (sv::Svexlist-count lst)
;;     (if (atom lst)
;;         nil
;;       (hons (remove-ha-under-gates (car lst) under-gate)
;;             (remove-ha-under-gates-lst (cdr lst) under-gate))))
;;   ///
;;   (verify-guards remove-ha-under-gates)

;;   (memoize 'remove-ha-under-gates
;;            :condition '(eq (sv::svex-kind svex) :call))

;;   (defret-mutual <fn>-is-correct
;;     (defret <fn>-is-correct
;;       (implies (and (sv::svex-p svex)
;;                     (warrants-for-adder-pattern-match))
;;                (equal (sv::svex-eval$ res-svex env)
;;                       (sv::svex-eval$ svex env)))
;;       :fn remove-ha-under-gates)
;;     (defret <fn>-is-correct
;;       (implies (and (warrants-for-adder-pattern-match)
;;                     (sv::svexlist-p lst))
;;                (equal (sv::svexlist-eval$ res-lst env)
;;                       (sv::svexlist-eval$ lst env)))
;;       :fn remove-ha-under-gates-lst)
;;     :hints (("Goal"
;;              :do-not-induct t
;;              :expand ((REMOVE-HA-UNDER-GATES SVEX UNDER-GATE)
;;                       (REMOVE-HA-UNDER-GATES SVEX NIL)
;;                       (REMOVE-HA-UNDER-GATES-LST LST UNDER-GATE)
;;                       (:free (args)
;;                              (sv::svex-apply$ 'HA+1-S-CHAIN args))
;;                       (:free (args)
;;                              (sv::svex-apply$ 'HA+1-C-CHAIN args))
;;                       (:free (args)
;;                              (sv::svex-apply$ 'ha-s-chain args))
;;                       (:free (args)
;;                              (sv::svex-apply$ 'ha-c-chain args))
;;                       (:free (args)
;;                              (sv::svex-apply$ 'fa-s-chain args)))
;;              :in-theory (e/d (ha-s-chain
;;                               HA+1-C-CHAIN
;;                               SV::SVEXLIST-EVAL$
;;                               SV::4VECLIST-NTH-SAFE
;;                               HA+1-S-CHAIN
;;                               SV::SVEX-APPLY
;;                               fa-s-chain
;;                               ha-c-chain
;;                               sv::svex-call->fn
;;                               sv::svex-call->args)
;;                              ()))))

;;   (define remove-ha-under-gates-alist ((alist sv::svex-alist-p))
;;     :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
;;     (if (atom alist)
;;         nil
;;       (acons (caar alist)
;;              (remove-ha-under-gates (cdar alist) nil)
;;              (remove-ha-under-gates-alist (cdr alist))))
;;     ///
;;     (defret <fn>-is-correct
;;       (implies (and (sv::svex-alist-p alist)
;;                     (warrants-for-adder-pattern-match))
;;                (equal (sv::svex-alist-eval$ res env)
;;                       (sv::svex-alist-eval$ alist env)))
;;       :hints (("goal"
;;                :do-not-induct t
;;                :induct (remove-ha-under-gates-alist alist)
;;                :in-theory (e/d (sv::svex-alist-eval$)
;;                                (remove-ha-under-gates)))))))

;; (defines remove-unpaired-ha
;;   :verify-guards nil
;;   :prepwork ((local (in-theory (disable remove-duplicates-equal
;;                                         member-equal))))
;;   (define remove-unpaired-ha ((svex sv::svex-p)
;;                               (pattern-alist pattern-alist-p))
;;     :returns (res-svex sv::svex-p :hyp (sv::svex-p svex))
;;     :measure (sv::Svex-count svex)
;;     (sv::svex-case
;;      svex
;;      :var svex
;;      :quote svex
;;      :call (b* ((to-remove (b* ((pattern-fn-call-list (adder-pattern-match svex 'ha-self))
;;                                 ((unless (consp pattern-fn-call-list))
;;                                  nil)
;;                                 ((pattern-fn-call p) (car pattern-fn-call-list))
;;                                 (entry (Hons-get p.args pattern-alist))
;;                                 ((when (and entry
;;                                             (= (len (remove-duplicates-equal (cdr entry))) 1)))
;;                                  t))
;;                              nil))
;;                 (args (remove-unpaired-ha-lst svex.args pattern-alist)))

;;              (cond ((not to-remove)
;;                     (sv::svex-call svex.fn args))
;;                    ((and* (eq svex.fn 'ha-s-chain)
;;                           (svl::equal-len svex.args 2))
;;                     (sv::svex-call 'sv::bitxor args))
;;                    ((and* (eq svex.fn 'ha-c-chain)
;;                           (svl::equal-len svex.args 2))
;;                     (sv::svex-call 'sv::bitand args))
;;                    ((and* (eq svex.fn 'ha+1-c-chain)
;;                           (svl::equal-len svex.args 2))
;;                     (sv::svex-call 'sv::bitor args))
;;                    ((and* (eq svex.fn 'ha+1-s-chain)
;;                           (svl::equal-len svex.args 3)
;;                           (integerp (car svex.args)))
;;                     (if (equal (car svex.args) 0)
;;                         (sv::Svex-call 'sv::Bitnot
;;                                        (hons-list (sv::svex-call 'sv::bitxor (cdr args))))
;;                       (sv::Svex-call 'sv::bitxor
;;                                      (hons-list 1
;;                                                 (sv::svex-call 'sv::bitxor (cdr args))))))
;;                    (t (sv::svex-call svex.fn args))))))

;;   (define remove-unpaired-ha-lst ((lst sv::svexlist-p)
;;                                   (pattern-alist pattern-alist-p))
;;     :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
;;     :measure (sv::Svexlist-count lst)
;;     (if (atom lst)
;;         nil
;;       (hons (remove-unpaired-ha (car lst) pattern-alist)
;;             (remove-unpaired-ha-lst (cdr lst) pattern-alist))))
;;   ///
;;   (verify-guards remove-unpaired-ha)

;;   (memoize 'remove-unpaired-ha
;;            :condition '(eq (sv::svex-kind svex) :call))

;;   (defret-mutual <fn>-is-correct
;;     (defret <fn>-is-correct
;;       (implies (and (sv::svex-p svex)
;;                     (warrants-for-adder-pattern-match))
;;                (equal (sv::svex-eval$ res-svex env)
;;                       (sv::svex-eval$ svex env)))
;;       :fn remove-unpaired-ha)
;;     (defret <fn>-is-correct
;;       (implies (and (warrants-for-adder-pattern-match)
;;                     (sv::svexlist-p lst))
;;                (equal (sv::svexlist-eval$ res-lst env)
;;                       (sv::svexlist-eval$ lst env)))
;;       :fn remove-unpaired-ha-lst)
;;     :hints (("Goal"
;;              :do-not-induct t
;;              :expand ((remove-unpaired-ha-lst nil pattern-alist)
;;                       (remove-unpaired-ha-lst lst pattern-alist)
;;                       (remove-unpaired-ha svex pattern-alist)
;;                       (nth 1 (cdr svex))
;;                       (remove-unpaired-ha-lst (cdr svex) pattern-alist)
;;                       (:free (args)
;;                              (sv::svex-apply$ 'HA+1-S-CHAIN args))
;;                       (:free (args)
;;                              (sv::svex-apply$ 'HA+1-C-CHAIN args))
;;                       (:free (args)
;;                              (sv::svex-apply$ 'ha-s-chain args))
;;                       (:free (args)
;;                              (sv::svex-apply$ 'ha-c-chain args))
;;                       (:free (args)
;;                              (sv::svex-apply$ 'fa-s-chain args)))
;;              :in-theory (e/d (ha-s-chain
;;                               HA+1-C-CHAIN
;;                               SV::SVEXLIST-EVAL$
;;                               SV::4VECLIST-NTH-SAFE
;;                               HA+1-S-CHAIN
;;                               SV::SVEX-APPLY
;;                               fa-s-chain
;;                               ha-c-chain
;;                               sv::svex-call->fn
;;                               sv::svex-call->args)
;;                              (len)))))

;;   (define remove-unpaired-ha-alist ((alist sv::svex-alist-p)
;;                                     (pattern-alist pattern-alist-p))
;;     :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
;;     (if (atom alist)
;;         nil
;;       (acons (caar alist)
;;              (remove-unpaired-ha (cdar alist) pattern-alist)
;;              (remove-unpaired-ha-alist (cdr alist) pattern-alist)))
;;     ///
;;     (defret <fn>-is-correct
;;       (implies (and (sv::svex-alist-p alist)
;;                     (warrants-for-adder-pattern-match))
;;                (equal (sv::svex-alist-eval$ res env)
;;                       (sv::svex-alist-eval$ alist env)))
;;       :hints (("goal"
;;                :do-not-induct t
;;                :induct (remove-unpaired-ha-alist alist pattern-alist)
;;                :in-theory (e/d (sv::svex-alist-eval$)
;;                                (remove-unpaired-ha)))))))

;; (define remove-ha-pairs-under-gates-alist ((svex-alist sv::svex-alist-p))
;;   :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
;;   (b* ((- (cw "--- Now removing misidentified half-adders.~%"))
;;        (svex-alist (remove-ha-under-gates-alist svex-alist))
;;        ((mv pattern-alist &)
;;         (gather-adder-patterns-in-svex-alist svex-alist :adder-type 'ha-self))
;;        (svex-alist (remove-unpaired-ha-alist svex-alist pattern-alist))

;;        (- (clear-memoize-table 'remove-ha-under-gates))
;;        (- (clear-memoize-table 'remove-unpaired-ha))
;;        )
;;     svex-alist)
;;   ///
;;   (defret <fn>-is-correct
;;     (implies (and (sv::svex-alist-p svex-alist)
;;                   (warrants-for-adder-pattern-match))
;;              (equal (sv::svex-alist-eval$ res env)
;;                     (sv::svex-alist-eval$ svex-alist env)))
;;     :hints (("goal"
;;              :do-not-induct t
;;              :in-theory (e/d ()
;;                              ())))))

#|(defines svex-pattern-context

(define svex-pattern-context ((svex sv::svex-p)
pattern
(depth natp))
:verify-guards nil
:measure (sv::Svex-count svex)
:Returns (x natp :rule-classes (:rewrite :type-prescription))
(if (equal svex pattern)
(progn$ (cw "here")
(lnfix depth))
(sv::Svex-case
svex
:quote 0
:var 0
:call (b* ((args (svexlist-pattern-context svex.args pattern depth))
(- (and (equal args 1)
(cwe "svex found in context: ~p0 ~%"
(acl2::subst '*** pattern svex)))))
(nfix (1- args))))))
(define svexlist-pattern-context ((lst sv::svexlist-p)
pattern
(depth natp))
:measure (sv::Svexlist-count lst)
:Returns (x natp :rule-classes (:rewrite :type-prescription))
(if (atom lst)
0
(max (svex-pattern-context (car lst) pattern depth)
(svexlist-pattern-context (cdr lst) pattern depth))))
///
(verify-guards svex-pattern-context)
(memoize 'svex-pattern-context)

(define svexalist-pattern-context ((x sv::Svex-alist-p)
pattern
(depth natp))
(if (atom x)
0
(progn$ (svex-pattern-context (cdar x) pattern depth)
(svexalist-pattern-context (cdr x) pattern depth)))))|#

(defines collect-ha-args-under-gates
  ;; collects to a fast-alist. Keys are args in any order.
  :verify-guards nil
  (define collect-ha-args-under-gates ((svex sv::svex-p)
                                       (underadder booleanp)
                                       (undergate booleanp)
                                       (collected alistp)
                                       (parsed-svexes alistp))
    :measure (sv::Svex-count svex)
    :Returns (mv (res-collected alistp :hyp (alistp collected))
                 (res-parsed-svexes alistp :hyp (alistp parsed-svexes)))
    (sv::svex-case
     svex
     :quote (mv collected parsed-svexes)
     :var (mv collected parsed-svexes)
     :call (b* (;; what if parsed under different context? This may need to be improved...
                (parse-key (list* svex underadder undergate))
                (parsed? (hons-get parse-key parsed-svexes))
                ((when parsed?) (mv collected parsed-svexes))
                (adder-p (or (equal svex.fn 'fa-c-chain)
                             (equal svex.fn 'fa-s-chain)
                             (equal svex.fn 'ha-c-chain)
                             (equal svex.fn 'ha-s-chain)
                             (equal svex.fn 'ha+1-c-chain)
                             (equal svex.fn 'ha+1-s-chain)))

                (ha-undergate? (and ;;underadder
                                undergate
                                (or (equal svex.fn 'ha-c-chain)
                                    (equal svex.fn 'ha-s-chain)
                                    (equal svex.fn 'ha+1-c-chain)
                                    (equal svex.fn 'ha+1-s-chain))))

                (collected (if ha-undergate?
                               ;; arguments should be ordered beforehand so not
                               ;; putting the args only one way.
                               (hons-acons (if (equal svex.fn 'ha+1-s-chain) (cdr svex.args) svex.args)
                                           nil
                                           collected)
                             collected))

                (parsed-svexes (hons-acons parse-key nil parsed-svexes)))
             (collect-ha-args-under-gates-list svex.args
                                               (or adder-p
                                                   (and
                                                    ;; carry on underadder only
                                                    ;; through these gates.
                                                    underadder
                                                    #|(member-equal
                                                    svex.fn
                                                    (list 'sv::bitand
                                                    'sv::unfloat
                                                    'sv::id 'sv::?* 'sv::?
                                                    'sv::bitor
                                                    'sv::uor
                                                    'SV::uand
                                                    'sv::bitxor))|#))
                                               (or (equal svex.fn 'sv::bitand)
                                                   (equal svex.fn 'sv::bitor)
                                                   (equal svex.fn 'sv::uor)
                                                   (equal svex.fn 'sv::uand)
                                                   (and (or (equal svex.fn 'sv::unfloat)
                                                            (equal svex.fn 'sv::id))
                                                        undergate)
                                                   (and underadder
                                                        (equal svex.fn 'sv::bitxor)
                                                        (or undergate
                                                            ;; If it is undergate move it through
                                                            ;; when bitxor is used for negation.
                                                            (not (member-equal 1 svex.args)))))
                                               collected
                                               parsed-svexes))))
  (define collect-ha-args-under-gates-list ((svexlist sv::svexlist-p)
                                            (underadder booleanp)
                                            (undergate booleanp)
                                            (collected alistp)
                                            (parsed-svexes alistp))
    :measure (sv::svexlist-count svexlist)
    :Returns (mv (res-collected alistp :hyp (alistp collected))
                 (res-parsed-svexes alistp :hyp (alistp parsed-svexes)))
    (if (atom svexlist)
        (mv collected parsed-svexes)
      (b* (((mv collected parsed-svexes)
            (collect-ha-args-under-gates (car svexlist)
                                         underadder undergate
                                         collected parsed-svexes))
           ((mv collected parsed-svexes)
            (collect-ha-args-under-gates-list (cdr svexlist)
                                              underadder undergate
                                              collected parsed-svexes)))
        (mv collected parsed-svexes))))
  ///
  (verify-guards collect-ha-args-under-gates)

  (define collect-ha-args-under-gates-alist ((x sv::svex-alist-p)
                                             &key
                                             ((collected alistp) 'nil)
                                             ((parsed-svexes alistp) 'nil))
    :Returns (mv (res-collected alistp :hyp (alistp collected))
                 (res-parsed-svexes alistp :hyp (alistp parsed-svexes)))
    (if (atom x)
        (mv (fast-alist-clean collected)
            (fast-alist-free parsed-svexes))
      (b* (((mv collected parsed-svexes)
            (collect-ha-args-under-gates (cdar x)
                                         nil nil
                                         collected parsed-svexes))
           ((mv collected parsed-svexes)
            (collect-ha-args-under-gates-alist (cdr x)
                                               :collected collected
                                               :parsed-svexes parsed-svexes)))
        (mv collected parsed-svexes)))))

(define shuffle-gates-after-removing-ha-under-gates ((svex.fn sv::fnsym-p)
                                                     (svex.args sv::svexlist-p)
                                                     (orig-svex.args sv::svexlist-p))

  ;; After an  half-adder is removed,  this function makes a  slight shuffle so  that we
  ;; don't match the exact same adder right away and possibly let other variations to be matched

  :prepwork ((local
              (in-theory (disable subsetp-equal
                                  member-equal
                                  symbol-listp
                                  default-car))))

  :returns (res-svex sv::svex-p :hyp (and (sv::fnsym-p svex.fn)
                                          (sv::svexlist-p svex.args))
                     :hints (("Goal"
                              :expand ((sv::svex-kind (car svex.args))
                                       (sv::svex-kind (cadr svex.args)))
                              :in-theory (e/d () (sv::svex-kind$inline)))))
  :guard-debug t
  :guard-hints (("Goal"
                 :expand ((sv::svex-kind (car svex.args))
                          (sv::svex-kind (cadr svex.args)))
                 :in-theory (e/d (and*
                                  SVL::EQUAL-LEN)
                                 (sv::svex-kind$inline))))

  (b* (((unless (or (equal svex.fn 'sv::bitxor)
                    (equal svex.fn 'sv::bitand)))
        (sv::Svex-call svex.fn svex.args))
       (no-orig (not orig-svex.args))
       ((unless (and*-exec (svl::equal-len svex.args 2)
                           (or no-orig
                               (svl::equal-len orig-svex.args 2))))
        (sv::Svex-call svex.fn svex.args))
       ((mv x1 x2) (mv (first svex.args) (second svex.args)))

       ((mv o1 o2) (mv (or no-orig (first orig-svex.args))
                       (or no-orig (second orig-svex.args))))

       ((list x1.fn x1.args) (and*-exec (equal (sv::svex-kind x1) :call)
                                        (list (sv::svex-call->fn x1)
                                              (sv::svex-call->args x1))))
       ((list x2.fn x2.args) (and*-exec (equal (sv::svex-kind x2) :call)
                                        (list (sv::svex-call->fn x2)
                                              (sv::svex-call->args x2))))
       (o1.fn (and*-exec orig-svex.args
                         (equal (sv::svex-kind o1) :call)
                         (sv::svex-call->fn o1)))
       (o2.fn (and*-exec orig-svex.args
                         (equal (sv::svex-kind o2) :call)
                         (sv::svex-call->fn o2)))

       ((when (or no-orig
                  (and*-exec (equal x1.fn o1.fn)
                             (equal x2.fn o2.fn))))
        (sv::Svex-call svex.fn svex.args)))
    (cond ((and*-exec (or no-orig (not (equal x1.fn o1.fn)))
                      (equal x1.fn svex.fn)
                      (svl::equal-len x1.args 2))
           (sv::Svex-call svex.fn
                          (hons-list (first x1.args)
                                     (sv::Svex-call svex.fn
                                                    (hons-list (second x1.args)
                                                               x2)))))
          ((and*-exec (or no-orig (not (equal x2.fn o2.fn)))
                      (equal x2.fn svex.fn)
                      (svl::equal-len x2.args 2))
           (sv::Svex-call svex.fn
                          (hons-list (sv::Svex-call svex.fn
                                                    (hons-list (second x2.args)
                                                               x1))
                                     (first x2.args))))
          (t  (sv::Svex-call svex.fn svex.args))))

  ///

  (defret <fn>-is-correct
    (implies t
             (equal (sv::Svex-eval$ res-svex env)
                    (sv::Svex-eval$ (sv::Svex-call svex.fn svex.args) env)))
    :fn shuffle-gates-after-removing-ha-under-gates
    :hints (("Goal"
             :expand ((sv::svex-kind (car svex.args))
                      (sv::svex-kind (cadr svex.args)))
             :in-theory (e/d (sv::svex-apply)
                             (sv::svex-kind$inline))))))

;; (shuffle-gates-after-removing-ha-under-gates 'sv::bitand
;;                                              (list 'z '(sv::bitand x y))
;;                                              (list 'z '(ha-c-chain x y)))

(defines remove-ha-under-gates
  :verify-guards nil
  :hints (("Goal"
           :in-theory (e/d (sv::SVEX-COUNT
                            SV::SVEX-CALL->FN
                            SV::SVEX-CALL->args)
                           ())))

  (define remove-ha-under-gates ((svex sv::Svex-p)
                                 &key
                                 ((wrap-with-id booleanp) 'wrap-with-id)
                                 ((collected alistp) 'collected))
    :measure (sv::svex-count svex)
    :Returns (res-svex sv::svex-p :hyp (sv::svex-p svex))

    (sv::svex-case
     svex
     :var svex
     :quote svex
     :call
     (b* ((adder-p (or (equal svex.fn 'ha-c-chain)
                       (equal svex.fn 'ha-s-chain)
                       (equal svex.fn 'ha+1-c-chain)
                       (equal svex.fn 'ha+1-s-chain)))
          (to-remove (and adder-p
                          (if (equal svex.fn 'ha+1-s-chain)
                              (hons-get (cdr svex.args) collected)
                            (hons-get svex.args collected))))
          ((unless to-remove)

           (shuffle-gates-after-removing-ha-under-gates
            svex.fn
            (remove-ha-under-gates-lst svex.args)
            svex.args)

           #|(sv::Svex-call svex.fn
           (remove-ha-under-gates-lst svex.args))|#)
          (res
           (cond
            ((ha-c-chain-self-pattern-p svex)
             (ha-c-chain-self-pattern-body
              svex
              (shuffle-gates-after-removing-ha-under-gates
               'sv::bitand
               (hons-list (remove-ha-under-gates x)
                          (remove-ha-under-gates y))
               nil)))
            ((ha-s-chain-self-pattern-p svex)
             (ha-s-chain-self-pattern-body
              svex
              (shuffle-gates-after-removing-ha-under-gates
               'sv::bitxor
               (hons-list (remove-ha-under-gates x)
                          (remove-ha-under-gates y))
               nil)))
            ((ha+1-s-chain-self-pattern-p svex)
             (ha+1-s-chain-self-pattern-body
              svex
              (cond
               ((equal m 0)
                (sv::Svex-call
                 'sv::bitnot
                 (hons-list
                  (sv::svex-call 'sv::bitxor
                                 (hons-list (remove-ha-under-gates x)
                                            (remove-ha-under-gates y))))))
               ((equal m 1)
                (sv::Svex-call
                 'sv::bitxor
                 (hons-list
                  1
                  (sv::svex-call 'sv::bitxor
                                 (hons-list (remove-ha-under-gates x)
                                            (remove-ha-under-gates y))))))
               ((equal m 10)
                (sv::svex-call 'sv::bitxor
                               (hons-list (remove-ha-under-gates x)
                                          (remove-ha-under-gates y))))
               (t
                (sv::Svex-call svex.fn
                               (remove-ha-under-gates-lst svex.args))))))
            ((ha+1-c-chain-self-pattern-p svex)
             (ha+1-c-chain-self-pattern-body
              svex
              (sv::Svex-call 'sv::bitor (hons-list (remove-ha-under-gates x)
                                                   (remove-ha-under-gates y)))))
            (t (sv::Svex-call svex.fn
                              (remove-ha-under-gates-lst svex.args)) ;; should never come here..
               )))
          (res (if wrap-with-id (sv::svex-call 'sv::id (hons-list res)) res)))
       res)))

  (define remove-ha-under-gates-lst ((lst sv::svexlist-p)
                                     &key
                                     ((wrap-with-id booleanp) 'wrap-with-id)
                                     ((collected alistp) 'collected))
    :measure (sv::svexlist-count lst)
    :Returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    (if (atom lst)
        nil
      (hons (remove-ha-under-gates (car lst))
            (remove-ha-under-gates-lst (cdr lst)))))
  ///

  (verify-guards remove-ha-under-gates-lst-fn
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ()))))

  (memoize 'remove-ha-under-gates
           ;; :condition '(eq (sv::svex-kind svex) :call)
           )

  (defret-mutual correctness
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::Svex-eval$ res-svex env)
                      (sv::Svex-eval$ svex env)))
      :fn remove-ha-under-gates)
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::Svexlist-eval$ res-lst env)
                      (sv::Svexlist-eval$ lst env)))
      :fn remove-ha-under-gates-lst)
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (sv::svex-apply$
                              sv::svex-apply
                              sv::svex-call->fn
                              ha-c-chain
                              ha-s-chain
                              sv::svex-call->args
                              ha+1-s-chain
                              ha+1-c-chain)
                             ()))))

  (define remove-ha-under-gates-alist ((lst sv::svex-alist-p)
                                       &key
                                       ((wrap-with-id booleanp) 'wrap-with-id)
                                       ((collected alistp) 'collected))
    :Returns (res sv::svex-alist-p :hyp (sv::svex-alist-p lst))
    (if (atom lst)
        nil
      (acons (caar lst)
             (remove-ha-under-gates (cdar lst))
             (remove-ha-under-gates-alist (cdr lst))))
    ///
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::Svex-alist-eval$ res env)
                      (sv::Svex-alist-eval$ lst env)))
      :hints (("Goal"
               :expand ((sv::svex-alist-eval nil env))
               :in-theory (e/d (sv::svex-alist-eval$) ()))))))

(define remove-ha-pairs-under-gates-alist ((svex-alist sv::svex-alist-p)
                                           &key
                                           ((wrap-with-id booleanp) 'nil))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  (b* ((- (cw "--- Now removing misidentified half-adders.~%"))
       ((mv collected &)
        (collect-ha-args-under-gates-alist svex-alist))
       (found-num (len collected))
       ((when (equal found-num 0))
        (progn$ (cw "- Could not find any misidentified half-adder.~%")
                (fast-alist-free collected)
                svex-alist))
       (- (cw "- Removing ~p0 half-adders that are suspected to be misidentified.~%" found-num))
       (svex-alist (remove-ha-under-gates-alist svex-alist))
       (- (fast-alist-free collected)))
    svex-alist)
  ///
  (defret <fn>-is-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-alist-eval$ res env)
                    (sv::svex-alist-eval$ svex-alist env)))
    :hints (("goal"
             :do-not-induct t
             :in-theory (e/d ()
                             ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Remove unpaired fa-s

;; gather-adder-patterns-in-svex-alist adder-type='fa-self

(define remove-unpaired-fa-s---clean-pattern-alist ((pattern-alist pattern-alist-p)
                                                    (acc pattern-alist-p))
  :returns (res pattern-alist-p :hyp (and (pattern-alist-p acc)
                                          (pattern-alist-p pattern-alist)))
  (if (atom pattern-alist)
      acc
    (b* (((cons key value) (car pattern-alist))
         ((when (equal value '(fa-s-chain)))
          (remove-unpaired-fa-s---clean-pattern-alist
           (cdr pattern-alist)
           (hons-acons key value acc))))
      (remove-unpaired-fa-s---clean-pattern-alist (cdr pattern-alist)
                                                  acc))))

(defines remove-unpaired-fa-s-aux
  :hints (("Goal"
           :expand ((SV::SVEX-COUNT SVEX)
                    (SV::SVEX-COUNT (LIST 'FA-S-CHAIN SVEX3 SVEX5 SVEX7)))
           :in-theory (e/d (SV::SVEX-CALL->ARGS
                            FA-S-CHAIN-ITSELF-PATTERN-P)
                           ())))
  :verify-guards nil
  (define remove-unpaired-fa-s-aux ((svex sv::svex-p)
                                    &optional
                                    ((pattern-alist pattern-alist-p) 'pattern-alist))
    :returns (res sv::Svex-p :hyp (sv::svex-p svex))
    :measure (sv::Svex-count svex)
    (sv::Svex-case
     svex
     :var svex
     :quote svex
     :call (cond ((fa-s-chain-itself-pattern-p svex)
                  (fa-s-chain-itself-pattern-body
                   svex
                   (b* ((args (acl2::merge-sort-lexorder (list x y z)))
                        (found (hons-get args pattern-alist))
                        ((when found)
                         (hons-list 'sv::bitxor (remove-unpaired-fa-s-aux x)
                                    (hons-list 'sv::bitxor
                                               (remove-unpaired-fa-s-aux y)
                                               (remove-unpaired-fa-s-aux z)))))
                     (sv::svex-call svex.fn
                                    (remove-unpaired-fa-s-aux-lst svex.args)))))
                 (t (sv::svex-call svex.fn
                                   (remove-unpaired-fa-s-aux-lst svex.args))))))
  (define remove-unpaired-fa-s-aux-lst ((lst sv::svexlist-p)
                                        &optional
                                        ((pattern-alist pattern-alist-p) 'pattern-alist))
    :measure (sv::Svexlist-count lst)
    :returns (res sv::Svexlist-p :hyp (sv::svexlist-p lst))
    (if (atom lst)
        nil
      (hons (remove-unpaired-fa-s-aux (car lst))
            (remove-unpaired-fa-s-aux-lst (cdr lst)))))
  ///
  (verify-guards remove-unpaired-fa-s-aux-fn)
  (memoize 'remove-unpaired-fa-s-aux-fn
           ;; :condition '(eq (sv::svex-kind svex) :call)
           )

  (defret-mutual correctness
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::svex-eval$ res env)
                      (sv::svex-eval$ svex env)))
      :fn remove-unpaired-fa-s-aux)
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::svexlist-eval$ res env)
                      (sv::svexlist-eval$ lst env)))
      :fn remove-unpaired-fa-s-aux-lst)
    :hints (("Goal"
             :do-not-induct t
             :expand ((:free (args)
                             (sv::Svex-apply$ 'fa-s-chain args))
                      (:free (args)
                             (sv::Svex-apply 'SV::BItXOR args)))
             :in-theory (e/d (;;SV::SVEX-APPLY$
                              fa-s-chain
                              SV::SVEX-CALL->FN
                              SV::SVEX-CALL->args)
                             ())))))

(define remove-unpaired-fa-s-alist-aux ((x sv::svex-alist-p)
                                        &optional
                                        ((pattern-alist pattern-alist-p) 'pattern-alist))
  :returns (res sv::Svex-alist-p :hyp (sv::svex-alist-p x))
  (if (atom x)
      x
    (acons (caar x)
           (remove-unpaired-fa-s-aux (cdar x))
           (remove-unpaired-fa-s-alist-aux (cdr x))))
  ///
  (defret <fn>-is-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-alist-eval$ res env)
                    (sv::svex-alist-eval$ x env)))
    :hints (("goal"
             :in-theory (e/d (SV::SVEX-ALIST-EVAL$)
                             ())))))

(define remove-unpaired-fa-s-alist ((svex-alist sv::svex-alist-p)
                                    &key
                                    ((env) 'env)
                                    ((context rp-term-listp) 'context)
                                    ((config svl::svex-reduce-config-p) 'config))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  (b* ((- (cw "--- Now looking for unpaired full-adder-s~%"))
       ((mv pattern-alist &)
        (gather-adder-patterns-in-svex-alist svex-alist :adder-type 'fa-self :track-column? nil))
       (pattern-alist (fast-alist-clean pattern-alist))
       (pattern-alist (fast-alist-free pattern-alist))
       (pattern-alist (remove-unpaired-fa-s---clean-pattern-alist pattern-alist nil))
       (found-num (len pattern-alist))
       ((when (equal found-num 0))
        (progn$ (cw "- Could not find any unpaired full-adder.~%")
                (fast-alist-free pattern-alist)
                svex-alist))
       (- (cw "- Removing ~p0 unpaired full-adder-s patterns.~%" found-num))

       (svex-alist (remove-unpaired-fa-s-alist-aux svex-alist pattern-alist))

       (- (fast-alist-free pattern-alist)))
    svex-alist)
  ///
  (defret <fn>-is-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-alist-eval$ res free-env)
                    (sv::svex-alist-eval$ svex-alist free-env)))
    :hints (("goal"
             :do-not-induct t
             :in-theory (e/d ()
                             ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines merge-fa-s-c-chains
  :verify-guards nil

  (define merge-fa-s-c-chains ((x sv::svex-p)
                               &key
                               ((env) 'env)
                               ((context rp::rp-term-listp) 'context)
                               ((config svl::svex-reduce-config-p) 'config))

    :returns (res-svex sv::svex-p :hyp (sv::svex-p x))
    :measure (sv::Svex-count x)
    (sv::Svex-case
     x
     :var x
     :quote x
     :call (b* ((args (merge-fa-s-c-chains-lst x.args)))
             (cond ((and (eq x.fn 'fa-s-chain)
                         (svl::equal-len x.args 3)
                         (and* (svl::bitp-of-svex (first x.args))
                               (svl::bitp-of-svex (second x.args))
                               (svl::bitp-of-svex (third x.args))))
                    (sv::svex-call 'sv::partsel
                                   (hons-list 0 1
                                              (sv::svex-call 'full-adder args))))
                   ((and (eq x.fn 'fa-c-chain)
                         (svl::equal-len x.args 4)
                         (and* (valid-fa-c-chain-args-p (first x.args)
                                                        (second x.args))
                               (svl::bitp-of-svex (second x.args))
                               (svl::bitp-of-svex (third x.args))
                               (svl::bitp-of-svex (fourth x.args))))
                    (sv::svex-call 'sv::partsel
                                   (hons-list 1 1
                                              (sv::svex-call 'full-adder (cdr args)))))

                   ((and (eq x.fn 'ha-s-chain)
                         (svl::equal-len x.args 2)
                         (and* (svl::bitp-of-svex (first x.args))
                               (svl::bitp-of-svex (second x.args))))
                    (sv::svex-call 'sv::partsel
                                   (hons-list 0 1
                                              (sv::svex-call 'half-adder args))))
                   ((and (eq x.fn 'ha-c-chain)
                         (svl::equal-len x.args 2)
                         (and* (svl::bitp-of-svex (first x.args))
                               (svl::bitp-of-svex (second x.args))))
                    (sv::svex-call 'sv::partsel
                                   (hons-list 1 1
                                              (sv::svex-call 'half-adder args))))

                   ((and (eq x.fn 'ha+1-s-chain)
                         (svl::equal-len x.args 3)
                         (and* (integerp (first x.args))
                               (not (equal (first x.args) 0))  ;; the 0 case is
                               ;; defined   with
                               ;; bitnot. Expected
                               ;; to  never  use
                               ;; that.
                               (svl::bitp-of-svex (second x.args))
                               (svl::bitp-of-svex (third x.args))))
                    (b* ((base (sv::svex-call 'sv::partsel
                                              (hons-list 0 1
                                                         (sv::svex-call 'full-adder
                                                                        (hons 1 (cdr args)))))))
                      (if (equal (first x.args) 10) ;; when this is 10, it means it was matched with carry+1
                          (sv::Svex-call 'sv::bitxor (hons-list 1 base))
                        base)))
                   ((and (eq x.fn 'ha+1-c-chain)
                         (svl::equal-len x.args 2)
                         (and* (svl::bitp-of-svex (first x.args))
                               (svl::bitp-of-svex (second x.args))))
                    (sv::svex-call 'sv::partsel
                                   (hons-list 1 1
                                              (sv::svex-call 'full-adder (hons 1 args)))))

                   (t (sv::svex-call x.fn args))))))

  (define merge-fa-s-c-chains-lst ((lst sv::svexlist-p)
                                   &key
                                   ((env) 'env)
                                   ((context rp::rp-term-listp) 'context)
                                   ((config svl::svex-reduce-config-p) 'config))
    :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        nil
      (hons (merge-fa-s-c-chains (car lst))
            (merge-fa-s-c-chains-lst (cdr lst)))))
  ///

  (verify-guards merge-fa-s-c-chains-fn)

  (memoize 'merge-fa-s-c-chains
           ;; :condition '(eq (sv::svex-kind x) :call)
           )

  (local
   (defthm sv::4vec-part-select-of-fa-chains/s-c-spec-lemma
     (implies (and (bitp x) (bitp y) (bitp z))
              (and (equal (sv::4vec-part-select 0 1 (fa-c-chain 0 x y z))
                          (fa-c-chain 0 x y z))
                   (equal (sv::4vec-part-select 0 1 (c-spec (list x y z)))
                          (c-spec (list x y z)))
                   (equal (sv::4vec-part-select 0 1 (s-spec (list x y z)))
                          (s-spec (list x y z)))))
     :hints (("Goal"
              :in-theory (e/d (bitp
                               FA-C-CHAIN)
                              ())))))

  (local
   (defthm sv::4vec-part-select-of-fa-chains/s-c-spec-lemma-2
     (implies (and (bitp x) (bitp y))
              (and (equal (sv::4vec-part-select 0 1 (c-spec (list x y)))
                          (c-spec (list x y)))
                   (equal (sv::4vec-part-select 0 1 (s-spec (list x y)))
                          (s-spec (list x y)))))
     :hints (("Goal"
              :in-theory (e/d (bitp
                               FA-C-CHAIN)
                              ())))))

  (local
   (defthm ha+1-s-chain-to-s-spec-lemma
     (implies (and (bitp x) (bitp y) (not (equal m 0)))
              (and (equal (ha+1-s-chain m x y)
                          (if (equal m 10)
                              (s-spec (list x y))
                            (s-spec (list 1 x y))))))
     :hints (("Goal"
              :in-theory (e/d (BITP ha+1-s-chain)
                              ())))))

  (local
   (defthm negate-of-s-spec-with-1
     (implies (and (bitp x)
                   (bitp y))
              (equal (LOGXOR 1 (S-SPEC (LIST 1 x y)))
                     (S-SPEC (LIST x y))))
     :hints (("Goal"
              :in-theory (e/d (bitp) ())))))

  (local
   (defthm s/c-spec-move-consts
     (and (equal (c-spec (list x y 1))
                 (c-spec (list 1 x y)))
          (equal (s-spec (list x y 1))
                 (s-spec (list 1 x y)))

          (equal (s-spec (list 0 x y))
                 (s-spec (list x y)))
          (equal (c-spec (list 0 x y))
                 (c-spec (list x y))))
     :hints (("Goal"
              :in-theory (e/d (c-spec s-spec SUM-LIST sum) ())))))

  (local
   (in-theory (disable svl::width-of-svex-extn-correct$-lst
                       svl::width-of-svex-extn-correct$
                       svexlist-p-implies-true-listp
                       (:rewrite acl2::apply$-badgep-properties . 1)
                       (:definition pattern-alist-p)
                       (:definition integer-listp)
                       member-equal
                       DEFAULT-CDR
                       DEFAULT-CAR
                       RP-TRANS)))

  (defret-mutual <fn>-is-correct
    (defret <fn>-is-correct
      (implies (and (sv::svex-p x)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    (warrants-for-adder-pattern-match))
               (equal (sv::svex-eval$ res-svex (rp-evlt env-term a))
                      (sv::svex-eval$ x (rp-evlt env-term a))))
      :fn merge-fa-s-c-chains)
    (defret <fn>-is-correct
      (implies (and (sv::svexlist-p lst)
                    (warrants-for-adder-pattern-match)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config))
                    )
               (equal (sv::svexlist-eval$ res-lst (rp-evlt env-term a))
                      (sv::svexlist-eval$ lst (rp-evlt env-term a))))
      :fn merge-fa-s-c-chains-lst)
    :hints (("Goal"
             :do-not-induct t
             :expand ((merge-fa-s-c-chains x)
                      (merge-fa-s-c-chains-lst lst))
             :in-theory (e/d (SVL::LOGAPP-TO-4VEC-CONCAT
                              S-C-SPEC
                              SVL::4VEC-CONCAT$
                              SV::SVEXLIST-EVAL$
                              SV::SVEX-APPLY
                              sv::svex-apply$
                              full-adder half-adder)
                             ()))))

  (define merge-fa-s-c-chains-alist ((alist sv::svex-alist-p)
                                     &key
                                     ((env) 'env)
                                     ((context rp::rp-term-listp) 'context)
                                     ((config svl::svex-reduce-config-p) 'config))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p alist))
    (if (atom alist)
        nil
      (acons (caar alist)
             (merge-fa-s-c-chains (cdar alist))
             (merge-fa-s-c-chains-alist (cdr alist))))
    ///
    (defret <fn>-is-correct
      (implies (and (sv::svex-alist-p alist)
                    (warrants-for-adder-pattern-match)
                    (rp::rp-term-listp context)
                    (rp::valid-sc env-term a)
                    (rp::eval-and-all context a)
                    (rp::falist-consistent-aux env env-term)
                    (svl::width-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->width-extns config))
                    (svl::integerp-of-svex-extn-correct$-lst
                     (svl::svex-reduce-config->integerp-extns config)))
               (equal (sv::svex-alist-eval$ res (rp-evlt env-term a))
                      (sv::svex-alist-eval$ alist (rp-evlt env-term a))))
      :hints (("goal"
               :do-not-induct t
               :induct (merge-fa-s-c-chains-alist alist)
               :in-theory (e/d (sv::svex-alist-eval$)
                               (merge-fa-s-c-chains))))))

  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define missed-adder-warning--adder-p (term
                                       nodes
                                       (limit natp))
  :measure (nfix limit)
  (if (zp limit)
      nil
    (case-match term
      (('sv::Bitxor 1 x)
       (missed-adder-warning--adder-p x nodes (1- limit)))
      (('id x)
       (missed-adder-warning--adder-p x nodes (1- limit)))
      (('sv::Bitxor x 1)
       (missed-adder-warning--adder-p x nodes (1- limit)))
      ((':node num)
       (b* ((x (hons-get num nodes)))
         (and (consp x)
              (missed-adder-warning--adder-p (cdr x) nodes (1- limit)))))
      ((fn . &)
       (or (equal fn 'fa-c-chain)
           (equal fn 'fa-s-chain)
           (equal fn 'full-adder)
           (equal fn 'half-adder)
           (equal fn 'ha-s-chain)
           (equal fn 'ha-c-chain)
           (equal fn 'ha+1-s-chain)
           (equal fn 'ha+1-c-chain))))))

(defines missed-adder-warning--traverse-node
  (define missed-adder-warning--traverse-node (node-term
                                               node-num
                                               nodes
                                               under-gate
                                               (limit natp))
    (b* (((when (zp limit))
          nil)
         (found (and under-gate
                     (missed-adder-warning--adder-p node-term nodes *large-number*)
                     (Not
                      (cwe "(:node ~p0). Node-term: ~p1 under ~p2.~%"
                           node-num node-term under-gate))))
         ((Unless (and (equal (svl::svexl-node-kind-wog node-term) :call)
                       (consp node-term)))
          found)
         (under-gate (or (and (equal (car node-term) 'sv::bitor) 'sv::bitor)
                         (and (equal (car node-term) 'sv::bitand) 'sv::bitand)
                         (and* (equal (car node-term) 'sv::bitxor)
                               (not (equal (nth 1 (true-list-fix node-term)) 1))
                               (not (equal (nth 2 (true-list-fix node-term)) 1))
                               'sv::bitxor)
                         (and (equal (car node-term) 'sv::partsel) under-gate))))
      (or*
       (missed-adder-warning--traverse-node-lst (cdr node-term)
                                                node-num
                                                nodes
                                                under-gate
                                                (1- limit))
       found)))

  (define missed-adder-warning--traverse-node-lst (node-lst
                                                   node-num
                                                   nodes
                                                   under-gate
                                                   (limit natp))
    (if (or (zp limit)
            (atom node-lst))
        nil
      (or* (missed-adder-warning--traverse-node (car node-lst)
                                                node-num
                                                nodes
                                                under-gate
                                                (1- limit))
           (missed-adder-warning--traverse-node-lst (cdr node-lst)
                                                    node-num
                                                    nodes
                                                    under-gate
                                                    (1- limit))))))

(define missed-adder-warning--iter ((term-alist alistp)
                                    nodes)
  (if (atom term-alist)
      nil
    (b* ((node-num (caar term-alist))
         (node-term (cdar term-alist)))
      (or* (missed-adder-warning--traverse-node node-term
                                                node-num
                                                nodes
                                                nil
                                                *large-number*)
           (missed-adder-warning--iter (cdr term-alist) nodes)))))

;;(include-book "books/centaur/misc/hons-extra" :dir :system)

(define missed-adder-warning ((svexl-alist svl::svexl-alist-p))
  (b* (((svl::svexl-alist x) svexl-alist)
       (x.node-array (make-fast-alist x.node-array)) ;;((with-fast x.node-array))
       ((Unless (and (alistp x.top-node-alist) ;; for guards
                     (alistp x.node-array)))
        nil)

       (- (cw "- Checking if any adders are nested in other gates...~%"))

       (found1 (missed-adder-warning--iter x.top-node-alist
                                           x.node-array))
       (found2 (missed-adder-warning--iter x.node-array
                                           x.node-array))

       (- (if (or found1 found2)
              (cw "- Some adders are nested within or/and/xor gates. This may cause problems...~%")
            (cw "-> Could not find any adders nested within gates. That's good.~%")))
       )
    nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Try to add ha-c-chain for shifted outputs

(defines add-ha-c-for-shifted-search
  :verify-guards nil
  (define add-ha-c-for-shifted-search ((x sv::svex-p)
                                       (under-adder))
    :returns (mv (collected true-listp)
                 (good-args integerp))
    :measure (sv::Svex-count x)
    (sv::svex-case
     x
     :var (mv nil 1)
     :quote (mv nil 1)
     :call
     (cond ((or* (equal x.fn 'ha-c-chain)
                 (equal x.fn 'ha-s-chain)
                 (equal x.fn 'fa-c-chain)
                 (equal x.fn 'fa-s-chain)
                 (equal x.fn 'ha+1-s-chain)
                 (equal x.fn 'ha+1-c-chain))
            (b* (((mv collected &)
                  (add-ha-c-for-shifted-search-lst x.args t)))
              (mv collected 3)))
           ((and* (svl::equal-len x.args 2)
                  (equal x.fn 'sv::bitand))
            (b* (((mv collected good-args)
                  (add-ha-c-for-shifted-search-lst x.args under-adder))
                 ((when (and under-adder
                             (equal good-args 3)))
                  (mv (cons x collected) 3)))
              (mv collected 0)))
           ((or* (equal x.fn 'sv::?*)
                 (equal x.fn 'sv::?))
            (mv nil 3))
           (t (add-ha-c-for-shifted-search-lst x.args nil)))))

  (define add-ha-c-for-shifted-search-lst ((lst sv::Svexlist-p)
                                           (under-adder))
    :returns (mv (collected true-listp)
                 (good-args integerp))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        (mv nil 0)
      (b* (((mv c1 g1) (add-ha-c-for-shifted-search (car lst)
                                                    under-adder))
           ((mv c2 g2) (add-ha-c-for-shifted-search-lst (cdr lst)
                                                        under-adder)))
        (mv (append c1 c2)
            (logior g1 g2)))))
  ///
  (verify-guards add-ha-c-for-shifted-search)
  (memoize 'add-ha-c-for-shifted-search
           ;; :condition '(eq (sv::svex-kind x) :call)
           )
  ;; no need to verify anything.

  (define add-ha-c-for-shifted-search-main ((x sv::svex-p))
    :Returns (collected-lst true-listp)
    (case-match x
      (('sv::concat size a b)
       (cond ((not (natp size))
              nil)
             ((= size 1)
              (b* (((mv c &)
                    (add-ha-c-for-shifted-search a nil)))
                ;; ((Unless c) nil)
                ;; (c (make-fast-alist (pairlis$ c nil)))
                ;; (c (fast-alist-clean c)))
                c))
             ((> size 1)
              (add-ha-c-for-shifted-search-main a))
             (t
              (add-ha-c-for-shifted-search-main b))))
      (& (b* (((mv c &)
               (add-ha-c-for-shifted-search x nil)))
           c))))

  (define add-ha-c-for-shifted-search-alist ((x sv::svex-alist-p))
    :Returns (collected-lst true-listp)
    (if (atom x)
        nil
      (append (add-ha-c-for-shifted-search-main (cdar x))
              (add-ha-c-for-shifted-search-alist (cdr x))))))

(defines add-ha-c-for-shifted
  :verify-guards nil
  (define add-ha-c-for-shifted  ((x sv::svex-p)
                                 (collected))
    :returns (res-svex sv::svex-p :hyp (sv::svex-p x))
    :measure (sv::Svex-count x)
    (sv::svex-case
     x
     :var x
     :quote x
     :call
     (cond ((and*-exec
             (equal x.fn 'sv::bitand)
             (svl::equal-len x.args 2)
             (hons-get x collected))
            (sv::Svex-call 'ha-c-chain
                           (add-ha-c-for-shifted-lst x.args collected)))
           (t (sv::Svex-call x.fn
                             (add-ha-c-for-shifted-lst x.args collected))))))

  (define add-ha-c-for-shifted-lst ((lst sv::Svexlist-p)
                                    (collected))
    :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p lst))
    :measure (sv::Svexlist-count lst)
    (if (atom lst)
        nil
      (hons (add-ha-c-for-shifted (car lst) collected)
            (add-ha-c-for-shifted-lst (cdr lst) collected))))
  ///
  (verify-guards add-ha-c-for-shifted)
  (memoize 'add-ha-c-for-shifted
           ;; :condition '(eq (sv::svex-kind x) :call)
           )

  (defret-mutual <fn>-is-correct
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::svex-eval$ res-svex env)
                      (sv::svex-eval$ x env)))
      :fn add-ha-c-for-shifted)
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::svexlist-eval$ res-lst env)
                      (sv::svexlist-eval$ lst env)))
      :fn add-ha-c-for-shifted-lst)
    :hints (("Goal"
             :do-not-induct t
             :expand ()
             :in-theory (e/d (sv::svex-apply$
                              sv::svex-apply
                              ha-c-chain)
                             ()))))

  (define add-ha-c-for-shifted-alist ((x sv::Svex-alist-p)
                                      (collected))
    :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p x))
    (if (atom x)
        nil
      (acons (caar x)
             (add-ha-c-for-shifted (cdar x) collected)
             (add-ha-c-for-shifted-alist (cdr x) collected)))
    ///
    (defret <fn>-is-correct
      (implies (warrants-for-adder-pattern-match)
               (equal (sv::svex-alist-eval$ res env)
                      (sv::svex-alist-eval$ x env)))
      :hints (("Goal"
               :in-theory (e/d (sv::svex-alist-eval$
                                sv::svex-alist-eval)
                               ()))))))

(define search-and-add-ha-c-for-shifted ((x sv::Svex-alist-p))
  :returns (res sv::svex-alist-p :hyp (sv::svex-alist-p x))
  :prepwork
  ()

  (b* (((unless (search-and-add-ha-c-for-shifted-enabled))
        x)
       (collected-lst (add-ha-c-for-shifted-search-alist x))
       ((Unless collected-lst) x)
       (c (make-fast-alist (pairlis$ collected-lst nil)))
       (c (fast-alist-clean c))
       (- (and c
               (cw "- Marking ~p0 half-adder carry patterns that are suspected to ~
        come from a shifted data output result. If the proof fails and this is ~
        not a shifted multiplier/adder, then try disabling this heuristic by ~
        calling: ~p1~%~%" (len c) '(enable-search-and-add-ha-c-for-shifted
                                    nil))))
       ((Unless c) x)
       (x (add-ha-c-for-shifted-alist x c))
       (- (fast-alist-free c)))
    x)
  ///
  (defret <fn>-is-correct
    (implies (warrants-for-adder-pattern-match)
             (equal (sv::svex-alist-eval$ res env)
                    (sv::svex-alist-eval$ x env)))
    :hints (("Goal"
             :in-theory (e/d (sv::svex-alist-eval$
                              sv::svex-alist-eval)
                             ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(make-event
 `(define svex-reduce-w/-env-config-1 ()
    :returns (config svl::svex-reduce-config-p)
    (svl::make-svex-reduce-config
     :width-extns ',(strip-cars (table-alist 'svl::width-of-svex-extns (w state)))
     :integerp-extns ',(strip-cars (table-alist 'svl::integerp-of-svex-extns (w state)))
     :keep-missing-env-vars (keep-missing-env-vars-in-svex))
    ///
    (defret <fn>-correct
      (and (implies (warrants-for-adder-pattern-match)
                    (and (svl::width-of-svex-extn-correct$-lst
                          (svl::svex-reduce-config->width-extns config))
                         (svl::integerp-of-svex-extn-correct$-lst
                          (svl::svex-reduce-config->integerp-extns config)))))
      :hints (("Goal"
               :do-not-induct t
               :use (,@(loop$ for x in (strip-cdrs (table-alist 'svl::width-of-svex-extns (w state)))
                              collect
                              `(:instance ,x))
                     ,@(loop$ for x in (strip-cdrs (table-alist 'svl::integerp-of-svex-extns (w state)))
                              collect
                              `(:instance ,x)))
               :in-theory (e/d (svl::width-of-svex-extn-correct$-lst)
                               (svl::integerp-of-svex-extn-correct$
                                svl::width-of-svex-extn-correct$)
                               ))))
    (in-theory (disable (:e svex-reduce-w/-env-config-1)))))

(local
 (in-theory (enable subsetp-equal)))

(make-event
 (b* ((w '((apply$-warrant-ha-c-chain)
           (apply$-warrant-fa-c-chain)
           (apply$-warrant-ha+1-c-chain)
           (apply$-warrant-ha+1-s-chain)
           (apply$-warrant-ha-s-chain)
           (apply$-warrant-fa-s-chain)
           (apply$-warrant-full-adder)
           (apply$-warrant-half-adder))))
   `(define check-context-for-adder-warrants ((context rp-term-listp))
      :returns valid
      (subsetp-equal ',w context)
      ///
      (local
       (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))
      (local
       (defthm member-equal-and-eval-and-all
         (implies (and (eval-and-all context a)
                       (member-equal x context))
                  (and (rp-evlt x a)
                       (implies (force (not (include-fnc x 'list)))
                                (rp-evl x a))))
         :rule-classes (:rewrite)))
      (local
       (in-theory (disable eval-and-all)))
      (defret <fn>-is-correct
        (implies (and (eval-and-all context acl2::unbound-free-env)
                      (rp-evl-meta-extract-global-facts)
                      (find-adders-in-svex-formula-checks state)
                      valid)
                 (and ,@w))
        :hints (("Goal"
                 :do-not-induct t
                 :in-theory (e/d () ())))))))

(define vescmul-clear-memoize-tables ()
  (progn$ (clear-memoize-table 's-order)
          (clear-memoize-table 'svl::width-of-svex-fn)
          (clear-memoize-table 'svl::integerp-of-svex-fn)
          (clear-memoize-table 'svl::svex-reduce-w/-env-fn)
          (clear-memoize-table 'svl::svex-reduce-w/-env-masked-fn)
          (clear-memoize-table 'adder-pattern-match)
          (clear-memoize-table 'clear-adder-fnc-from-unfloat)
          (clear-memoize-table 'replace-adder-patterns-in-svex)
          (clear-memoize-table 'fix-order-of-fa/ha-s-args)
          (clear-memoize-table 'svl::bitand/or/xor-cancel-repeated)
          (clear-memoize-table 'simplify-to-find-fa-c-patterns-fn)
          (clear-memoize-table 'wrap-pp-with-id-aux)
          (clear-memoize-table 'add-ha-c-for-shifted)
          (clear-memoize-table 'extract-svex-from-id)
          (clear-memoize-table 'global-zero-fa-c-chain-extra-arg)
          (clear-memoize-table 'fix-order-of-fa/ha-chain-args-fn)
          (clear-memoize-table 'ppx-simplify-fn)
          (clear-memoize-table 'remove-ha-under-gates)
          (clear-memoize-table 'remove-unpaired-fa-s-aux-fn)
          (clear-memoize-table 'merge-fa-s-c-chains)
          (clear-memoize-table 'add-ha-c-for-shifted-search)))

(with-output
  :off :all
  :gag-mode :goals
  :on (error summary)
  (define rewrite-adders-in-svex-alist ((term)
                                        (context rp-term-listp))
    :returns (mv res-term res-dont-rw)
    :guard-debug t
    (case-match term
      (('sv::svex-alist-eval ('quote svex-alist) env-orig)
       (b* ((- (vescmul-clear-memoize-tables))

            (env (rp::ex-from-rp env-orig))
            ((mv falistp env) (case-match env
                                (('falist ('quote x) &) (mv t x))
                                (& (mv nil env))))
            ((unless falistp)
             (if (and (consp env) (equal (car env) 'cons))
                 (progn$
                  (cw "Note: the environment of svex-eval-alist is not a fast-alist. Making it a fast-alist now.~%")
                  (mv `(sv::svex-alist-eval ',svex-alist (make-fast-alist ,env-orig))
                      `(nil t (nil t))))
               (mv term nil)))

            ((Unless (sv::svex-alist-p svex-alist)) ;; for guards
             (mv term (raise "given sv::svex-alist does not have sv::svex-alist: ~p0." svex-alist)))
            ((Unless (sv::svex-alist-no-foreign-op-p svex-alist)) ;; to convert svex-eval to eval$
             (mv term (raise "given sv::svex-alist has foreign operands: ~p0" svex-alist)))
            ((Unless (check-context-for-adder-warrants context)) ;; check for existence of warrants.
             (mv term (raise "Some necessary warrants were not found in the context: ~p0" context)))

            (config (svex-reduce-w/-env-config-1))

            (- (cw "Starting: svl::svex-alist-reduce-w/-env. ~%"))
            (- (time-tracker :rewrite-adders-in-svex :end))
            (- (time-tracker :rewrite-adders-in-svex :init
                             :times '(1 2 3 4 5)
                             :interval 5
                             ))
            (- (time-tracker :rewrite-adders-in-svex :start!))
            (config (svl::change-svex-reduce-config
                     config :skip-bitor/and/xor-repeated t))
            (svex-alist (svl::svexalist-convert-bitnot-to-bitxor svex-alist))
            (svex-alist (svl::svex-alist-reduce-w/-env svex-alist :env env :config config))
            (- (acl2::sneaky-save 'orig-svex-alist svex-alist))
            (- (time-tracker :rewrite-adders-in-svex :stop))
            (- (time-tracker :rewrite-adders-in-svex :print?
                             :min-time 0
                             :msg "The total runtime of svl::svex-alist-reduce-w/-env ~
was ~st seconds."))

            (config (svl::change-svex-reduce-config
                     config
                     :skip-bitor/and/xor-repeated nil
                     :keep-missing-env-vars nil))

            (- (cw "Starting: rp::rewrite-adders-in-svex-alist. ~%"))
            (- (time-tracker :rewrite-adders-in-svex :end))
            (- (time-tracker :rewrite-adders-in-svex :init
                             :times '(1 2 3 4 5)
                             :interval 5
                             ))
            (- (time-tracker :rewrite-adders-in-svex :start!))

            (- (if (aggressive-find-adders-in-svex)
                   (cw "Aggressive mode is enabled. Disabling may reduce the time spent during adder pattern search. To disable run:~%(rp::enable-aggressive-find-adders-in-svex nil) ~%~%")
                 (cw "Warning: Aggressive mode is disabled. Enabling may help a failing proof go through. To enable run:~%(rp::enable-aggressive-find-adders-in-svex t) ~%")))

            (svex-alist (wrap-pp-with-id-alist svex-alist))
            (find-f/h-adders-state (make-find-f/h-adders-state))

            (svex-alist (find-f/h-adders-in-svex-alist svex-alist
                                                       *find-f/h-adders-in-svex-alist-limit*
                                                       :adder-type 'fa))

            ;;(- (design_res-broken svex-alist "after-fa"))

            #|(- (cwe "resulting svexl-alist after full-adders ~p0 ~%"
            (svl::svex-alist-to-svexl-alist svex-alist)))|#

            (- (acl2::sneaky-save 'after-fa svex-alist))
            (- (cw "~%Access the svexl-alist after full-adder search:
(b* (((mv res state) (acl2::sneaky-load 'rp::after-fa state)))
   (mv state (svl::svex-alist-to-svexl-alist res))) ~%"))

            (- (time-tracker :rewrite-adders-in-svex :stop))
            (- (time-tracker :rewrite-adders-in-svex :print?
                             :min-time 0
                             :msg "Search for full adder patterns took ~st secs.~%~%"))

            (- (time-tracker :rewrite-adders-in-svex :end))
            (- (time-tracker :rewrite-adders-in-svex :init
                             :times '(1 2 3 4 5)
                             :interval 5
                             ))
            (- (time-tracker :rewrite-adders-in-svex :start!))

            ;;(svex-alist (svl::light-svex-alist-simplify-bitand/or/xor svex-alist))

            (svex-alist (find-f/h-adders-in-svex-alist svex-alist
                                                       *find-f/h-adders-in-svex-alist-limit*
                                                       :adder-type 'ha
                                                       :find-f/h-adders-state (change-find-f/h-adders-state
                                                                               find-f/h-adders-state
                                                                               :track-column? 20)))
            (- (acl2::sneaky-save 'after-round1 svex-alist))
            (- (cw "~%Access the svexl-alist after full-adder and half-adder search:
(b* (((mv res state) (acl2::sneaky-load 'rp::after-round1 state)))
   (mv state (svl::svex-alist-to-svexl-alist res))) ~%"))

            ;; run again without the track-column blocking.
            ;; (- (cw "~%--- Running half-adder search again with less restrictions~%"))
            ;; (svex-alist (find-f/h-adders-in-svex-alist svex-alist
            ;;                                            *find-f/h-adders-in-svex-alist-limit*
            ;;                                            :adder-type 'ha
            ;;                                            :find-f/h-adders-state (change-find-f/h-adders-state
            ;;                                                                    find-f/h-adders-state
            ;;                                                                    :skip-light-simplify t
            ;;                                                                    :skip-vector-adder t)))

            ;;(- (design_res-broken svex-alist "after-ha"))

            (- (time-tracker :rewrite-adders-in-svex :stop))
            (- (time-tracker :rewrite-adders-in-svex :print?
                             :min-time 0
                             :msg "Search for half adder patterns took ~st secs.~%~%"))

          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
            ;; Final leg
            (- (time-tracker :rewrite-adders-in-svex :end))
            (- (time-tracker :rewrite-adders-in-svex :init
                             :times '(1 2 3 4 5)
                             :interval 5
                             ))
            (- (time-tracker :rewrite-adders-in-svex :start!))

            (- (cw "~%"))
            (- (cw "Now will perform global simplification, remove potentialy misidentified half-adders, perform another round of full-adder/half-adder detection, and finalize the search. ~%~%"))

            ;; (- (cw "--- Let's try to reduce number of negations~%"))
            ;; (new-svex-alist (svl::svex-alist-reduce-bit-negations svex-alist))
            ;; (- (if (hons-equal new-svex-alist svex-alist)
            ;;        (cw "-> Nothing is changed after negation reduction attempt. ~%")
            ;;      (cw "-> Could clean some number negations. ~%")))
            ;; (svex-alist new-svex-alist)

            ;; I have  seen a case (32X32_UBP_AR_VCSkA)  where simplifying before
            ;; removing ha-pairs helps.
            (svex-alist (svl::svex-alist-simplify-bitand/or/xor svex-alist :nodes-to-skip-alist nil))
            (svex-alist (fix-order-of-fa/ha-chain-args-alist svex-alist))

            (svex-alist (search-and-add-ha-c-for-shifted svex-alist))

            ;;(- (design_res-broken svex-alist "before remove-ha-pairs-under-gates-alist"))

            (new-svex-alist (remove-unpaired-fa-s-alist svex-alist))
            ;; remove half-adders under gates..
            (new-svex-alist (remove-ha-pairs-under-gates-alist new-svex-alist))
            ;; try maybe global simplification here to clear out more clutter. Maybe this is unnecessary

            ;;(- (design_res-broken svex-alist "after remove-ha-pairs-under-gates-alist"))

            (disable-search (and (not (aggressive-find-adders-in-svex))
                                 (equal new-svex-alist svex-alist)))
            (- (and disable-search
                    (cw "- Agressive mode is disabled and removing adders did not change anything -> ending the search.~%")))
            (svex-alist new-svex-alist)

            ;; There's  something  off  somewhere  that calling  this  twice  was
            ;; necessary to properly clean stuff.  May have to do with inside-out
            ;; vs. outside-in simplificaiton
            (svl::nodes-to-skip-alist nil)
            (svex-alist (if disable-search svex-alist (svl::svex-alist-simplify-bitand/or/xor-outside-in svex-alist)))
            (svex-alist (if disable-search svex-alist (svl::svex-alist-simplify-bitand/or/xor svex-alist)))
            (svex-alist (if disable-search svex-alist (fix-order-of-fa/ha-chain-args-alist svex-alist)))

            #|(- (cwe "resulting svexl-alist after removing half-adders and global simplification ~p0 ~%"
            (svl::svex-alist-to-svexl-alist svex-alist)))|#

            (find-f/h-adders-state (change-find-f/h-adders-state find-f/h-adders-state
                                                                 :pp-id-cleaned t
                                                                 :reduce-bit-negations t))
            (svex-alist (if disable-search svex-alist
                          (find-f/h-adders-in-svex-alist svex-alist
                                                         *find-f/h-adders-in-svex-alist-limit*
                                                         :adder-type 'fa)))
            (- (cw "---~%"))
            (svex-alist (if disable-search svex-alist
                          (find-f/h-adders-in-svex-alist svex-alist
                                                         *find-f/h-adders-in-svex-alist-limit*
                                                         :adder-type 'ha
                                                         :find-f/h-adders-state (change-find-f/h-adders-state
                                                                                 find-f/h-adders-state
                                                                                 :track-column? 2
                                                                                 :skip-vector-adder t))))
            (- (cw "---~%"))
            (svex-alist (if disable-search svex-alist
                          (find-f/h-adders-in-svex-alist svex-alist
                                                         *find-f/h-adders-in-svex-alist-limit*
                                                         :adder-type 'fa
                                                         :find-f/h-adders-state (change-find-f/h-adders-state
                                                                                 find-f/h-adders-state
                                                                                 :only-quick-search t))))

            (- (acl2::sneaky-save 'after-round2 svex-alist))
            (- (cw "~%Access the svexl-alist after the second round of full-adder and half-adder search:
(b* (((mv res state) (acl2::sneaky-load 'rp::after-round2 state)))
   (mv state (svl::svex-alist-to-svexl-alist res))) ~%"))

            (svex-alist (if disable-search svex-alist
                          (svl::svex-alist-simplify-bitand/or/xor svex-alist))) ;; prob unnecessary
            (svex-alist (if disable-search svex-alist
                          (remove-ha-pairs-under-gates-alist svex-alist :wrap-with-id t)))
            (svex-alist (if disable-search svex-alist
                          (remove-unpaired-fa-s-alist svex-alist)))
            ;; (svex-alist (if disable-search svex-alist
            ;;               (svl::svex-alist-simplify-bitand/or/xor svex-alist))) ;; prob unnecessary

            ;; to be enabled manually to make s-c-spec-meta work faster. but left
            ;; disabled by default because debugging becomes difficult with this.
            (svex-alist (if (merge-fa-chains)
                            (merge-fa-s-c-chains-alist svex-alist)
                          svex-alist))

            (- (time-tracker :rewrite-adders-in-svex :stop))
            (- (time-tracker :rewrite-adders-in-svex :print?
                             :min-time 0
                             :msg "Final round of searching for adders took ~st secs.~%~%"))
          ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

            (- (cw "Finished: rp::rewrite-adders-in-svex-alist.~%"))

            (- (cw "Starting: svl::svex-alist-to-svexl-alist ~%"))
            (svexl-alist (svl::svex-alist-to-svexl-alist svex-alist))
            (- (let ((x (svl::svexl-alist->node-array svexl-alist))) ;; for guards
                 (cw "Finished: svl::svex-alist-to-svexl-alist. Resulting svexl-alist has ~p0 nodes.~%~%" (len x))))

            (- (missed-adder-warning svexl-alist))

            ;;(- (cwe "resulting svexl-alist: ~p0 ~%" svexl-alist))
            (- (acl2::sneaky-save 'after-all svexl-alist))
            (- (cw "Access the resulting svexl-alist:~%(acl2::sneaky-load 'rp::after-all state)~%"))

            (- (clear-memoize-table 'replace-adder-patterns-in-svex))

            (& (hons-clear t))
            )
         (mv `(svl::svexl-alist-eval$ ',svexl-alist ,env-orig)
             `(nil t t))))
      (& (mv term nil)))
    ///

    (local
     (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

    (local
     (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

    (local
     (defthm is-rp-of-others
       (implies (not (equal (car term) 'rp))
                (not (is-rp term)))
       :hints (("Goal"
                :in-theory (e/d (is-rp) ())))))

    (local
     (defthm is-equals-of-others
       (implies (not (equal (car term) 'equals))
                (not (is-equals term )))
       :hints (("Goal"
                :in-theory (e/d (is-equals) ())))))

    (local
     (defthm is-if-of-others
       (implies (not (equal (car term) 'if))
                (not (is-if term)))
       :hints (("Goal"
                :in-theory (e/d (is-if) ())))))

    (local
     (create-regular-eval-lemma sv::svex-alist-eval 2  find-adders-in-svex-formula-checks))

    (local
     (create-regular-eval-lemma svl::SVEXL-ALIST-EVAL$ 2 find-adders-in-svex-formula-checks))

    (local
     (create-regular-eval-lemma MAKE-FAST-ALIST 1 find-adders-in-svex-formula-checks))

    (local
     (defthm rp-evlt-of-quoted
       (equal (rp-evlt (list 'quote x) a)
              x)))

    (local
     (defthmd rp-evlt-of-ex-from-rp-reverse
       (implies (syntaxp (equal term 'term))
                (equal (rp-evlt (caddr term) a)
                       (rp-evlt (ex-from-rp (caddr term)) a)))))

    (local
     (defthm dummy-lemma-
       (implies (consp (ex-from-rp term))
                (consp term))
       :rule-classes :forward-chaining))

    (local
     (defthm dummy-lemma-2
       (implies (equal (car (ex-from-rp term)) 'falist)
                (not (equal (car term) 'quote)))
       :rule-classes :forward-chaining))

    (local
     (defthm dummy-lemma-3
       (implies (and (rp-termp x)
                     (case-match x
                       (('falist ('quote &) &) t)))
                (falist-consistent-aux (cadr (cadr x))
                                       (caddr x)))
       :hints (("goal"
                :expand ((rp-termp x))
                :in-theory (e/d (rp-termp falist-consistent)
                                ())))))

    (local
     (defthm rp-evlt-of-falist
       (implies (and (rp-termp x)
                     (equal (car x) 'falist))
                (equal (rp-evlt x a)
                       (rp-evlt (caddr x) a)))
       :hints (("Goal"
                :expand ((RP-TERMP X))
                :in-theory (e/d (rp-termp falist-consistent)
                                ())))))

    (defret <fn>-is-correct
      (and (implies (and (rp::rp-term-listp context)
                         (rp-termp term)
                         (valid-sc term a)
                         (rp::eval-and-all context a)
                         (rp-evl-meta-extract-global-facts)
                         (find-adders-in-svex-formula-checks state))
                    (and (equal (rp-evlt res-term a)
                                (rp-evlt term a))
                         (valid-sc res-term a)))
           (implies (and (rp::rp-term-listp context)
                         (rp-termp term))
                    (rp-termp res-term)))
      :fn rewrite-adders-in-svex-alist
      :hints (("Goal"
               :expand ((rp-termp term)
                        (:free (fn args)
                               (valid-sc (cons fn args) a))
                        (RP-TERM-LISTP (CDR TERM))
                        (RP-TERM-LISTP (CDDR TERM)))
               :in-theory (e/d* (or*
                                 RP-TERM-LISTP
                                 rp-evlt-of-ex-from-rp-reverse
                                 regular-eval-lemmas-with-ex-from-rp
                                 regular-eval-lemmas
                                 ;;is-rp
                                 ;;FALIST-CONSISTENT
                                 ;;is-if
                                 svl::svexl-alist-eval$-correct-reverse)
                                (rp-evlt-of-ex-from-rp
                                 rp-trans-is-term-when-list-is-absent
                                 ex-from-rp
                                 is-rp
                                 RP-EVL-OF-VARIABLE
                                 rp-trans
                                 ;;rp::rp-term-listp
                                 rp::falist-consistent-aux
                                 rp::eval-and-all
                                 valid-sc)))))))

(profile 'rewrite-adders-in-svex-alist)

(rp::add-meta-rule
 :meta-fnc rewrite-adders-in-svex-alist
 :trig-fnc sv::svex-alist-eval
 :formula-checks find-adders-in-svex-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw)
 :disabled t
 :hints (("Goal"
          :in-theory (e/d ()
                          ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection apply$-of-adder-fncs-meta

  (define apply$-of-adder-fncs-meta-aux (args-term)
    :returns (mv (res-args rp-term-listp :hyp (rp-termp args-term))
                 all-bitp
                 valid)
    (case-match args-term
      (('cons x rest)
       (b* ((x-has-bitp (or (has-bitp-rp x)
                            (binary-fnc-p x)
                            (and (quotep x)
                                 (consp (cdr x))
                                 (bitp (unquote x)))))
            ((mv rest bitp valid)
             (apply$-of-adder-fncs-meta-aux rest)))
         (mv (cons x rest)
             (and x-has-bitp bitp)
             valid)))
      (('quote (x . rest))
       (b* ((x-has-bitp (bitp x))
            ((mv rest bitp valid)
             (apply$-of-adder-fncs-meta-aux (list 'quote rest))))
         (mv (cons `',x rest)
             (and x-has-bitp bitp)
             valid)))
      (''nil
       (mv nil t t))
      (& (mv nil nil nil)))
    ///
    (defretd <fn>-is-correct
      (implies valid
               (equal (rp-evlt args-term a)
                      (rp-evlt-lst res-args a))))
    (defret <fn>-is-valid-sc
      (implies (and valid
                    (valid-sc args-term a))
               (valid-sc-subterms res-args a))
      :hints (("Goal"
               :in-theory (e/d (is-rp is-if is-equals) ()))))

    (defret true-listp-of-<fn>
      (true-listp res-args))

    (local
     (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

    (local
     (defthm has-bitp-rp-implies
       (implies (and (has-bitp-rp term)
                     (valid-sc term a))
                (and (bitp (rp-evlt term a))))
       :hints (("goal"

                :in-theory (e/d (valid-sc-single-step
                                 has-bitp-rp
                                 is-rp)
                                (bitp))))))
    (local
     (with-output
       :off :all
       :on (error)
       (progn
         (create-regular-eval-lemma binary-or 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-and 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-xor 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-not 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-? 3 find-adders-in-svex-formula-checks)
         )))

    (local
     (defthm BINARY-FNC-P-implies
       (implies (and (BINARY-FNC-P term)
                     (rp-evl-meta-extract-global-facts)
                     (find-adders-in-svex-formula-checks state))
                (and (bitp (rp-evlt term a))))
       :hints (("goal"

                :in-theory (e/d* (REGULAR-EVAL-LEMMAS
                                  BINARY-FNC-P)
                                 (bitp))))))

    (defret <fn>-is-all-bitp
      (implies (and all-bitp
                    valid
                    (valid-sc args-term a)
                    (rp-evl-meta-extract-global-facts)
                    (find-adders-in-svex-formula-checks state))
               (and (bit-listp (rp-evlt args-term a))
                    (bit-listp (rp-evlt-lst res-args a))))
      :rule-classes (:rewrite :forward-chaining)
      :hints (("Goal"
               :in-theory (e/d (bit-listp
                                is-rp
                                is-if
                                is-equals)
                               ())))))

  ;; (apply$-of-adder-fncs-meta-aux `(cons (rp 'bitp x) (cons '1 (cons (rp 'bitp y) '(1)))))
  ;; = (((RP 'BITP X) '1 (RP 'BITP Y) '1) T T)

  (define apply$-of-adder-fncs-meta (term
                                     (context true-listp))
    :returns (mv (res rp-termp :hyp (rp-termp term)
                      :hints (("Goal"
                               :expand ((:free (rest) (is-rp (cons 'rp rest))))
                               :use ((:instance rp-term-listp-of-apply$-of-adder-fncs-meta-aux.res-args
                                                (args-term (CADR (CADDR TERM)))))
                               :in-theory (e/d (RP-TERM-LISTP)
                                               (rp-term-listp-of-apply$-of-adder-fncs-meta-aux.res-args)))))
                 dont-rw)
    (case-match term
      (('apply$ ('quote fnc) ('svl::4veclist-fix-wog args))
       (b* (((unless (member-equal fnc *adder-fncs*))
             (mv term nil))
            (warrant `(,(intern-in-package-of-symbol
                         (str::cat "APPLY$-WARRANT-" (symbol-name fnc))
                         fnc)))
            ((unless (member-equal warrant context))
             (mv term (raise "A necessary warrant is not found in the context: ~p0 ~%" warrant)))
            ((mv args-lst all-bitp valid)
             (apply$-of-adder-fncs-meta-aux args))
            ((unless valid)
             (mv term (raise "apply$-of-adder-fncs-meta-aux did not return valid. args: ~p0 ~%" args)))

            ((when (and* all-bitp
                         (or* (eq fnc 'ha-c-chain)
                              (eq fnc 'ha-s-chain))
                         (svl::equal-len args-lst 2)))
             (case fnc
               (ha-s-chain
                (mv `(rp 'bitp (equals (s-spec (cons ,(car args-lst)
                                                     (cons ,(cadr args-lst)
                                                           'nil)))
                                       (binary-xor ,(car args-lst)
                                                   ,(cadr args-lst))))
                    `(rp 'bitp (equals (s-spec (cons t (cons t 'nil)))
                                       (binary-xor t t)))))
               (ha-c-chain
                (mv `(rp 'bitp (equals (c-spec (cons ,(car args-lst)
                                                     (cons ,(cadr args-lst)
                                                           'nil)))
                                       (binary-and ,(car args-lst)
                                                   ,(cadr args-lst))))
                    `(rp 'bitp (equals (c-spec (cons t (cons t 'nil)))
                                       (binary-and t t)))))
               (t (mv term nil)))))
         (cond
          ((and* (eq fnc 'fa-c-chain)
                 (svl::equal-len args-lst 4))
           (mv `(,fnc (svl::4vec-fix-wog ,(first args-lst))
                      ,(second args-lst)
                      ,(third args-lst)
                      ,(fourth args-lst))
               `(nil (nil t) t t t)))
          ((and* (eq fnc 'ha+1-s-chain)
                 (svl::equal-len args-lst 3))
           (mv `(,fnc (svl::4vec-fix-wog ,(first args-lst))
                      ,(second args-lst)
                      ,(third args-lst))
               `(nil (nil t) t t)))
          ((and* (or (eq fnc 'fa-s-chain)
                     (eq fnc 'full-adder))
                 (svl::equal-len args-lst 3))
           (mv `(,fnc ,(first args-lst)
                      ,(second args-lst)
                      ,(third args-lst))
               `(nil t t t)))
          ((and* (svl::equal-len args-lst 2)
                 (or (eq fnc 'ha-c-chain)
                     (eq fnc 'ha+1-c-chain)
                     (eq fnc 'ha-s-chain)
                     (eq fnc 'half-adder)))
           (mv `(,fnc ,(first args-lst)
                      ,(second args-lst))
               `(nil t t t)))
          (t (mv term nil)))))
      (& (mv term nil)))

    ///

    (local
     (with-output
       :off :all
       :on (error)
       (progn
         (create-regular-eval-lemma rp 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma c-spec 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma bitp 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma equals 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma cons 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma s-spec 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha-s-chain 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-xor 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma binary-and 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha+1-s-chain 3 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma fa-s-chain 3 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma full-adder 3 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma half-adder 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha+1-c-chain 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma fa-c-chain 4 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma ha-c-chain 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma apply$ 2 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma svl::4veclist-fix-wog 1 find-adders-in-svex-formula-checks)
         (create-regular-eval-lemma svl::4vec-fix-wog 1 find-adders-in-svex-formula-checks))))

    (local
     (defthm rp-evlt-of-quoted
       (implies (and (equal (car x) 'quote))
                (equal (rp-evlt x a)
                       (cadr x)))))

    (local
     (defthm 4vec-bitxor-or-dont-care
       (and (equal (sv::4vec-bitxor '(-1 . 0) x)
                   '(-1 . 0))
            (equal (sv::4vec-bitxor x '(-1 . 0))
                   '(-1 . 0)))
       :hints (("Goal"
                :in-theory (e/d (sv::4vec-bitxor) ())))))

    #|(local
    (defthm 4vec-bitand-or-dont-care
    (and (equal (sv::4vec-bitand '(-1 . 0) x)
    '(-1 . 0))
    (equal (sv::4vec-bitand x '(-1 . 0))
    '(-1 . 0)))
    :hints (("Goal"
    :in-theory (e/d (sv::4vec-bitand) ())))))|#

    ;; (local
    ;;  (defthm rp-evlt-lst-of-cdr
    ;;    (equal (rp-evlt-lst (cdr x) a)
    ;;           (cdr (rp-evlt-lst x a)))))

    (local
     (defthm RP-EVLT-LST-when-atom-and-cddr
       (implies (consp (cdr x))
                (equal (car (rp-evlt-lst (cddr x) a))
                       (rp-evlt (caddr x) a)))))

    (local
     (defthm RP-EVLT-LST-when-atom-and-cdr
       (implies (consp x)
                (equal (car (rp-evlt-lst (cdr x) a))
                       (rp-evlt (cadr x) a)))))

    (local
     (defthm consp-of-rp-evlt-lst
       (equal (consp (rp-evlt-lst lst a))
              (consp lst))
       :hints (("Goal"
                :induct (len lst)
                :in-theory (e/d (rp-trans-lst) ())))))

    (local
     (defthm HA+1-C-CHAIN-of-4vec-fix
       (and (equal (HA+1-C-CHAIN (sv::4vec-fix x) y)
                   (HA+1-C-CHAIN x y))
            (equal (HA+1-C-CHAIN x (sv::4vec-fix y))
                   (HA+1-C-CHAIN x y)))
       :hints (("Goal"
                :in-theory (e/d (HA+1-C-CHAIN) ())))))

    (local
     (defthm HA-C-CHAIN-of-4vec-fix
       (and (equal (HA-C-CHAIN (sv::4vec-fix x) y)
                   (HA-C-CHAIN x y))
            (equal (HA-C-CHAIN x (sv::4vec-fix y))
                   (HA-C-CHAIN x y)))
       :hints (("Goal"
                :in-theory (e/d (HA-C-CHAIN) ())))))

    (local
     (defthm FA-C-CHAIN-of-4vec-fix
       (and (equal (fa-c-chain m (sv::4vec-fix x) y z)
                   (fa-c-chain m x y z))
            (equal (fa-c-chain m x (sv::4vec-fix y) z)
                   (fa-c-chain m x y z))
            (equal (fa-c-chain m x y (sv::4vec-fix z))
                   (fa-c-chain m x y z)))
       :hints (("Goal"
                :in-theory (e/d (fa-c-chain) ())))))

    (local
     (defthm FA-s-CHAIN-of-4vec-fix
       (and (equal (fa-s-chain (sv::4vec-fix x) y z)
                   (fa-s-chain x y z))
            (equal (fa-s-chain x (sv::4vec-fix y) z)
                   (fa-s-chain x y z))
            (equal (fa-s-chain x y (sv::4vec-fix z))
                   (fa-s-chain x y z)))
       :hints (("Goal"
                :in-theory (e/d (fa-s-chain) ())))))

    (local
     (defthm full-adder-of-4vec-fix
       (and (equal (full-adder (sv::4vec-fix x) y z)
                   (full-adder x y z))
            (equal (full-adder x (sv::4vec-fix y) z)
                   (full-adder x y z))
            (equal (full-adder x y (sv::4vec-fix z))
                   (full-adder x y z)))
       :hints (("Goal"
                :in-theory (e/d (full-adder) ())))))

    (local
     (defthm half-adder-of-4vec-fix
       (and (equal (half-adder (sv::4vec-fix x) y)
                   (half-adder x y))
            (equal (half-adder x (sv::4vec-fix y))
                   (half-adder x y)))
       :hints (("Goal"
                :in-theory (e/d (half-adder) ())))))

    (local
     (defthm ha+1-s-CHAIN-of-4vec-fix
       (and (equal (ha+1-s-chain m (sv::4vec-fix x) y)
                   (ha+1-s-chain m x y))
            (equal (ha+1-s-chain m x (sv::4vec-fix y))
                   (ha+1-s-chain m x y)))
       :hints (("Goal"
                :in-theory (e/d (ha+1-s-chain) ())))))

    (local
     (defthm ha-s-CHAIN-of-4vec-fix
       (and (equal (ha-s-chain (sv::4vec-fix x) y)
                   (ha-s-chain x y))
            (equal (ha-s-chain x (sv::4vec-fix y))
                   (ha-s-chain x y)))
       :hints (("Goal"
                :in-theory (e/d (ha-s-chain) ())))))

    (local
     (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

    (local
     (defthm member-equal-and-eval-and-all
       (implies (and (eval-and-all context a)
                     (member-equal x context))
                (and (rp-evlt x a)
                     (implies (force (not (include-fnc x 'list)))
                              (rp-evl x a))))
       :rule-classes (:rewrite)))

    (local
     (defthm valid-sc-of-car-when-valid-sc-subterms
       (implies (and (consp lst)
                     (valid-sc-subterms lst a))
                (valid-sc (car lst) a))))

    (local
     (defthm VALID-SC-SUBTERMS-of-cdr
       (implies (VALID-SC-SUBTERMS lst a)
                (VALID-SC-SUBTERMS (cdr lst) a))))

    (local
     (defthmd s-spec-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (s-spec (list (rp-evlt (car x) a)
                                     (rp-evlt (cadr x) a)))
                       (binary-xor (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (local
     (defthmd ha-c-chain-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (HA-C-CHAIN (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))
                       (binary-and (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (local
     (defthmd ha-s-chain-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (HA-s-CHAIN (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))
                       (binary-xor (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (local
     (defthmd c-spec-when-bit-listp
       (implies (and (svl::equal-len x 2)
                     (bit-listp (rp-evlt-lst x a)))
                (equal (c-spec (list (rp-evlt (car x) a)
                                     (rp-evlt (cadr x) a)))
                       (binary-and (rp-evlt (car x) a)
                                   (rp-evlt (cadr x) a))))
       :hints (("Goal"
                :do-not-induct t
                :in-theory (e/d (BIT-LISTP bitp) ())))))

    (defret <fn>-is-valid-sc
      (and (implies (and (rp::rp-term-listp context)
                         (rp-termp term)
                         (valid-sc term a)
                         (rp-evl-meta-extract-global-facts)
                         (find-adders-in-svex-formula-checks state))
                    (valid-sc res a)))
      :fn apply$-of-adder-fncs-meta
      :hints (("Goal"
               :do-not-induct t
               :expand ((:free (x y a)
                               (eval-and-all (cons x y) a))
                        (:free (x y a)
                               (CONTEXT-FROM-RP (cons 'rp y) a))
                        (:free (x y a)
                               (ex-from-rp (cons 'rp y)))
                        (:free (x y a)
                               (ex-from-rp (cons 'equals y)))
                        (:free (x y a)
                               (CONTEXT-FROM-RP (cons 'equals y) a)))
               :in-theory (e/d* (s-spec-when-bit-listp
                                 c-spec-when-bit-listp
                                 apply$-of-adder-fncs-meta-aux-is-all-bitp
                                 ;;CONTEXT-FROM-RP
                                 regular-eval-lemmas
                                 regular-eval-lemmas-with-ex-from-rp
                                 is-rp is-if is-equals)
                                ((:REWRITE DEFAULT-CDR)
                                 (:REWRITE
                                  RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT)
                                 (:REWRITE
                                  ACL2::SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP)
                                 (:REWRITE VALID-SC-CADR)
                                 (:DEFINITION EX-FROM-RP)
                                 (:DEFINITION MEMBER-EQUAL)
                                 (:REWRITE NTH-0-CONS)
                                 (:REWRITE NTH-ADD1)
                                 len
                                 RP-EVLT-LST-OF-CONS
                                 bit-listp
                                 (:rewrite str::coerce-to-list-removal)
                                 (:rewrite str::coerce-to-string-removal)
                                 (:DEFINITION STR::FAST-STRING-APPEND)
                                 ;;(:DEFINITION RP-TRANS-LST)
                                 (:DEFINITION STRING-APPEND)
                                 ;;rp-trans-lst
                                 rp-trans
                                 rp-termp
                                 eval-and-all
                                 svl::4veclist-fix-wog-is-4veclist-fix
                                 rp-trans)))
              (and stable-under-simplificationp
                   '(:use ((:instance apply$-of-adder-fncs-meta-aux-is-all-bitp
                                      (args-term (cadr (caddr term)))
                                      ))))
              ))

    (defret <fn>-is-correct
      (and (implies (and (rp::rp-term-listp context)
                         (rp-termp term)
                         (valid-sc term ACL2::UNBOUND-FREE-ENV)
                         (rp::eval-and-all context ACL2::UNBOUND-FREE-ENV)
                         (rp-evl-meta-extract-global-facts)
                         (find-adders-in-svex-formula-checks state))
                    (and (equal (rp-evlt res ACL2::UNBOUND-FREE-ENV)
                                (rp-evlt term ACL2::UNBOUND-FREE-ENV))
                         #|(valid-sc res a)|#)))
      :fn apply$-of-adder-fncs-meta
      :hints (("Goal"
               :expand ((:free (x y)
                               (svl::4veclist-fix-wog (cons x y)))
                        (:free (a)
                               (svl::4veclist-fix-wog
                                (rp-evlt-lst
                                 (cddr (mv-nth 0
                                               (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                 a)))
                        (:free (a)(svl::4veclist-fix-wog
                                   (rp-evlt-lst
                                    (cdr (mv-nth 0
                                                 (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                    a)))
                        (:free (a)(svl::4veclist-fix-wog
                                   (cdr
                                    (rp-evlt-lst
                                     (cddr (mv-nth 0
                                                   (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                     a))))
                        (:free (a)
                               (svl::4veclist-fix-wog
                                (rp-evlt-lst
                                 (cdddr (mv-nth 0
                                                (apply$-of-adder-fncs-meta-aux (cadr (caddr term)))))
                                 a))))
               :in-theory (e/d* (s-spec-when-bit-listp
                                 c-spec-when-bit-listp
                                 ha-s-chain-when-bit-listp
                                 ha-c-chain-when-bit-listp
                                 apply$-of-adder-fncs-meta-aux-is-correct
                                 ;;FA-S-CHAIN
                                 ;;HA+1-C-CHAIN
                                 ;;fA-c-CHAIN
                                 regular-eval-lemmas
                                 regular-eval-lemmas-with-ex-from-rp)
                                (rp-evlt-lst-of-cons
                                 (:rewrite str::coerce-to-list-removal)
                                 (:rewrite str::coerce-to-string-removal)
                                 (:definition str::fast-string-append)
                                 ;;(:definition rp-trans-lst)
                                 (:definition string-append)
                                 (:definition valid-sc)
                                 (:definition valid-sc-subterms)
                                 ;;rp-trans-lst

                                 rp-termp
                                 eval-and-all
                                 svl::4veclist-fix-wog-is-4veclist-fix
                                 rp-trans)))
              (and stable-under-simplificationp
                   '(:use ((:instance apply$-of-adder-fncs-meta-aux-is-all-bitp
                                      (args-term (cadr (caddr term)))
                                      (a acl2::unbound-free-env)))))))

    (rp::disable-rules '(svl::4veclist-fix-wog
                         sv::4veclist-fix
                         svl::4veclist-fix-wog-is-4veclist-fix))

    (profile 'apply$-of-adder-fncs-meta)
    )

  (rp::add-meta-rule
   :meta-fnc apply$-of-adder-fncs-meta
   :trig-fnc apply$
   :formula-checks find-adders-in-svex-formula-checks
   :valid-syntaxp t
   :returns (mv term dont-rw)
   :hints (("Goal"
            :in-theory (e/d ()
                            ())))))

#|
(define rewrite-adders-in-svex-alist ((svex-alist sv::Svex-alist-p))
:Returns (res sv::Svex-alist-p :hyp (sv::Svex-alist-p svex-alist))
(b* ((- (cw "Starting: rp::rewrite-adders-in-svex-alist. ~%"))

(- (time-tracker :rewrite-adders-in-svex :end))
(- (time-tracker :rewrite-adders-in-svex :init
:times '(1 2 3 4 5)
:interval 5
))
(- (time-tracker :rewrite-adders-in-svex :start!))

(svex-alist (find-f/h-adders-in-svex-alist svex-alist
*find-f/h-adders-in-svex-alist-limit*
:adder-type 'fa))

;;(svex-alist (find-f/h-adders-in-svex-alist svex-alist (1- *find-f/h-adders-in-svex-alist-limit*)))

(- (cwe "resulting svex-alist after full-adders ~p0 ~%" svex-alist))

(- (time-tracker :rewrite-adders-in-svex :stop))
(- (time-tracker :rewrite-adders-in-svex :print?
:min-time 0
:msg "Search for full adder patterns took ~st secs.~%~%"))

;; ((mv pattern-alist &)
;;  (gather-adder-patterns-in-svex-alist svex-alist nil nil 1))
;; (svex-alist (replace-adder-patterns-in-svex-alist svex-alist pattern-alist 1))

(- (time-tracker :rewrite-adders-in-svex :end))
(- (time-tracker :rewrite-adders-in-svex :init
:times '(1 2 3 4 5)
:interval 5
))
(- (time-tracker :rewrite-adders-in-svex :start!))
;;(- (cw "- Searching for other adders (e.g., half-adder) now.~%"))
;; ((mv pattern-alist &)
;;  (gather-adder-patterns-in-svex-alist svex-alist nil nil 2))
;; (svex-alist (replace-adder-patterns-in-svex-alist svex-alist pattern-alist 2))
(svex-alist (find-f/h-adders-in-svex-alist svex-alist
*find-f/h-adders-in-svex-alist-limit*
:adder-type 'ha))
(- (clear-memoize-table 'replace-adder-patterns-in-svex))
;;(- (fast-alist-free pattern-alist))
(- (time-tracker :rewrite-adders-in-svex :stop))
(- (time-tracker :rewrite-adders-in-svex :print?
:min-time 0
:msg "Search for other adder patterns took ~st secs.~%~%"))

(- (cw "Finished: rp::rewrite-adders-in-svex-alist.~%"))

)
svex-alist)
///
(defret <fn>-is-correct
(implies (and (force (sv::svex-alist-p svex-alist))
(force (warrants-for-adder-pattern-match)))
(equal (sv::svex-alist-eval$ res env)
(sv::svex-alist-eval$ svex-alist env)))
:hints (("Goal"
:in-theory (e/d () ())))))|#

;; (define rewrite-adders-in-svex ((svex sv::Svex-p))
;;   :Returns (res sv::Svex-p :hyp (sv::svex-p svex))
;;   ;; It is easier to manage the simplification algo in one place. So I am using
;;   ;; rewrite-adders-in-svex-alist here as well.
;;   ;; In practice, I don't expect this function to be ever used.
;;   (b* ((svex-alist (acons 'res svex nil))
;;        (svex-alist (rewrite-adders-in-svex-alist svex-alist)))
;;     (if (and (consp svex-alist) (consp (car svex-alist))) ;; for guards
;;         (cdar svex-alist)
;;       svex))
;;   ///
;;   (defret <fn>-is-correct
;;     (implies (and (force (sv::svex-p svex))
;;                   (force (warrants-for-adder-pattern-match)))
;;              (equal (sv::svex-eval$ res env)
;;                     (sv::svex-eval$ svex env)))
;;     :fn rewrite-adders-in-svex
;;     :hints (("Goal"
;;              :Expand ((sv::svex-alist-eval$
;;                        (rewrite-adders-in-svex-alist (list (cons 'res svex)))
;;                        env))
;;              :use ((:instance rewrite-adders-in-svex-alist-is-correct
;;                               (svex-alist (LIST (CONS 'RES SVEX)))))
;;              :in-theory (e/d (sv::svex-alist-eval$
;;                               SV::SVEX-ALIST-EVAL)
;;                              (rewrite-adders-in-svex-alist-is-correct))))))

;; (def-rp-rule trigger-rewrite-adders-in-svex-alist
;;   (implies (and (force (sv::svex-alist-p alist))
;;                 (force (warrants-for-adder-pattern-match))
;;                 (force (sv::svex-alist-no-foreign-op-p alist)))
;;            ;; svex-alist-eval-meta-w/o-svexl should return wrapped with identity
;;            (equal (identity (sv::svex-alist-eval alist env))
;;                   (sv::svex-alist-eval$
;;                    (rewrite-adders-in-svex-alist
;;                     alist)
;;                    env)))
;;   :disabled t ;; should be enabled in the defthmrp-multiplier macro
;;   :hints (("Goal"
;;            ;; :use ((:instance svl::svex-alist-reduce-w/-env-correct
;;            ;;                  (svl::Svex-alist alist)
;;            ;;                  (svl::env nil)
;;            ;;                  (svl::env-term ''nil)))
;;            :in-theory (e/d () ()))))
