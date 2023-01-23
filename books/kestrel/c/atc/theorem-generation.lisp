; C Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2022 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "generation-contexts")
(include-book "types-to-recognizers")
(include-book "variable-tables")

(include-book "kestrel/event-macros/event-generation" :dir :system)
(include-book "kestrel/std/system/formals-plus" :dir :system)
(include-book "kestrel/std/system/fresh-logical-name-with-dollars-suffix" :dir :system)
(include-book "kestrel/std/system/untranslate-dollar" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-theorem-generation
  :parents (atc-event-and-code-generation)
  :short "Facilities for generating theorems in ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are for the new approach to proof generation
     in which we generate modular, compositional theorems."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-pure-correct-thm ((fn symbolp)
                                       (fn-guard symbolp)
                                       (context atc-contextp)
                                       (expr exprp)
                                       (type typep)
                                       (term pseudo-termp)
                                       (compst-var symbolp)
                                       (hints true-listp)
                                       (instructions true-listp)
                                       (thm-index posp)
                                       (names-to-avoid symbol-listp)
                                       state)
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (thm-index posp :hyp (posp thm-index))
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate a correctness theorem for a pure expression execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function @('fn') that the expression is part of is passed as input.")
   (xdoc::p
    "As theorem name, we just combine
     @('fn') with @('correct') and with the theorem index.
     The name just needs to be unique locally to the call to ATC,
     so we expect that generally no @('$') signs will need to be added
     by @(tsee fresh-logical-name-with-$s-suffix).")
   (xdoc::p
    "The theorem says that
     @(tsee exec-expr-pure) called on the quoted expression
     is the same as the term;
     it also says that the term has the expression's type.
     The term is untranslated, to make it more readable,
     in particular to eliminate quotes before numbers.
     Term, expression, and type are passed as inputs.
     The theorem is contextualized,
     and further conditioned by the satisfaction of the guard of @('fn').")
   (xdoc::p
    "The hints to prove the theorem are passed as input,
     because they depend on the specifics of the expression."))
  (b* ((wrld (w state))
       (name (pack fn '-correct- thm-index))
       ((mv name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                  name nil names-to-avoid wrld))
       (type-pred (type-to-recognizer type wrld))
       (uterm (untranslate$ term nil state))
       (formula `(and (equal (exec-expr-pure ',expr ,compst-var)
                             ,uterm)
                      (,type-pred ,uterm)))
       (formula (atc-contextualize formula context nil))
       (formula `(implies (and (compustatep ,compst-var)
                               (,fn-guard ,@(formals+ fn wrld)))
                          ,formula))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :instructions instructions
                                            :enable nil)))
    (mv event name (1+ thm-index) names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-expr-bool-correct-thm ((fn symbolp)
                                       (fn-guard symbolp)
                                       (context atc-contextp)
                                       (expr exprp)
                                       (type typep)
                                       (aterm pseudo-termp)
                                       (cterm pseudo-termp)
                                       (compst-var symbolp)
                                       (hints true-listp)
                                       (instructions true-listp)
                                       (thm-index posp)
                                       (names-to-avoid symbol-listp)
                                       state)
  :returns (mv (thm-event pseudo-event-formp)
               (thm-name symbolp)
               (thm-index posp :hyp (posp thm-index))
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate a correctness theorem for a boolean expression execution."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee atc-gen-expr-pure-correct-thm),
     but with some important differences.")
   (xdoc::p
    "The ACL2 term from which the C expression is generated is boolean-valued,
     so the execution of the expression cannot be equal to the term.
     Instead, there must be another ACL2 term,
     whose value is (the ACL2 model of) a C value,
     that the expression execution is equated to in the theorem.
     The two terms are
     @('aterm') (for `ACL2 term') and @('cterm') (for `C term'),
     both passed as parameters to this ACL2 function
     (unlike a single @('term') in @(tsee atc-gen-expr-pure-correct-thm)).
     The two terms and their relation are slightly different
     for different kinds of boolean expression terms;
     see the callers of this ACL2 function for details.")
   (xdoc::p
    "While @(tsee atc-gen-expr-pure-correct-thm) generates a theorem
     whose conclusion consists of two conjuncts,
     namely the equation with the expression execution
     and the type predicate applied to the term,
     here we generate four conjuncts.
     The first two are similar to @(tsee atc-gen-expr-pure-correct-thm),
     but we use @('cterm') for that purpose, as explained above.
     The other two conjuncts refer to @('aterm') instead:
     they say that @(tsee test-value) applied to @('cterm') yields @('aterm'),
     and that @('aterm') is a boolean.")
   (xdoc::p
    "The reason for the form of this theorem is that
     the symbolic execution rules have separate binding hypotheses
     for executing the expression and for applying @(tsee test-value):
     for example, see the @('exec-expr-pure-when-cond') rule
     in @(see atc-exec-expr-pure-rules)."))
  (b* ((wrld (w state))
       (name (pack fn '-correct- thm-index))
       ((mv name names-to-avoid) (fresh-logical-name-with-$s-suffix
                                  name nil names-to-avoid wrld))
       (type-pred (type-to-recognizer type wrld))
       (uaterm (untranslate$ aterm nil state))
       (ucterm (untranslate$ cterm nil state))
       (formula `(and (equal (exec-expr-pure ',expr ,compst-var)
                             ,ucterm)
                      (,type-pred ,ucterm)
                      (equal (test-value ,ucterm)
                             ,uaterm)
                      (booleanp ,uaterm)))
       (formula (atc-contextualize formula context nil))
       (formula `(implies (and (compustatep ,compst-var)
                               (,fn-guard ,@(formals+ fn wrld)))
                          ,formula))
       ((mv event &) (evmac-generate-defthm name
                                            :formula formula
                                            :hints hints
                                            :instructions instructions
                                            :enable nil)))
    (mv event name (1+ thm-index) names-to-avoid)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atc-gen-enter-inscope ((fn symbolp)
                               (fn-guard symbolp)
                               (inscope atc-symbol-varinfo-alist-listp)
                               (context atc-contextp)
                               (compst-var symbolp)
                               (thm-index posp)
                               (names-to-avoid symbol-listp)
                               (wrld plist-worldp))
  :returns (mv (new-inscope atc-symbol-varinfo-alist-listp
                            :hyp (atc-symbol-varinfo-alist-listp inscope))
               (new-context atc-contextp :hyp (atc-contextp context))
               (events pseudo-event-form-listp)
               (thm-index posp :hyp (posp thm-index))
               (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
  :short "Generate an updated symbol table according to entering a new scope."
  :long
  (xdoc::topstring
   (xdoc::p
    "The initial symbol table is generated by @(tsee atc-gen-init-inscope);
     see the documentation of that function.
     When we enter a new scope (via @(tsee enter-scope)),
     we generate an updated symbol table that not only has an additional scope,
     but also has new theorems associated to the existing scopes.
     These new theorems say that reading each variable name yields the variable
     in the computation state updated to enter the scope.
     We also return a new context, updated with the new computation state.")
   (xdoc::p
    "Each new theorem is proved from the old theorem,
     using the rule that reduces @(tsee read-var) of @(tsee enter-scope)
     to just @(tsee read-var).
     The hypothesis of that rule saying that there are frames
     is discharged via the rules in
     @(see atc-compustate-frames-number-rules):
     the computation state that @(tsee enter-scope) is applied to
     always starts with @(tsee add-frame)
     or @(tsee enter-scope)
     or @(tsee add-var);
     there may be other forms possible, which we will handle later."))
  (b* ((premise (make-atc-premise-compustate :var compst-var
                                             :term `(enter-scope ,compst-var)))
       (context (append context (list premise)))
       ((mv new-inscope events names-to-avoid)
        (atc-gen-enter-inscope-aux fn fn-guard inscope context compst-var
                                   thm-index names-to-avoid wrld)))
    (mv (cons nil new-inscope)
        context
        events
        (1+ thm-index)
        names-to-avoid))

  :prepwork
  ((define atc-gen-enter-inscope-aux ((fn symbolp)
                                      (fn-guard symbolp)
                                      (inscope atc-symbol-varinfo-alist-listp)
                                      (context atc-contextp)
                                      (compst-var symbolp)
                                      (thm-index posp)
                                      (names-to-avoid symbol-listp)
                                      (wrld plist-worldp))
     :returns (mv (new-inscope atc-symbol-varinfo-alist-listp
                               :hyp (atc-symbol-varinfo-alist-listp inscope))
                  (events pseudo-event-form-listp)
                  (names-to-avoid symbol-listp :hyp (symbol-listp names-to-avoid)))
     :parents nil
     (b* (((when (endp inscope)) (mv nil nil names-to-avoid))
          (scope (car inscope))
          ((mv new-scope events names-to-avoid)
           (atc-gen-enter-inscope-aux-aux fn fn-guard scope context compst-var
                                          thm-index names-to-avoid wrld))
          (scopes (cdr inscope))
          ((mv new-scopes more-events names-to-avoid)
           (atc-gen-enter-inscope-aux fn fn-guard scopes context compst-var
                                      thm-index names-to-avoid wrld)))
       (mv (cons new-scope new-scopes)
           (append events more-events)
           names-to-avoid))

     :prepwork
     ((define atc-gen-enter-inscope-aux-aux ((fn symbolp)
                                             (fn-guard symbolp)
                                             (scope atc-symbol-varinfo-alistp)
                                             (context atc-contextp)
                                             (compst-var symbolp)
                                             (thm-index posp)
                                             (names-to-avoid symbol-listp)
                                             (wrld plist-worldp))
        :returns (mv (new-scope atc-symbol-varinfo-alistp
                                :hyp (atc-symbol-varinfo-alistp scope))
                     (events pseudo-event-form-listp)
                     (names-to-avoid symbol-listp
                                     :hyp (symbol-listp names-to-avoid)))
        :parents nil
        (b* (((when (endp scope)) (mv nil nil names-to-avoid))
             ((cons var info) (car scope))
             (type (atc-var-info->type info))
             (thm (atc-var-info->thm info))
             (type-pred (type-to-recognizer type wrld))
             (new-thm (pack fn '- var '-in-scope- thm-index))
             ((mv new-thm names-to-avoid)
              (fresh-logical-name-with-$s-suffix new-thm nil names-to-avoid wrld))
             (formula `(and (equal (read-var (ident ,(symbol-name var))
                                             ,compst-var)
                                   ,var)
                            (,type-pred ,var)))
             (formula (atc-contextualize formula context nil))
             (formula `(implies (and (compustatep ,compst-var)
                                     (,fn-guard ,@(formals+ fn wrld)))
                                ,formula))
             (hints `(("Goal"
                       :in-theory
                       '(,thm
                         read-var-of-enter-scope
                         compustate-frames-number-of-add-frame-not-zero
                         compustate-frames-number-of-enter-scope-not-zero
                         compustate-frames-number-of-add-var-not-zero))))
             ((mv event &) (evmac-generate-defthm new-thm
                                                  :formula formula
                                                  :hints hints
                                                  :enable nil))
             (new-info (change-atc-var-info info :thm new-thm))
             (rest (cdr scope))
             ((mv new-rest events names-to-avoid)
              (atc-gen-enter-inscope-aux-aux fn fn-guard rest context compst-var
                                             thm-index names-to-avoid wrld)))
          (mv (acons var new-info new-rest)
              (cons event events)
              names-to-avoid))
        :prepwork
        ((local
          (in-theory (enable alistp-when-atc-symbol-varinfo-alistp-rewrite))))
        :verify-guards :after-returns)))))
