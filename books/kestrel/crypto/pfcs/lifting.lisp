; PFCS (Prime Field Constraint System) Library
;
; Copyright (C) 2023 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "PFCS")

(include-book "semantics-shallow")
(include-book "proof-support")

(local (include-book "omap-lib-ext"))

(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/std/system/good-atom-listp" :dir :system))
(local (include-book "kestrel/utilities/nfix" :dir :system))
(local (include-book "std/typed-lists/symbol-listp" :dir :system))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ lifting
  :parents (semantics)
  :short "Lifting from deeply to shallowly embedded semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "The "
    (xdoc::seetopic "semantics-shallowly-embedded"
                    "shallowly embedded semantics")
    " of PFCSes includes an ACL2 function @(tsee sesem-definition)
     to turn a deeply embedded PFCS definition
     into a shallowly embedded PFCS definition.
     The two must and can be related formally:
     the satisfaction of the deeply embedded definition
     is equivalent to the satisfaction of the shallowly embedded one.")
   (xdoc::p
    "Here we explicate this formal relation,
     via ACL2 code that maps a deeply embedded PFCS definition
     not only to a shallowly embedded version of it,
     but also to a theorem that relates the two.
     This is a form of lifting:
     a deeply embedded definition is lifted into a shallowly embedded one.
     The latter is easier to reason about,
     and anything proved about it
     can be extended to the deeply embedded definition
     by using the lifting theorem generated here."))
  :order-subtopics t
  :default-parent lifting)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection lift-rules
  :short "Some rules used by the lifter."
  :long
  (xdoc::topstring
   (xdoc::p
    "The lifter generates proof that make use of
     certain rules about omaps and about some built-ins.
     To avoid a dependency on the libraries that contain those rules,
     here we create versions of these rules that are part of the lifter
     and that are used in proofs generated by the lifter."))

  (defruled lift-rule-omap-in-to-in-of-keys
    (iff (omap::in key map)
         (set::in key (omap::keys map)))
    :by omap::in-to-in-of-keys)

  (defruled lift-rule-omap-consp-of-in-iff-in
    (iff (consp (omap::in key map))
         (omap::in key map))
    :by omap::consp-of-in-iff-in)

  (defruled lift-rule-natp-of-mod
    (implies (and (natp a)
                  (posp b))
             (natp (mod a b))))

  (defruled lift-rule-nfix-when-natp
    (implies (natp x)
             (equal (nfix x) x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define sesem-definition-thm ((def definitionp) (prime symbolp))
  :returns (event pseudo-event-formp)
  :short "Generate theorem connecting deeply and shallowly embedded semantics."
  :long
  (xdoc::topstring
   (xdoc::p
    "Given a PFCS definition,
     @(tsee sesem-definition) generates a shallowly embedded version of it.
     Here we define a theorem connecting that shallowly embedded version
     to the deeply embedded semantics of the definition.")
   (xdoc::p
    "The theorem says that
     the satisfaction of the definition (expressed via @(tsee definition-satp)
     is equivalent to the satisfaction of the shallowly embedded definition.")
   (xdoc::p
    "When the definition has no free variables,
     the theorem is proved by enabling certain definitions and rules.
     The proof is obtained completely by rewriting.")
   (xdoc::p
    "If the definition has free variables,
     the shallowly embedded version of the definition is a @(tsee defun-sk),
     as is @(tsee constraint-relation-satp);
     the latter is what @(tsee definition-satp) gets rewritten to,
     using the rules passed to the proof.
     Both @(tsee defun-sk)s are existentially quantified.
     Essentially, we need to show that each one implies the other,
     using the witness of one to calculate the witness of the other.
     The proof naturally splits into two parts (`only if' and `if').
     Each part if proved mostly by rewriting,
     but we also need some lemma instances.
     The lemma instances for the @('suff') rules of the @(tsee defun-sk)s
     are expected.
     The other instances serve to establish that
     the parameters are not in @('asgfree')
     while the existentially quantified variables are in @('asgfree'):
     we need to leverage the relation between @(tsee omap::in)
     and set membership in @(tsee omap::keys),
     given things are formulated;
     perhaps there is a way to do this via rewrite rules."))

  (b* (((definition def) def)
       (free (definition-free-vars def))
       (thm-name (acl2::packn-pos (list 'definition-satp-of-
                                        def.name
                                        '-to-shallow)
                                  def.name))

       ((when (equal free nil))
        `(defruled ,thm-name
           (implies (and (equal (lookup-definition ',def.name defs)
                                ',def)
                         ,@(sesem-gen-fep-terms def.para prime))
                    (equal (definition-satp
                             ',def.name defs (list ,@def.para) ,prime)
                           (,def.name ,@def.para ,prime)))
           :in-theory '(,def.name
                        (:e ,def.name)
                        definition-satp
                        constraint-satp-of-relation-when-nofreevars
                        constraint-relation-nofreevars-satp
                        constraint-list-satp-of-cons
                        constraint-list-satp-of-nil
                        constraint-satp-of-equal
                        constraint-equal-satp
                        eval-expr
                        eval-expr-list
                        (:e definition->para)
                        (:e definition->body)
                        (:e definition-free-vars)
                        (:e constraint-kind)
                        (:e constraint-equal->left)
                        (:e constraint-equal->right)
                        (:e constraint-relation)
                        (:e constraint-relation->name)
                        (:e constraint-relation->args)
                        (:e expression-kind)
                        (:e expression-const->value)
                        (:e expression-var->name)
                        (:e expression-add->arg1)
                        (:e expression-add->arg2)
                        (:e expression-mul->arg1)
                        (:e expression-mul->arg2)
                        (:e expression-var-list)
                        assignment-wfp-of-update
                        assignment-wfp-of-nil
                        assignment-fix-when-assignmentp
                        assignmentp-of-update
                        (:e assignmentp)
                        omap::from-lists
                        pfield::fep-fw-to-natp
                        pfield::natp-of-add
                        pfield::natp-of-mul
                        len
                        fty::consp-when-reserrp
                        acl2::natp-compound-recognizer
                        (:e nat-listp)
                        (:e set::empty)
                        car-cons
                        cdr-cons
                        omap::in-of-update
                        acl2::nat-listp-of-cons
                        acl2::not-reserrp-when-nat-listp
                        nfix
                        (:t mod))))

       (constraint-relation-satp-witness
        `(constraint-relation-satp-witness ',def.name
                                           ',(expression-var-list def.para)
                                           defs
                                           (omap::from-lists ',def.para
                                                             (list ,@def.para))
                                           ,prime))
       (def-witness `(,(add-suffix-to-fn def.name "-WITNESS")
                      ,@def.para ,prime)))

    `(defruled ,thm-name
       (implies (and (equal (lookup-definition ',def.name defs)
                            ',def)
                     ,@(sesem-gen-fep-terms def.para prime)
                     (posp ,prime))
                (equal (definition-satp
                         ',def.name defs (list ,@def.para) ,prime)
                       (,def.name ,@def.para ,prime)))
       :in-theory '((:t definition-satp)
                    (:t ,def.name))
       :use (only-if-direction if-direction)

       :prep-lemmas

       ((defruled only-if-direction
          (implies (and (equal (lookup-definition ',def.name defs)
                               ',def)
                        ,@(sesem-gen-fep-terms def.para prime))
                   (implies (definition-satp
                              ',def.name defs (list ,@def.para) ,prime)
                            (,def.name ,@def.para ,prime)))
          :in-theory '(definition-satp
                        constraint-satp-of-relation
                        constraint-relation-satp
                        constraint-list-satp-of-cons
                        constraint-list-satp-of-nil
                        constraint-satp-of-equal
                        constraint-equal-satp
                        eval-expr
                        eval-expr-list
                        (:e definition->para)
                        (:e definition->body)
                        (:e definition-free-vars)
                        (:e constraint-kind)
                        (:e constraint-equal->left)
                        (:e constraint-equal->right)
                        (:e constraint-relation)
                        (:e constraint-relation->name)
                        (:e constraint-relation->args)
                        (:e expression-kind)
                        (:e expression-const->value)
                        (:e expression-var->name)
                        (:e expression-add->arg1)
                        (:e expression-add->arg2)
                        (:e expression-mul->arg1)
                        (:e expression-mul->arg2)
                        (:e expression-var-list)
                        assignment-wfp-of-update*
                        assignment-wfp-of-update
                        assignment-wfp-of-nil
                        assignment-fix-when-assignmentp
                        assignmentp-of-update*
                        assignmentp-of-update
                        (:e assignmentp)
                        omap::from-lists
                        pfield::fep-fw-to-natp
                        pfield::natp-of-add
                        pfield::natp-of-mul
                        len
                        fty::consp-when-reserrp
                        acl2::natp-compound-recognizer
                        (:e nat-listp)
                        (:e set::empty)
                        car-cons
                        cdr-cons
                        omap::in-of-update*
                        omap::in-of-update
                        acl2::nat-listp-of-cons
                        acl2::not-reserrp-when-nat-listp
                        lift-rule-nfix-when-natp
                        (:t mod)
                        (:t reserr)
                        fty::reserrp-of-reserr
                        lift-rule-omap-consp-of-in-iff-in
                        (:e set::in)
                        natp-of-cdr-of-in-when-assignmentp-type
                        fep-of-cdr-of-in-when-assignment-wfp)
          :use ((:instance ,(add-suffix-to-fn def.name "-SUFF")
                           ,@(sesem-definition-thm-aux1
                              free constraint-relation-satp-witness))
                ,@(sesem-definition-thm-aux2
                   (append def.para free)
                   constraint-relation-satp-witness)))

        (defruled if-direction
          (implies (and (equal (lookup-definition ',def.name defs)
                               ',def)
                        ,@(sesem-gen-fep-terms def.para prime)
                        (posp ,prime))
                   (implies (,def.name ,@def.para ,prime)
                            (definition-satp
                              ',def.name defs (list ,@def.para) ,prime)))
          :in-theory '(,def.name
                       definition-satp
                       constraint-satp-of-relation
                       constraint-list-satp-of-cons
                       constraint-list-satp-of-nil
                       constraint-satp-of-equal
                       constraint-equal-satp
                       eval-expr
                       eval-expr-list
                       (:e definition->para)
                       (:e definition->body)
                       (:e definition-free-vars)
                       (:e constraint-kind)
                       (:e constraint-equal->left)
                       (:e constraint-equal->right)
                       (:e constraint-relation)
                       (:e constraint-relation->name)
                       (:e constraint-relation->args)
                       (:e expression-kind)
                       (:e expression-const->value)
                       (:e expression-var->name)
                       (:e expression-add->arg1)
                       (:e expression-add->arg2)
                       (:e expression-mul->arg1)
                       (:e expression-mul->arg2)
                       (:e expression-var-list)
                       assignment-wfp-of-update*
                       assignment-wfp-of-update
                       assignment-wfp-of-nil
                       assignment-fix-when-assignmentp
                       assignmentp-of-update*
                       assignmentp-of-update
                       (:e assignmentp)
                       omap::from-lists
                       pfield::fep-fw-to-natp
                       car-cons
                       cdr-cons
                       (:e nat-listp)
                       omap::keys-of-update
                       omap::in-of-update*
                       omap::in-of-update
                       (:e omap::keys)
                       (:e set::insert)
                       len
                       lift-rule-nfix-when-natp
                       (:e reserrp)
                       acl2::not-reserrp-when-natp
                       nat-listp
                       (:e omap::in)
                       lift-rule-natp-of-mod
                       (:e natp))
          :use (:instance constraint-relation-satp-suff
                          (asgfree (omap::from-lists
                                    ',free
                                    (list ,@(sesem-definition-thm-aux3
                                             free def-witness))))
                          (name ',def.name)
                          (args (expression-var-list ',def.para))
                          (asg (omap::from-lists ',def.para
                                                 (list ,@def.para))))))))

  :prepwork

  ((define sesem-definition-thm-aux1 ((free symbol-listp) (witness "A term."))
     :returns (doublets doublet-listp)
     (cond ((endp free) nil)
           (t (cons `(,(car free)
                      (cdr (omap::in ',(car free) ,witness)))
                    (sesem-definition-thm-aux1 (cdr free) witness))))
     :prepwork ((local (in-theory (enable doublet-listp length len)))))

   (define sesem-definition-thm-aux2 ((vars symbol-listp) (witness "A term."))
     :returns (lemma-instances true-listp)
     (cond ((endp vars) nil)
           (t (cons `(:instance lift-rule-omap-in-to-in-of-keys
                                (key ',(car vars))
                                (map ,witness))
                    (sesem-definition-thm-aux2 (cdr vars) witness)))))

   (define sesem-definition-thm-aux3 ((free symbol-listp) (witness "A term."))
     :returns (terms true-listp)
     (cond ((endp free) (raise "Error."))
           ((endp (cdr free)) (list witness))
           (t (sesem-definition-thm-aux3-aux free 0 witness)))
     :prepwork
     ((define sesem-definition-thm-aux3-aux ((free symbol-listp)
                                             (index natp)
                                             (witness "A term."))
        :returns (terms true-listp)
        (cond ((endp free) nil)
              (t (cons `(mv-nth ,index ,witness)
                       (sesem-definition-thm-aux3-aux
                        (cdr free) (1+ index) witness)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define lift-fn ((def definitionp) (prime symbolp))
  :returns (event pseudo-event-formp)
  :short "Lift a deeply embedded PFCS definition
          to a shallowly embedded PFCS definition
          with a theorem relating the two."
  (b* ((event-fn (sesem-definition def prime))
       (event-thm (sesem-definition-thm def prime)))
    `(encapsulate ()
       ,event-fn
       ,event-thm)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(acl2::defmacro+ lift (def &key (prime 'p))
  :short "Macro to lift a deeply embedded PFCS definition
          to a shallowly embedded PFCS definition
          with a theorem relating the two."
  :long
  (xdoc::topstring
   (xdoc::p
    "The required argument must be a ground form
     that evaluates to a PFCS @(tsee definition).
     The form is evaluated and the resulting definition is processed.")
   (xdoc::p
    "The keyword argument must be a symbol
     to use for the prime that parameterizes the PFCS semantics.
     It is @('p') by default.
     This is quoted (not evaluated) for processing."))
  `(make-event (lift-fn ,def ',prime)))
