; C Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2020 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "abstract-syntax")
(include-book "portable-ascii-identifiers")
(include-book "function-environments")

(include-book "kestrel/fty/sbyte32" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atc-static-semantics
  :parents (atc-implementation)
  :short "A static semantics of C for ATC."
  :long
  (xdoc::topstring
   (xdoc::p
    "In order to support the generation of proofs for
     the C code generated by ATC,
     we need a static semantics (as well as a dynamic semantics)
     of (the needed portion of) C.
     The static semantics serves to prove that
     the generated C code compiles.
     Here we provide an initial formal static semantics,
     which should support the generation of proofs
     for an initial version of ATC.")
   (xdoc::p
    "This preliminary static semantics may be extended in the future,
     and may be replaced by a more comprehensive model
     that we will be developing as part of the "
    (xdoc::seetopic "language" "language formalization")
    ".")
   (xdoc::p
    "The static semantics is defined over the C abstract syntax,
     but for now it rejects many valid constructs
     just because ATC does not generate those constructs for now.
     This way, we keep the static semantics simpler.
     Being more restrictive is adequate here:
     if a program generated by ATC passes the constraints
     of this excessively strict static semantics,
     it is a valid C program,
     regardless of the fact that many valid C programs (not generated by ATC)
     are rejected by this static semantics.")
   (xdoc::p
    "This static semantics uses the notion of `well-formed'
     to describe abstract syntactic entities
     that satisfy the constraints of the static semantics."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::deflist var-symtab
  :short "Fixtype of symbol tables of variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This keeps track of all the variables in scope [C18:6.2.1],
     organized according to block scopes.
     The list has one element for each nested block,
     where the first element (the @(tsee car)), if present,
     corresponds to the innermost block:
     this order is natural, as blocks are added via @(tsee cons).
     The list is never empty:
     we always initialize the symbol table one (empty) block.")
   (xdoc::p
    "Each element of the sequence is just a set of variable names for now,
     because currently all the variables have type @('int').
     Note that currently we do not support variables with file scope.")
   (xdoc::p
    "Using sets is adequate because the variables declared in a block
     must all have different names [C18:6.2.1/2].
     However, it is possible for two sets in the list not to be disjoint,
     when a variable in an inner block hides one in an outer block
     [C18:6.2.1/4]."))
  :elt-type ident-set
  :true-listp t
  :non-emptyp t
  :elementp-of-nil t
  :pred var-symtabp
  ///

  (defrule var-symtabp-of-cons-alt
    (iff (var-symtabp (cons a x))
         (and (ident-setp a)
              (or (var-symtabp x)
                  (eq x nil))))
    :enable var-symtabp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-symtab-lookup ((var identp) (symtab var-symtabp))
  :returns (yes/no booleanp)
  :short "Look up a variable in a symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we just return a boolean,
     indicating whether the variable is found or not.
     We search for it in the sequence in order,
     i.e. from innermost to outermost block.
     This will be important when we extend variable symbol tables
     with information about the variables (particularly, types),
     because a variable reference refers to the one in the innermost block,
     when there are others."))
  (and (mbt (not (endp symtab)))
       (or (set::in (ident-fix var) (ident-set-fix (car symtab)))
           (and (not (endp (cdr symtab)))
                (var-symtab-lookup var (cdr symtab)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-symtab-init ()
  :returns (symtab var-symtabp)
  :short "Create an initial variable symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "This contains a single block with no variables."))
  (list nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-symtab-add-block ((symtab var-symtabp))
  :returns (new-symtab var-symtabp)
  :short "Add a block scope to a variable symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "We add the empty set (of variables)
     to the front of the sequence.
     This is used when a block is entered."))
  (cons nil (var-symtab-fix symtab))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define var-symtab-add-var ((var identp) (symtab var-symtabp))
  :returns (mv (okp booleanp) (new-symtab var-symtabp))
  :short "Add a variable to (the innermost block of) a variable symbol table."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the block already has a variable with that name,
     it is an error: we return @('nil') as first result.
     Otherwise, we add the variable and return the symbol table,
     along with @('t') as first result."))
  (b* ((var (ident-fix var))
       (symtab (var-symtab-fix symtab))
       (block (ident-set-fix (car symtab)))
       ((when (set::in var block)) (mv nil symtab))
       (new-block (set::insert var block)))
    (mv t (cons new-block (cdr symtab))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod senv
  :short "Fixtype of static environments."
  :long
  (xdoc::topstring
   (xdoc::p
    "A static environment consists of
     a function environment
     and a variables symbol table.")
   (xdoc::p
    "The function environment consists of
     information about the functions in scope.
     As defined later, we build the function environment
     as we traverse the tranlation unit."))
  ((functions fun-env)
   (variables var-symtab))
  :pred senvp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define irr-senv ()
  :returns (env senvp)
  :short "An irrelevant static environment, usable as a dummy return value."
  (with-guard-checking :none (ec-call (senv-fix :irrelevant)))
  ///
  (in-theory (disable (:e irr-senv))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ident-wfp ((id identp))
  :returns (yes/no booleanp)
  :short "Check if an identifier is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check whether the underlying ACL2 string satisfies the conditions
     described in Section `C identifiers' of @(tsee atc).
     As noted there, C18 allows a possibly broader range of valid identifiers,
     but ATC only generates this kind of portable identifiers."))
  (atc-ident-stringp (ident->name id))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define iconst-wfp ((ic iconstp))
  :returns (yes/no booleanp)
  :short "Check if an integer constant is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we require the integer constant
     to be decimal (not octal or hexadecimal),
     to be signed,
     and to have no type suffixes.
     This means that the integer constant must have type @('int'),
     and therefore that its numberic value must in that type's range.
     Given our current definition of @(tsee sintp),
     the value must fit in 32 bits (with the sign bit being 0)."))
  (b* (((iconst ic) ic))
    (and (acl2::sbyte32p ic.value)
         (equal ic.base (iconst-base-dec))
         (not ic.unsignedp)
         (equal ic.type (iconst-tysuffix-none))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define const-wfp ((c constp))
  :returns (yes/no booleanp)
  :short "Check if a constant is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only accept well-formed integer constants.
     The other kinds of constants are placeholders in our abstract syntax,
     anyhow."))
  (const-case c
              :int (iconst-wfp c.get)
              :float nil
              :enum nil
              :char nil)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define unop-wfp ((op unopp))
  :returns (yes/no booleanp)
  :short "Check if a unary operator is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "In C they are all well-formed of course,
     but having this predicate lets us limit the supported ones if desired.
     Currently we support all the ones in the abstract syntax."))
  (and (member-eq (unop-kind op) '(:plus :minus :bitnot :lognot)) t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define binop-wfp ((op binopp))
  :returns (yes/no booleanp)
  :short "Check if a binary operator is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "In C they are all well-formed of course,
     but having this predicate lets us limit the supported ones if desired.
     Currently we support
     all the non-side-effecting ones in the abstract syntax
     (i.e. not the assignment operators."))
  (and (member-eq (binop-kind op) '(:mul :div :rem
                                    :add :sub
                                    :shl :shr
                                    :lt :gt :le :ge
                                    :eq :ne
                                    :bitand :bitxor :bitior
                                    :logand :logor))
       t)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyspecseq-wfp ((tss tyspecseqp))
  :returns (yes/no booleanp)
  :short "Check if a sequence of type specifiers is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "In C they are all well-formed of course,
     but for now we only allow the one for @('int')."))
  (tyspecseq-case tss :sint)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define tyname-wfp ((tn tynamep))
  :returns (yes/no booleanp)
  :short "Check if a type name is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "We check that the underlying sequence of type specifiers is well-formed."))
  (tyspecseq-wfp (tyname->specs tn))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines expr-wfp
  :short "Check if an expression is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only allow
     (well-formed) identifiers in scope,
     (well-formed) constants,
     unary expressions with well-formed operators and operands,
     and binary expressions with well-formed operators and operands.
     We disallow
     function calls,
     pre/post-increment/decrement,
     casts,
     and ternary (i.e. conditional) expressions.")
   (xdoc::p
    "Normally a static semantics would also return a type for each expression,
     but for now all our expressions have type @('int'),
     so there is no need to return this."))

  (define expr-wfp ((e exprp) (env senvp))
    :returns (yes/no booleanp)
    (expr-case e
               :ident (and (ident-wfp e.get)
                           (var-symtab-lookup e.get (senv->variables env)))
               :const (const-wfp e.get)
               :call (b* ((info (fun-env-lookup e.fun (senv->functions env))))
                       (and info
                            (= (len (fun-info->params info))
                               (len e.args))))
               :postinc nil
               :postdec nil
               :preinc nil
               :predec nil
               :unary (and (unop-wfp e.op)
                           (expr-wfp e.arg env))
               :cast nil
               :binary (and (binop-wfp e.op)
                            (expr-wfp e.arg1 env)
                            (expr-wfp e.arg2 env))
               :cond (and (expr-wfp e.test env)
                          (expr-wfp e.then env)
                          (expr-wfp e.else env)))
    :measure (expr-count e))

  (define expr-list-wfp ((es expr-listp) (env senvp))
    :returns (yes/no booleanp)
    (or (endp es)
        (and (expr-wfp (car es) env)
             (expr-list-wfp (cdr es) env)))
    :measure (expr-list-count es))

  ///

  (fty::deffixequiv-mutual expr-wfp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines stmt-wfp
  :short "Check if a statement is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only allow
     @('return') statements with expressions,
     conditional statements, and
     compound statements.")
   (xdoc::p
    "The ACL2 function that processes a block item returns,
     besides an indication of success or failure,
     also a possibly updated static environment.
     The update happens when the block item is a declaration:
     this way, subsequent block items can access the declared variable.")
   (xdoc::p
    "For a compound statement,
     we add a block scope to the variable symbol table
     and then we process the list of block items.
     There is no need to explicitly remove it when exiting the block,
     because we only use the extended variable symbol table
     to check the well-formedness of the items of the block.
     Anything that follows the block is checked
     with the variable symbol table prior to the extension.
     In fact, a compound statement does not update the static environment."))

  (define stmt-wfp ((s stmtp) (env senvp))
    :returns (yes/no booleanp)
    (stmt-case
     s
     :labeled nil
     :compound (b* ((var-symtab (senv->variables env))
                    (ext-var-symtab (var-symtab-add-block var-symtab))
                    (ext-env (change-senv env :variables ext-var-symtab)))
                 (block-item-list-wfp s.items ext-env))
     :expr nil
     :null nil
     :if (and (expr-wfp s.test env)
              (stmt-wfp s.then env))
     :ifelse (and (expr-wfp s.test env)
                  (stmt-wfp s.then env)
                  (stmt-wfp s.else env))
     :switch nil
     :while nil
     :dowhile nil
     :for nil
     :goto nil
     :continue nil
     :break nil
     :return (and s.value
                  (expr-wfp s.value env)))
    :measure (stmt-count s))

  (define block-item-wfp ((item block-itemp) (env senvp))
    :returns (mv (yes/no booleanp) (new-env senvp))
    (block-item-case
     item
     :decl (b* (((decl decl) item.get)
                ((unless (and (tyspecseq-wfp decl.type)
                              (ident-wfp decl.name)
                              (expr-wfp decl.init env)))
                 (mv nil (senv-fix env)))
                (var-symtab (senv->variables env))
                ((mv okp new-var-symtab)
                 (var-symtab-add-var decl.name var-symtab))
                ((when (not okp)) (mv nil (senv-fix env)))
                (new-env (change-senv env :variables new-var-symtab)))
             (mv t new-env))
     :stmt (mv (stmt-wfp item.get env) (senv-fix env)))
    :measure (block-item-count item))

  (define block-item-list-wfp ((items block-item-listp) (env senvp))
    :returns (yes/no booleanp)
    (or (endp items)
        (b* (((mv okp env) (block-item-wfp (car items) env))
             ((when (not okp)) nil))
          (block-item-list-wfp (cdr items) env)))
    :measure (block-item-list-count items))

  :verify-guards nil ; done below
  ///
  (verify-guards stmt-wfp)

  (fty::deffixequiv-mutual stmt-wfp))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-decl-wfp ((param param-declp) (env senvp))
  :returns (mv (yes/no booleanp)
               (new-env senvp))
  :short "Check if a parameter declaration is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "The static environment passed as input is the one
     engendered by the parameter declarations that precede this one.
     We ensure that the components of the parameter declaration are well-formed
     and that the parameter can be added to the variable symbol table;
     the latter check fails if there is a duplicate parameter.
     If all checks succeed, we return the static environment
     updated with the parameter."))
  (b* (((param-decl param) param)
       ((unless (tyspecseq-wfp param.type)) (mv nil (irr-senv)))
       ((unless (ident-wfp param.name)) (mv nil (irr-senv)))
       (var-symtab (senv->variables env))
       ((mv okp new-var-symtab) (var-symtab-add-var param.name var-symtab))
       ((when (not okp)) (mv nil (irr-senv))))
    (mv t (change-senv env :variables new-var-symtab)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define param-decl-list-wfp ((params param-decl-listp) (env senvp))
  :returns (mv (yes/no booleanp)
               (new-env senvp))
  :short "Check if a list of parameter declaration is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "We go through each element of the list,
     calling @(tsee param-decl-wfp) and threading the environment through."))
  (b* (((when (endp params)) (mv t (senv-fix env)))
       ((mv okp env) (param-decl-wfp (car params) env))
       ((when (not okp)) (mv nil env)))
    (param-decl-list-wfp (cdr params) env))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fundef-wfp ((fundef fundefp) (fenv fun-envp))
  :returns (mv (yes/no booleanp)
               (new-fenv fun-envp))
  :short "Check if a function definition is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting with an empty variable environment,
     we process the parameter declarations and obtain the environment
     in which the function body must be statically well-formed.
     If a function with the same name is already in the environment,
     it is an error: there is a duplicate function name.
     Otherwise, we return the function environment
     updated with the function definition.")
   (xdoc::p
    "The scope of a function identifier goes from its declaration
     to the end of the translation unit [C:6.2.1/4].
     Thus, as we go through
     the function definitions in the translation unit in order,
     we extend the function environment."))
  (b* (((fundef fundef) fundef)
       ((unless (tyspecseq-wfp fundef.result)) (mv nil (irr-fun-env)))
       ((unless (ident-wfp fundef.name)) (mv nil (irr-fun-env)))
       (env (make-senv :functions fenv :variables (var-symtab-init)))
       ((mv okp env) (param-decl-list-wfp fundef.params env))
       ((when (not okp)) (mv nil (irr-fun-env)))
       ((unless (stmt-wfp fundef.body env)) (mv nil (irr-fun-env)))
       (fenv (fun-env-extend fundef fenv)))
    (fun-env-result-case
     fenv
     :err (mv nil nil)
     :ok (mv t fenv.get)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ext-decl-wfp ((ext ext-declp) (fenv fun-envp))
  :returns (mv (yes/no booleanp)
               (new-fenv fun-envp))
  :short "Check if an external declaration is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "For now we only allow well-formed function definitions."))
  (ext-decl-case ext
                 :fundef (fundef-wfp ext.get fenv)
                 :decl (mv nil (irr-fun-env)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define ext-decl-list-wfp ((exts ext-decl-listp) (fenv fun-envp))
  :returns (mv (yes/no booleanp)
               (new-fenv fun-envp))
  :short "Check if a list of external declarations are well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "We thread the function environment through."))
  (b* (((when (endp exts)) (mv t (fun-env-fix fenv)))
       ((mv okp fenv) (ext-decl-wfp (car exts) fenv))
       ((unless okp) (mv nil (irr-fun-env))))
    (ext-decl-list-wfp (cdr exts) fenv))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define transunit-wfp ((tunit transunitp))
  :returns (yes/no booleanp)
  :short "Check if a translation unit is well-formed."
  :long
  (xdoc::topstring
   (xdoc::p
    "Starting from the empty environment,
     we check all the external declarations,
     threading the environment through,
     and discarding the final one (it served its pupose)."))
  (b* (((transunit tunit) tunit)
       (fenv nil)
       ((mv okp &) (ext-decl-list-wfp tunit.decls fenv)))
    okp)
  :hooks (:fix))
