; Java Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JAVA")

(include-book "name-translation")
(include-book "types")

(include-book "kestrel/std/system/all-free-bound-vars" :dir :system)
(include-book "kestrel/std/system/all-vars-open" :dir :system)
(include-book "kestrel/std/system/dumb-occur-var-open" :dir :system)
(include-book "kestrel/std/system/mvify" :dir :system)
(include-book "kestrel/std/system/remove-dead-if-branches" :dir :system)
(include-book "kestrel/std/system/remove-mbe" :dir :system)
(include-book "kestrel/std/system/remove-progn" :dir :system)
(include-book "kestrel/std/system/remove-trivial-vars" :dir :system)
(include-book "kestrel/std/system/remove-unused-vars" :dir :system)
(include-book "kestrel/std/system/unquote-term" :dir :system)
(include-book "std/alists/remove-assocs" :dir :system)
(include-book "std/strings/symbols" :dir :system)
(include-book "std/typed-alists/symbol-pos-alistp" :dir :system)
(include-book "std/typed-alists/symbol-symbol-alistp" :dir :system)

(local (include-book "std/typed-lists/pseudo-term-listp" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation
  :parents (atj-code-generation)
  :short "Pre-translation performed by ATJ, as part of code generation."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned "
    (xdoc::seetopic "atj-code-generation" "here")
    ", prior to generating Java code,
     ATJ performs an ACL2-to-ACL2 pre-translation.
     Currently, this pre-translation consists of the following steps.
     The first three steps apply to both the deep and the shallow embedding;
     the others apply only to the shallow embedding.")
   (xdoc::ol
    (xdoc::li
     "We remove @(tsee return-last).
      See "
     (xdoc::seetopic "atj-pre-translation-remove-last" "here")
     ".")
    (xdoc::li
     "We remove dead @(tsee if) branches.
      See "
     (xdoc::seetopic "atj-pre-translation-remove-dead-if-branches" "here")
     ".")
    (xdoc::li
     "We remove the unused lambda-bound variables.
      See "
     (xdoc::seetopic "atj-pre-translation-unused-vars" "here")
     ".")
    (xdoc::li
     "We remove the trivial lambda-bound variables.
      See "
     (xdoc::seetopic "atj-pre-translation-trivial-vars" "here")
     ".")
    (xdoc::li
     "We replace @(tsee list) calls with @(tsee mv) calls
      in functions that return multiple results.
      See "
     (xdoc::seetopic "atj-pre-translation-multiple-values" "here")
     ".")
    (xdoc::li
     "We annotate terms with ATJ type information.
      See "
     (xdoc::seetopic "atj-pre-translation-type-annotation" "here")
     ".")
    (xdoc::li
     "We mark the lambda-bound variables
      that can be reused and destructively updated in Java.
      See "
     (xdoc::seetopic "atj-pre-translation-var-reuse" "here")
     ".")
    (xdoc::li
     "We rename variables
      so that their names are valid Java variable names
      and so that different variables with the same name are renamed apart,
      unless they have been marked for reuse in the previous step.
      See "
     (xdoc::seetopic "atj-pre-translation-var-renaming" "here")
     ".")))
  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-remove-last
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of @(tsee return-last)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in both the deep and shallow embedding approach.")
   (xdoc::p
    "We selectively remove the @(':logic') or @(':exec') parts of @(tsee mbe)s
     (which are translated to @('(return-last 'mbe1-raw <exec> <logic>)'))
     based on the @(':guards') input.
     We remove all the non-last arguments of @(tsee prog2$)s and @(tsee progn$)s
     (which are translated to @('(return-last 'progn <non-last> <last>)')).")
   (xdoc::p
    "These are the only @(tsee return-last) forms
     that make it through input validation.
     Note that the non-last arguments of @(tsee prog2$) and @(tsee progn$)
     are checked to be free of side effects by ATJ,
     and thus their removal is safe and semantics-preserving."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-remove-return-last ((term pseudo-termp) (guards$ booleanp))
  :returns (new-term pseudo-termp :hyp (pseudo-termp term))
  :short "Remove all the @(tsee return-last)s from a term."
  (b* ((term (if guards$
                 (remove-mbe-logic term)
               (remove-mbe-exec term)))
       (term (remove-progn term)))
    term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc atj-pre-translation-remove-dead-if-branches
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of dead @(tsee if) branches."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in both the deep and shallow embedding approach.")
   (xdoc::p
    "If the test of an @(tsee if) is @('t'),
     we replace the @(tsee if) with the `then' branch;
     if the test of an @(tsee if) is @('nil'),
     we replace the @(tsee if) with the `else' branch.
     Note that the previous translation step
     may turn @(tsee mbt)s in @(tsee if) tests into @('t')s,
     so it is appropriate for this pre-translation step
     to come after the previous one.")
   (xdoc::p
    "We use the @(tsee remove-dead-if-branches) system utility.
     No other code is needed to do this in ATJ.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-unused-vars
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of all the unused lambda-bound variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done in both the deep and shallow embedding approach.")
   (xdoc::p
    "We remove all the lambda-bound variables,
     and corresponding actual arguments,
     that are not actually used in the body of the lambda expression.
     This way, we avoid calculating and assigning actual arguments
     that are then discarded.
     Recall that ATJ checks that the ACL2 code to be translated to Java
     is free of side effects:
     thus, this removal is safe and semantics-preserving.")
   (xdoc::p
    "This is accomplished
     via the @(tsee remove-unused-vars) system utility.
     No other code is needed to do this in ATJ.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-trivial-vars
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          removal of all the trivial lambda-bound variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "We remove all the lambda-bound variables,
     and corresponding actual arguments,
     that are identical to the corresponding actual arguments.
     See the discussion in @(tsee remove-trivial-vars),
     which is the utility that we use
     to accomplish this pre-translation step.")
   (xdoc::p
    "This pre-translation step makes terms simpler to work with
     (for the purpose of ATJ)
     by only keeping the ``true'' @(tsee let)s in a term
     (which are lambda expressions in translated terms),
     avoiding the ``artificial'' ones to close the lambda expressions.
     Indeed, @(tsee let) terms are generally not closed in other languages,
     or even in ACL2's untranslated terms.")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-multiple-values
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          replacement of @(tsee list) calls with @(tsee mv) calls
          in functions that return multiple results."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "As explained in @(tsee mvify),
     when terms that return multiple values,
     such as the bodies of functions that return multiple results,
     are "
    (xdoc::seetopic "acl2::term" "translated")
    " by ACL2 in internal form,
     the fact that they return multiple values is ``lost'':
     the macro @(tsee mv) expands to @(tsee list).
     The @(tsee mvify) utility can be used to ``recover'' this information,
     by replacing calls of @(tsee list)
     (which in internal form are
     nests of @(tsee cons)es ending with quoted @('nil')s)
     with calls of @(tsee mv).")
   (xdoc::p
    "This is what this ATJ pre-translation step does.
     This is only done in the bodies of functions that return multiple results;
     the bodies of the other functions are left unchanged."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-restore-mv-terms ((body pseudo-termp) (out-types atj-type-listp))
  :returns (new-body pseudo-termp :hyp (pseudo-termp body))
  :short "Replace @(tsee list) calls with @(tsee mv) calls
          in the body of a function that returns multiple results."
  :long
  (xdoc::topstring
   (xdoc::p
    "Whether the function in question returns multiple results
     is determined by the length of the list of output types.")
   (xdoc::p
    "The replacement is done only at the ``leaves'' of the body,
     where `leaf' is defined in the documentation of @(tsee mvify)."))
  (if (>= (len out-types) 2)
      (mvify body)
    body))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-type-annotation
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          addition of type annotations."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "This step annotates ACL2 terms with ATJ types:
     (i) each ACL2 term is wrapped with a function named @('[src>dst]'),
     where @('src') identifies the ATJ type of the term
     and @('dst') identifies an ATJ type to which the term must be converted to;
     (ii) each ACL2 variable @('var') in a term is renamed to @('[type]var'),
     where @('type') identifies the ATJ type of the variable.")
   (xdoc::p
    "More precisely,
     both @('src') and @('dst') above identify non-empty lists of ATJ types.
     This is because an ACL2 term may return multiple values (see @(tsee mv)):
     each list consists of two or more ATJ types when he ACL2 term does;
     otherwise, it consists of one type ATJ type only.
     The two lists (for @('src') and @('dst')) will always have the same length,
     because ACL2 prevents treating
     single values as multiple values,
     multiple values as single values,
     or multiple values of a certain number
     as multiple values of a different number.
     Non-executable functions relax these restrictions,
     but their body includes calls of @('acl2::throw-nonexec-error'),
     which has raw Lisp code and is currently not whitelisted by ATJ.")
   (xdoc::p
    "These annotations facilitate the ACL2-to-Java translation,
     which uses the type annotations as ``instructions'' for
     (i) which types to declare Java local variables with, and
     (ii) which Java conversion code to insert around expressions.")
   (xdoc::p
    "The annotated terms are still ACL2 terms (with a specific structure).
     This should let us prove, in ACL2,
     the equality of the annotated terms with the original terms,
     under suitable variable rebinding,
     and by introducing the @('[src>dst]') functions as identities.
     (This has not been done yet.)"))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-id ((type atj-typep))
  :returns (id stringp)
  :short "Short string identifying an ATJ type."
  :long
  (xdoc::topstring
   (xdoc::p
    "We use a short two-letter string to identify each ATJ type.
     For the ATJ types that correspond to AIJ's public classes,
     the first letter is @('A') and the second letter is from the class name.
     For the Java primitive types,
     the first letter is @('J') and the second letter is from [JVMS:4.3.2].
     For the Java primitive array types,
     the first letter is @('Y') (which is the ending letter of `array')
     and the second letter is from [JVMS:4.3.2]."))
  (case type
    (:ainteger "AI")
    (:arational "AR")
    (:anumber "AN")
    (:acharacter "AC")
    (:astring "AS")
    (:asymbol "AY")
    (:acons "AP")
    (:avalue "AV")
    (:jboolean "JZ")
    (:jchar "JC")
    (:jbyte "JB")
    (:jshort "JS")
    (:jint "JI")
    (:jlong "JJ")
    (:jboolean[] "YZ")
    (:jchar[] "YC")
    (:jbyte[] "YB")
    (:jshort[] "YS")
    (:jint[] "YI")
    (:jlong[] "YJ")
    (otherwise (prog2$ (impossible) "")))
  ///

  (defrule atj-type-id-injective
    (implies (and (atj-typep x)
                  (atj-typep y))
             (equal (equal (atj-type-id x)
                           (atj-type-id y))
                    (equal x y)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-of-id ((id stringp))
  :returns (type atj-typep)
  :short "ATJ type identified by a short string."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-type-id).")
  (cond ((equal id "AI") :ainteger)
        ((equal id "AR") :arational)
        ((equal id "AN") :anumber)
        ((equal id "AC") :acharacter)
        ((equal id "AS") :astring)
        ((equal id "AY") :asymbol)
        ((equal id "AP") :acons)
        ((equal id "AV") :avalue)
        ((equal id "JZ") :jboolean)
        ((equal id "JC") :jchar)
        ((equal id "JB") :jbyte)
        ((equal id "JS") :jshort)
        ((equal id "JI") :jint)
        ((equal id "JJ") :jlong)
        ((equal id "YZ") :jboolean[])
        ((equal id "YC") :jchar[])
        ((equal id "YB") :jbyte[])
        ((equal id "YS") :jshort[])
        ((equal id "YI") :jint[])
        ((equal id "YJ") :jlong[])
        (t (prog2$
            (raise "Internal error: ~x0 does not identify a type." id)
            :avalue))) ; irrelevant
  ///

  (defrule atj-type-of-id-of-atj-type-id
    (implies (atj-typep x)
             (equal (atj-type-of-id (atj-type-id x))
                    x))
    :enable atj-type-id))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-id ((types atj-type-listp))
  :guard (consp types)
  :returns (id stringp)
  :short "String identifying a non-empty list of ATJ types."
  :long
  (xdoc::topstring-p
   "We concatenate the short strings returned by @(tsee atj-type-id).")
  (atj-types-id-aux types)

  :prepwork
  ((define atj-types-id-aux ((types atj-type-listp))
     :returns (id stringp :hyp :guard)
     (cond ((endp types) "")
           (t (str::cat (atj-type-id (car types))
                        (atj-types-id-aux (cdr types))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-of-id ((id stringp))
  :returns (types atj-type-listp)
  :short "Non-empty list of ATJ types identified by
          a concatenation of short strings."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-types-id).")
  (b* ((types (atj-types-of-id-aux (explode id) id)))
    (if (consp types)
        types
      (prog2$
       (raise "Internal error: ~x0 identifies an empty list of types." id)
       (list :avalue)))) ; just so that result is always CONSP

  :prepwork
  ((define atj-types-of-id-aux ((chars character-listp) (id stringp))
     :returns (types atj-type-listp)
     (b* (((when (endp chars)) nil)
          ((unless (>= (len chars) 2))
           (raise "Internal error: ~x0 does not identify a list of types." id))
          (first-id (implode (list (first chars) (second chars))))
          (first-type (atj-type-of-id first-id))
          (rest-types (atj-types-of-id-aux (cddr chars) id)))
       (cons first-type rest-types))))

  ///

  (more-returns
   (types consp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-conv ((src-types atj-type-listp) (dst-types atj-type-listp))
  :guard (and (consp src-types)
              (consp dst-types))
  :returns (name symbolp)
  :short "ATJ type conversion function names used to annotate ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned "
    (xdoc::seetopic "atj-pre-translation-type-annotation" "here")
    ", each ACL2 term is wrapped with a function named @('[src>dst]'),
     where @('src') identifies the ATJ types of the term
     and @('dst') identifies an ATJ types
     to which the term must be converted to.")
   (xdoc::p
    "These function names are all in the @('\"JAVA\"') package.
     For now we do not need these functions to actually exist in the ACL2 world,
     because annotated terms are only created ephemerally as data
     manipulated by the ATJ code generation functions.
     However, in order to prove that the type annotation process
     preserves the ACL2 meaning of terms,
     these functions will need to exist and be defined as identify functions,
     which can be easily done with a macro when that becomes important."))
  (intern$ (str::cat "["
                     (atj-types-id src-types)
                     ">"
                     (atj-types-id dst-types)
                     "]")
           "JAVA"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-types-of-conv ((conv symbolp))
  :returns (mv (src-types atj-type-listp)
               (dst-types atj-type-listp))
  :short "Source and destination ATJ types of a conversion function."
  :long
  (xdoc::topstring-p
   "This is the inverse of @(tsee atj-type-conv).")
  (b* ((string (symbol-name conv))
       ((unless (and (> (length string) 0)
                     (eql (char string 0) #\[)
                     (eql (char string (1- (length string))) #\])))
        (raise "Internal error: ~x0 is not a conversion function." conv)
        (mv (list :avalue) (list :avalue))) ; irrelevant
       (pos (position #\> string))
       ((unless (natp pos))
        (raise "Internal error: ~x0 is not a conversion function." conv)
        (mv (list :avalue) (list :avalue))) ; irrelevant
       (src-id (subseq string 1 pos))
       (dst-id (subseq string (1+ pos) (1- (length string))))
       (src-types (atj-types-of-id src-id))
       (dst-types (atj-types-of-id dst-id)))
    (mv src-types dst-types))
  :guard-hints (("Goal"
                 :use ((:instance acl2::nth-of-index-when-member
                        (k #\>) (x (explode (symbol-name conv)))))
                 :in-theory (disable acl2::nth-of-index-when-member)))
  :prepwork ((local (include-book "std/lists/index-of" :dir :system)))
  ///

  (more-returns
   (src-types consp :rule-classes :type-prescription)
   (dst-types consp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-wrap-term ((term pseudo-termp)
                            (src-types atj-type-listp)
                            (dst-types? atj-type-listp))
  :guard (consp src-types)
  :returns (wrapped-term pseudo-termp)
  :short "Wrap an ACL2 term with a type conversion function."
  :long
  (xdoc::topstring
   (xdoc::p
    "The conversion is from the source types to the destination types.
     If the destination types are the empty list,
     they are treated as if they were equal to the source types,
     i.e. the conversion is a no-op."))
  (b* (((unless (mbt (pseudo-termp term))) nil)
       (conv (if dst-types?
                 (atj-type-conv src-types dst-types?)
               (atj-type-conv src-types src-types))))
    (fcons-term* conv term)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unwrap-term ((term pseudo-termp))
  :returns (mv (unwrapped-term pseudo-termp)
               (src-types atj-type-listp)
               (dst-types atj-type-listp))
  :short "Unwrap an ACL2 term wrapped by @(tsee atj-type-wrap-term)."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is essentially the inverse function,
     except that it always returns a list of destination types,
     never @('nil')."))
  (b* ((term (if (mbt (pseudo-termp term)) term nil))
       ((when (or (variablep term)
                  (fquotep term)
                  (flambda-applicationp term)))
        (raise "Internal error: the term ~x0 has the wrong format." term)
        (mv nil (list :avalue) (list :avalue))) ; irrelevant
       (fn (ffn-symb term))
       ((when (flambdap fn))
        (raise "Internal error: the term ~x0 has the wrong format." term)
        (mv nil (list :avalue) (list :avalue))) ; irrelevant
       ((mv src-types dst-types) (atj-types-of-conv fn)))
    (mv (fargn term 1) src-types dst-types))
  ///

  (more-returns
   (src-types consp :rule-classes :type-prescription)
   (dst-types consp :rule-classes :type-prescription))

  (defret acl2-count-of-atj-type-unwrap-term-linear
    (implies unwrapped-term
             (< (acl2-count unwrapped-term)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-rewrap-term ((term pseudo-termp)
                              (src-types atj-type-listp)
                              (dst-types? atj-type-listp))
  :guard (consp src-types)
  :returns (rewrapped-term pseudo-termp
                           :hints (("Goal" :expand ((pseudo-termp term)))))
  :short "Re-wrap an ACL2 term with a type conversion function."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is used when annotating @(tsee if) terms,
     in the shallow embedding approach.
     These terms are initially wrapped with a type conversion function,
     but in general may need to be wrapped with a different one.
     So here we replace the wrapper.
     See @(tsee atj-type-annotate-term) for details."))
  (b* (((when (or (variablep term)
                  (fquotep term)
                  (not (consp (fargs term)))))
        (raise "Internal error: the term ~x0 has the wrong format." term)))
    (atj-type-wrap-term (fargn term 1) src-types dst-types?))
  :guard-hints (("Goal" :expand ((pseudo-termp term)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-rewrap-terms ((terms pseudo-term-listp)
                               (src-typess atj-type-list-listp)
                               (dst-types?s atj-type-list-listp))
  :guard (and (acl2::cons-listp src-typess)
              (= (len terms) (len src-typess))
              (= (len terms) (len dst-types?s)))
  :returns (rewrapped-terms pseudo-term-listp)
  :short "Lift @(tsee atj-type-rewrap-term) to lists."
  (cond ((endp terms) nil)
        (t (cons (atj-type-rewrap-term (car terms)
                                       (car src-typess)
                                       (car dst-types?s))
                 (atj-type-rewrap-terms (cdr terms)
                                        (cdr src-typess)
                                        (cdr dst-types?s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-var ((var symbolp) (types atj-type-listp))
  :guard (consp types)
  :returns (annotated-var symbolp)
  :short "Annotate an ACL2 variable with a non-empty list of types."
  :long
  (xdoc::topstring
   (xdoc::p
    "As mentioned "
    (xdoc::seetopic "atj-pre-translation-type-annotation" "here")
    ", we systematically add type information to each ACL2 variable.
     We do so by adding @('[types]') before the variable name,
     where @('types') identifies a list of ATJ types."))
  (packn-pos (list "[" (atj-types-id types) "]" var) var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unannotate-var ((var symbolp))
  :returns (mv (unannotated-var symbolp)
               (types atj-type-listp))
  :short "Decompose an annotated ACL2 variable into
          its unannotated counterpart and its types."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse of @(tsee atj-type-annotate-var)."))
  (b* ((string (symbol-name var))
       ((unless (and (> (length string) 0)
                     (eql (char string 0) #\[)))
        (raise "Internal error: ~x0 is not an annotated variable." var)
        (mv nil (list :avalue))) ; irrelevant
       (pos (position #\] string))
       ((unless (natp pos))
        (raise "Internal error: ~x0 is not an annotated variable." var)
        (mv nil (list :avalue))) ; irrelevant
       (types-id (subseq string 1 pos))
       (types (atj-types-of-id types-id))
       (unannotated-string (subseq string (1+ pos) (length string)))
       (unannotated-var (intern-in-package-of-symbol unannotated-string var)))
    (mv unannotated-var types))
  :guard-hints (("Goal"
                 :use ((:instance acl2::nth-of-index-when-member
                        (k #\]) (x (explode (symbol-name var)))))
                 :in-theory (disable acl2::nth-of-index-when-member)))
  :prepwork ((local (include-book "std/lists/index-of" :dir :system)))
  ///

  (more-returns
   (types consp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-vars ((vars symbol-listp)
                                (types atj-type-listp))
  :guard (int= (len vars) (len types))
  :returns (new-vars symbol-listp)
  :short "Annotate each of a list of ACL2 variable
          with a corresponding singleton list of types."
  (cond ((endp vars) nil)
        (t (cons (atj-type-annotate-var (car vars) (list (car types)))
                 (atj-type-annotate-vars (cdr vars) (cdr types)))))
  ///

  (defret len-of-atj-type-annotate-vars
    (equal (len new-vars)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-unannotate-vars ((vars symbol-listp))
  :returns (unannotated-vars symbol-listp)
  :short "Remove the type annotations from a list of variables."
  :long
  (xdoc::topstring-p
   "The annotating types are discarded.")
  (b* (((when (endp vars)) nil)
       ((mv var &) (atj-type-unannotate-var (car vars)))
       (vars (atj-type-unannotate-vars (cdr vars))))
    (cons var vars))
  ///

  (defret len-of-atj-type-unannotate-vars
    (equal (len unannotated-vars)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-check-mv-let-call ((term pseudo-termp))
  :returns (mv (yes/no booleanp)
               (indices nat-listp)
               (vars symbol-listp)
               (mv-term pseudo-termp)
               (body-term pseudo-termp))
  :short "Check if a term is a (translated) call of @(tsee mv-let)
          with some possibly missing @(tsee mv-nth) calls."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is similar to @(tsee acl2::check-mv-let-call),
     except that it allows some of the @(tsee mv-nth) calls to be missing.
     Initially a translated @(tsee mv-let) has all those calls,
     but ATJ's pre-translation step that removes unused variables
     may remove some of them.
     Thus, we cannot use @(tsee acl2::check-mv-let-call) here,
     and instead create a custom version here
     (which may be moved to a more general library at some point,
     since it is not really ATJ-specific).
     This version also returns the indices of the @(tsee mv-nth) calls
     that are present, in increasing order
     (if they appear in a different order,
     this function returns @('nil') as first result)."))
  (b* ((term (if (mbt (pseudo-termp term)) term nil))
       ((when (variablep term)) (mv nil nil nil nil nil))
       ((when (fquotep term)) (mv nil nil nil nil nil))
       (lambda-mv (ffn-symb term))
       ((unless (flambdap lambda-mv)) (mv nil nil nil nil nil))
       (list-mv (lambda-formals lambda-mv))
       ((unless (equal list-mv (list 'mv))) (mv nil nil nil nil nil))
       (mv-term (fargn term 1))
       (lambda-vars-of-mv-nths (lambda-body lambda-mv))
       ((when (variablep lambda-vars-of-mv-nths)) (mv nil nil nil nil nil))
       ((when (fquotep lambda-vars-of-mv-nths)) (mv nil nil nil nil nil))
       (lambda-vars (ffn-symb lambda-vars-of-mv-nths))
       ((unless (flambdap lambda-vars)) (mv nil nil nil nil nil))
       (vars (lambda-formals lambda-vars))
       (body-term (lambda-body lambda-vars))
       ((when (dumb-occur-var-open 'mv body-term)) (mv nil nil nil nil nil))
       (mv-nths (fargs lambda-vars-of-mv-nths))
       ((mv mv-nths-okp indices) (atj-check-mv-let-call-aux mv-nths 0))
       ((unless mv-nths-okp) (mv nil nil nil nil nil)))
    (mv t indices vars mv-term body-term))

  :prepwork
  ((define atj-check-mv-let-call-aux ((terms pseudo-term-listp)
                                      (min-next-index natp))
     :returns (mv (yes/no booleanp)
                  (indices nat-listp))
     (b* (((when (endp terms)) (mv t nil))
          (term (car terms))
          ((unless (and (ffn-symb-p term 'mv-nth)
                        (= (len (fargs term)) 2))) (mv nil nil))
          ((unless (quotep (fargn term 1))) (mv nil nil))
          (index (cadr (fargn term 1)))
          ((unless (and (natp index)
                        (>= index min-next-index))) (mv nil nil))
          ((unless (eq (fargn term 2) 'mv)) (mv nil nil))
          ((mv rest-okp rest-indices)
           (atj-check-mv-let-call-aux (cdr terms) (1+ index)))
          ((unless rest-okp) (mv nil nil)))
       (mv t (cons index rest-indices)))
     ///
     (defret len-of-atj-check-mv-let-call-aux.indices
       (implies yes/no
                (equal (len indices)
                       (len terms))))))

  ///

  (defret len-of-atj-check-mv-let-call.indices/vars
    (implies yes/no
             (equal (len indices)
                    (len vars)))
    :hyp :guard)

  (defret atj-check-mv-let-call-mv-term-smaller
    (implies yes/no
             (< (acl2-count mv-term)
                (acl2-count term)))
    :rule-classes :linear)

  (defret atj-check-mv-let-call-body-term-smaller
    (implies yes/no
             (< (acl2-count body-term)
                (acl2-count term)))
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-type-annotate-term
  :short "Add ATJ type annotations to ACL2 terms."
  :long
  (xdoc::topstring
   (xdoc::p
    "The type annotation procedure involves inferring the types of terms,
     and wrapping terms with type conversion functions
     to match certain type requirements.")
   (xdoc::p
    "The @('var-types') input assigns types to (at least)
     all the free variables in the term that is being annotated.
     At the top level (see @(tsee atj-type-annotate-formals+body)),
     @('var-types') is initialized with the formal parameters of a function
     and with its corresponding input types.
     When we encounter a lambda expression in a term,
     @('var-types') is updated with an alist that assigns
     to the formal parameters of the lambda expression
     the types inferred for the actual arguments of the lambda expression;
     that is, unlike at the top level, at intermediate levels
     variables receive the types inferred for their binding terms.
     Here `updated' means that
     the new alist is appended before the existing one:
     recall that, due to the pre-translation step
     that removes trivial lambda-bound variables,
     lambda expressions may not be closed at this point;
     thus, the appending achieves the desired ``overwriting''.")
   (xdoc::p
    "Even though variables can be annotated by multiple types in general
     (see @(tsee atj-type-annotate-var)),
     @('var-types') assigns single types to variables.
     The only variables annotated with lists of two or more types
     are the @('mv') vars that arise in the translation of @(tsee mv-let)
     (see @(tsee atj-check-mv-let-call)).
     These @('mv') variables are treated specially
     by the type annotation process,
     without a need to add them to @('var-types').")
   (xdoc::p
    "The @('required-types?') input specifies
     the type(s) required for the term, if any.
     This is @('nil') if there are no requirements;
     it is a singleton list if the term is to be single-valued;
     it is a list of two or more types if the term is to be multi-valued.
     At the top level (see @(tsee atj-type-annotate-formals+body)),
     @('required-types?') consists of the output type(s) of the function
     (singleton if single-valued, of length two or more if multi-valued):
     the body of the function must have the output type(s) of the function.
     The recursive function @('atj-type-annotate-args'),
     that operates on the arguments of a function call,
     does not take a list of required types as input;
     if it did, it would be always consist of @('nil')s,
     so we simply avoid it.")
   (xdoc::p
    "The result of annotating a term is not only the annotated term,
     but also the type(s) of the wrapped term.
     This is always the same as the required types
     when there are required types;
     when there are no required types,
     the resulting type(s) is/are the one(s) inferred for the term.")
   (xdoc::p
    "The type inferred for a variable is the one assigned by @('var-types').
     (As already mentioned before,
     the @('mv') variables annotated with two or more types
     are handled specially;
     they are never to this function directly.)
     We annotate the variable with its type;
     note that the variable names in @('var-types')
     do not have type annotations.
     We wrap the variable with a type conversion function
     from the inferred type(s) to the required type(s) if supplied,
     or to the inferred type(s) (i.e. no-op conversion) if not supplied.")
   (xdoc::p
    "The type inferred for a quoted constant
     is determined by the value of the quoted constant.
     We wrap the quoted constant with a type conversion function
     as discussed above.")
   (xdoc::p
    "The non-strict function @(tsee if) is treated specially,
     because eventually it is translated to a Java @('if'),
     which assigns either the `then' part or the `else' part
     to a Java local variable.
     The type of the Java local variable is
     (the Java counterpart of) @('required-types?') if supplied:
     in this case, when @('required-types?') is recursively passed
     to the second and third argument of the @(tsee if),
     both terms will be wrapped so that they have the required type(s).
     However, if @('required-types?') is @('nil'),
     the recursive annotation of the `then' and `else' subterms
     may produce different types,
     and so in this case we re-wrap those terms
     with the least upper bound of the two types.
     The case of a term of the form @('(if a a b)')
     is treated a little differently,
     but there is no substantial difference.
     In the general case of @('(if a b c)') with @('a') different from @('b'),
     there is never any required type for the test @('a'),
     because in the Java code it is just used
     to generate the test of the @('if');
     ACL2 should ensure that the test of an @(tsee if) is single-valued,
     but we defensively check for that.
     In all cases, the @(tsee if) is wrapped with
     the identify conversion function for the overall type(s),
     for uniformity and to readily indicate the type
     of the Java local variable to generate.")
   (xdoc::p
    "For a lambda expression
     (other than the kind resulting from an @(tsee mv-let),
     whose treatment is described below),
     the argument terms are annotated without required types.
     The inferred types are then assigned to the formal parameters
     when the body of the lambda expression is annotated.
     We annotate all the formal parameters of the lambda expression;
     but note that the new @('var-types') has non-annotated variable names.
     Note that the list of types returned by @(tsee atj-type-annotate-args)
     has a different meaning from
     the one returned by @(tsee atj-type-annotate-term):
     while the latter is a single or multiple type for a single term,
     the latter consists of a single type for each argument
     (more on this below).")
   (xdoc::p
    "For a named function call other than @(tsee mv)
     (whose treatment is described below),
     the function's types are obtained.
     We first try annotating the argument terms without required types
     (as done for a lambda expression as explained above),
     thus inferring types for the arguments.
     Then we look for the function types (of the named function)
     whose input types are wider than or the same as
     the inferred argument types.
     If there are some, we select the one whose input types are the least
     (this always exists because of the closure property
     checked by @(tsee def-atj-other-function-type);
     see the documentation of that macro and supporting functions for details);
     we then use the output type(s) of the selected function type
     as the type(s) inferred for the function call,
     and wrap it to adapt to the required type(s) for the function call if any.
     The successful selection of such a function type means that,
     in the generated Java code, an overloaded method will be called
     based on the argument types inferred by the Java compiler.
     If there are no function types satisfying the above condition,
     we look at the primary function type (which always exists),
     and its input types become the required ones for the argument terms,
     while the output type(s) are used to infer the type(s) for the call,
     which is then wrapped as needed to match the required type(s) if any.")
   (xdoc::p
    "If we encounter a call of @(tsee mv),
     which may be introduced by a previous pre-translation step,
     we allow its arguments to have any types
     and we regard the call as having the multiple type obtained
     by putting the argument types into a list.")
   (xdoc::p
    "Before attempting to process lambda expression or named function calls
     as described above,
     we first check whether the term is a translated @(tsee mv-let).
     For this to be the case,
     not only @(tsee atj-check-mv-let-call) must succeed,
     yielding variables @('var1'), ..., @('varn')
     and subterms @('mv-term') and @('body-term'),
     but also the term assigned to the @('mv') variable
     must have multiple types.
     If the term is not a translated @(tsee mv-let),
     the term is processed as any other term.
     If the term is a translated @(tsee mv-let),
     we annotate it by building a term of the form")
   (xdoc::codeblock
    "([reqinf>reqinf]"
    " ((lambda ([types]mv)"
    "          ([reqinf>reqinf]"
    "           ((lambda ([type1]var1 ... [typen]varn)"
    "                    ([...>reqinf] body-term))"
    "            ([AV>type1] (mv-nth ([AI>AI] '0)"
    "                                ([types>types] [types]mv)))"
    "            ..."
    "            ([AV>typen] (mv-nth ([AI>AI] 'n-1)"
    "                                ([types>types] [types]mv))))))"
    "  ([types>types] mv-term)))")
   (xdoc::p
    "where @('types') consists of @('type1'), ..., @('typen'),
     and where @('reqinf') is @('required-types?') if non-@('nil')
     or otherwise the types inferred for @('body-term').
     This term is systematically annotated in the same way as any other term,
     so that subsequent pre-processing steps can treat all terms uniformly.
     The @('[AV>typei]') conversions
     are consistent with the function type of @(tsee mv-nth),
     so that, as we are adding more direct support for @(tsee mv) in ATJ,
     the code generation functions can still treat these newly annotated terms
     as before, i.e. treating multiple values as lists.")
   (xdoc::p
    "The function @('atj-type-annotate-mv-let') first checks whether the term
     has the structure of a translated @(tsee mv-let).
     Then it annotates the term to which the @('mv') variable is bound,
     inferring a non-empty list of types (i.e. @('types') above) for it:
     if the list is a singleton,
     the term is actually not a translated @(tsee mv-let),
     and the function returns a failure,
     letting @('atj-type-annotate-term') handle the term.
     Otherwise, after checking that the number of types
     is consistent with the number of variables
     (this is never expected to fail),
     we annotate the body term:
     we pass the top-level required types (if any),
     and we update @('var-types') with the @(tsee mv-let) variables
     associated to the types for the term to which @('mv') is bound;
     we do not need to update @('var-types') with @('mv')
     because @(tsee atj-check-mv-let-call) ensures that
     the variable @('mv') does not occur free in the body term.
     Note that, in general, some variables bound to @(tsee mv-nth) calls
     may have been removed by a previous pre-translation step,
     the one that removes unused variables (see @(tsee atj-check-mv-let-call));
     thus, in order to extend @('var-types'),
     we select the types for which there are actually variables.")
   (xdoc::p
    "In @('atj-type-annotate-args'), we check that
     the types inferred for each single argument are a singleton.
     Except for the argument of @('((lambda (mv) ...) mv-term)')
     in a translated @(tsee mv-let),
     in ACL2 all the arguments of function calls must be single-valued.
     We do not expect this check to ever fail.")
   (xdoc::p
    "Note that an annotated term is still a regular term,
     but it has a certain structure."))

  (define atj-type-annotate-term ((term pseudo-termp)
                                  (required-types? atj-type-listp)
                                  (var-types atj-symbol-type-alistp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :returns (mv (annotated-term pseudo-termp)
                 (resulting-types atj-type-listp))
    (b* (((unless (mbt (pseudo-termp term)))
          (mv nil (list :avalue)))
         ((unless (mbt (atj-type-listp required-types?)))
          (mv nil (list :avalue)))
         ((unless (mbt (atj-symbol-type-alistp var-types)))
          (mv nil (list :avalue)))
         ((when (variablep term))
          (b* ((var term)
               (var+type (assoc-eq var var-types))
               ((unless (consp var+type))
                (prog2$
                 (raise "Internal error: the variable ~x0 has no type." term)
                 (mv nil (list :avalue)))) ; irrelevant
               (type (cdr var+type))
               (types (list type))
               (var (atj-type-annotate-var var types))
               ((unless (<= (len required-types?) 1))
                (raise "Internal error: ~
                        requiring multiple types ~x0 ~
                        for a single-type variable ~x1."
                       required-types? var)
                (mv nil (list :avalue)))) ; irrelevant
            (mv (atj-type-wrap-term var types required-types?)
                (or required-types? types))))
         ((when (fquotep term))
          (b* ((value (unquote-term term))
               (type (atj-type-of-value value))
               (types (list type))
               ((unless (<= (len required-types?) 1))
                (raise "Internal error: ~
                        requiring multiple types ~x0 ~
                        for a quoted constant ~x1."
                       required-types? term)
                (mv nil (list :avalue)))) ; irrelevant
            (mv (atj-type-wrap-term term types required-types?)
                (or required-types? types))))
         ((mv successp annotated-term resulting-types)
          (atj-type-annotate-mv-let
           term required-types? var-types guards$ wrld))
         ((when successp) (mv annotated-term resulting-types))
         (fn (ffn-symb term))
         ((when (and (eq fn 'if)
                     (int= (len (fargs term)) 3))) ; should be always true
          (b* ((test (fargn term 1))
               (then (fargn term 2))
               (else (fargn term 3)))
            (if (equal test then) ; it's an OR
                (b* ((first test)
                     (second else)
                     ((unless (<= (len required-types?) 1))
                      (raise "Internal error: ~
                              requiring multiple types ~x0 ~
                              for the term ~x1."
                             required-types? term)
                      (mv nil (list :avalue))) ; irrelevant
                     ((mv first first-types)
                      (atj-type-annotate-term first
                                              required-types?
                                              var-types
                                              guards$
                                              wrld))
                     ((unless (= (len first-types) 1))
                      (raise "Internal error: ~
                              the first disjunct ~x0 of the term ~x1 ~
                              returns multiple values."
                             first term)
                      (mv nil (list :avalue))) ; irrelevant
                     ((mv second second-types)
                      (atj-type-annotate-term second
                                              required-types?
                                              var-types
                                              guards$
                                              wrld))
                     ((unless (= (len second-types) 1))
                      (raise "Internal error: ~
                              the second disjunct ~x0 of the term ~x1 ~
                              returns multiple values."
                             second term)
                      (mv nil (list :avalue))) ; irrelevant
                     (types (or required-types?
                                (atj-type-list-join first-types second-types)))
                     (first (if required-types?
                                first
                              (atj-type-rewrap-term first
                                                    first-types
                                                    types)))
                     (second (if required-types?
                                 second
                               (atj-type-rewrap-term second
                                                     second-types
                                                     types)))
                     (term (fcons-term* 'if first first second)))
                  (mv (atj-type-wrap-term term types types)
                      types))
              (b* (((mv test test-types) (atj-type-annotate-term test
                                                                 nil
                                                                 var-types
                                                                 guards$
                                                                 wrld))
                   ((unless (= (len test-types) 1))
                    (raise "Internal error: ~
                            the test ~x0 of the term ~x1 ~
                            returns multiple values."
                           test term)
                    (mv nil (list :avalue))) ; irrelevant
                   ((mv then then-types)
                    (atj-type-annotate-term then
                                            required-types?
                                            var-types
                                            guards$
                                            wrld))
                   ((mv else else-types)
                    (atj-type-annotate-term else
                                            required-types?
                                            var-types
                                            guards$
                                            wrld))
                   ((unless (= (len then-types) (len else-types)))
                    (raise "Internal error: ~
                            the branches ~x0 and ~x1 of the term ~x2 ~
                            have different numbers of types, ~
                            namely ~x3 and ~x4."
                           then else term then-types else-types)
                    (mv nil (list :avalue))) ; irrelevant
                   ((unless (or (null required-types?)
                                (= (len required-types?) (len then-types))))
                    (raise "Internal error: ~
                            requiring the types ~x0 for the term ~x1, ~
                            which has a different number of types ~x2."
                           required-types? term (len then-types))
                    (mv nil (list :avalue))) ; irrelevant
                   (types (or required-types?
                              (atj-type-list-join then-types else-types)))
                   (then (if required-types?
                             then
                           (atj-type-rewrap-term then
                                                 then-types
                                                 types)))
                   (else (if required-types?
                             else
                           (atj-type-rewrap-term else
                                                 else-types
                                                 types)))
                   (term (fcons-term* 'if test then else)))
                (mv (atj-type-wrap-term term types types)
                    types)))))
         (args (fargs term))
         ((mv args types) (atj-type-annotate-args args
                                                  var-types
                                                  guards$
                                                  wrld))
         ((when (eq fn 'mv))
          (b* (((unless (>= (len types) 2))
                (raise "Internal error: ~
                        found MV applied to arguments ~x0."
                       args)
                (mv nil (list :avalue))) ; irrelevant
               ((unless (or (null required-types?)
                            (= (len types) (len required-types?))))
                (raise "Internal error: ~
                        requiring the types ~x0 for the term ~x1."
                       required-types? term)
                (mv nil (list :avalue)))) ; irrelevant
            (mv (atj-type-wrap-term (fcons-term 'mv args)
                                    types
                                    required-types?)
                (or required-types? types))))
         ((when (symbolp fn))
          (b* ((fn-info (atj-get-function-type-info fn guards$ wrld))
               (main-fn-type (atj-function-type-info->main fn-info))
               (other-fn-types (atj-function-type-info->others fn-info))
               (all-fn-types (cons main-fn-type other-fn-types))
               (types? (atj-output-types-of-min-input-types types
                                                            all-fn-types)))
            (if (consp types?)
                (b* (((unless (or (null required-types?)
                                  (= (len required-types?) (len types?))))
                      (raise "Internal error: ~
                              requiring the types ~x0 for the term ~x1, ~
                              which has a different number of types ~x2."
                             required-types? term types?)
                      (mv nil (list :avalue)))) ; irrelevant
                  (mv (atj-type-wrap-term (fcons-term fn args)
                                          types?
                                          required-types?)
                      (or required-types? types?)))
              (b* ((in-types (atj-function-type->inputs main-fn-type))
                   (out-types (atj-function-type->outputs main-fn-type))
                   ((unless (= (len in-types) (len args)))
                    (raise "Internal error: ~
                            the function ~x0 has ~x1 arguments ~
                            but a different number of input types ~x2."
                           fn (len args) (len in-types))
                    (mv nil (list :avalue))) ; irrelevant
                   ((unless (= (len in-types) (len types)))
                    (raise "Internal error: ~
                            the input types ~x0 of the function ~x1 ~
                            differ in number from the argument types ~x2."
                           in-types fn types)
                    (mv nil (list :avalue))) ; irrelevant
                   (args (atj-type-rewrap-terms args
                                                (atj-type-list-to-type-list-list
                                                 types)
                                                (atj-type-list-to-type-list-list
                                                 in-types)))
                   ((unless (consp out-types))
                    (raise "Internal error: ~
                            the function ~x0 has an empty list of output types."
                           fn)
                    (mv nil (list :avalue)))) ; irrelevant
                (mv (atj-type-wrap-term (fcons-term fn args)
                                        out-types
                                        required-types?)
                    (or required-types? out-types))))))
         (formals (lambda-formals fn))
         (var-types (append (pairlis$ formals types) var-types))
         (formals (atj-type-annotate-vars formals types))
         ((mv body types) (atj-type-annotate-term (lambda-body fn)
                                                  required-types?
                                                  var-types
                                                  guards$
                                                  wrld))
         (term (fcons-term (make-lambda formals body) args))
         ((unless (or (null required-types?)
                      (= (len required-types?) (len types))))
          (raise "Internal error: ~
                  requiring the types ~x0 for the term ~x1, ~
                  whose inferred types are ~x2."
                 required-types? term types)
          (mv nil (list :avalue)))) ; irrelevant
      (mv (atj-type-wrap-term term
                              types
                              required-types?)
          (or required-types? types)))
    ;; 2nd component is non-0
    ;; so that the call of ATJ-TYPE-ANNOTATE-MV-LET decreases:
    :measure (two-nats-measure (acl2-count term) 1))

  (define atj-type-annotate-mv-let ((term pseudo-termp)
                                    (required-types? atj-type-listp)
                                    (var-types atj-symbol-type-alistp)
                                    (guards$ booleanp)
                                    (wrld plist-worldp))
    :returns (mv (success booleanp)
                 (annotated-term pseudo-termp)
                 (resulting-types atj-type-listp))
    (b* (((unless (mbt (pseudo-termp term)))
          (mv nil nil (list :avalue)))
         ((unless (mbt (atj-type-listp required-types?)))
          (mv nil nil (list :avalue)))
         ((unless (mbt (atj-symbol-type-alistp var-types)))
          (mv nil nil (list :avalue)))
         ((mv mv-let-p indices vars mv-term body-term)
          (atj-check-mv-let-call term))
         ((unless mv-let-p)
          (mv nil nil (list :avalue))) ; 2nd and 3rd result irrelevant
         ((mv annotated-mv-term mv-term-types)
          (atj-type-annotate-term mv-term nil var-types guards$ wrld))
         ((when (= (len mv-term-types) 1))
          (mv nil nil (list :avalue))) ; 2nd and 3rd result irrelevant
         (annotated-mv (atj-type-annotate-var 'mv mv-term-types))
         (sel-types (atj-select-mv-term-types indices mv-term-types))
         (annotated-vars (atj-type-annotate-vars vars sel-types))
         (var-types (append (pairlis$ vars sel-types) var-types))
         ((mv annotated-body-term body-term-types)
          (atj-type-annotate-term
           body-term required-types? var-types guards$ wrld))
         ((unless (or (null required-types?)
                      (= (len required-types?) (len body-term-types))))
          (raise "Internal error: ~
                  requiring the types ~x0 for the term ~x1, ~
                  whose inferred types are ~x2."
                 required-types? term body-term-types)
          (mv nil nil (list :avalue))) ; irrelevant
         (wrapped-mv (atj-type-wrap-term annotated-mv mv-term-types nil))
         (annotated-mv-nth-calls (atj-type-annotate-mv-nth-terms sel-types
                                                                 indices
                                                                 wrapped-mv))
         (inner-lambda (make-lambda annotated-vars annotated-body-term))
         (inner-lambda-app (fcons-term inner-lambda annotated-mv-nth-calls))
         (annotated-inner-lambda-app (atj-type-wrap-term inner-lambda-app
                                                         body-term-types
                                                         body-term-types))
         (outer-lambda (make-lambda (list annotated-mv)
                                    annotated-inner-lambda-app))
         (outer-lambda-app (fcons-term outer-lambda (list annotated-mv-term)))
         (final-term (atj-type-wrap-term outer-lambda-app
                                         body-term-types
                                         body-term-types)))
      (mv t
          final-term
          (or required-types? body-term-types)))
    :measure (two-nats-measure (acl2-count term) 0))

  (define atj-type-annotate-args ((args pseudo-term-listp)
                                  (var-types atj-symbol-type-alistp)
                                  (guards$ booleanp)
                                  (wrld plist-worldp))
    :returns (mv (annotated-args (and (pseudo-term-listp annotated-args)
                                      (equal (len annotated-args)
                                             (len args))))
                 (resulting-types (and (atj-type-listp resulting-types)
                                       (equal (len resulting-types)
                                              (len args)))))
    (b* (((unless (mbt (pseudo-term-listp args)))
          (mv (repeat (len args) nil) (repeat (len args) :avalue)))
         ((unless (mbt (atj-symbol-type-alistp var-types)))
          (mv (repeat (len args) nil) (repeat (len args) :avalue)))
         ((when (endp args)) (mv nil nil))
         ((mv arg types) (atj-type-annotate-term (car args)
                                                 nil ; REQUIRED-TYPES?
                                                 var-types
                                                 guards$
                                                 wrld))
         ((unless (= (len types) 1))
          (raise "Internal error: ~
                  the function argument ~x0 has types ~x1."
                 (car args) types)
          (mv (repeat (len args) nil) (repeat (len args) :avalue))) ; irrelevant
         (type (car types))
         ((mv args types) (atj-type-annotate-args (cdr args)
                                                  var-types
                                                  guards$
                                                  wrld)))
      (mv (cons arg args) (cons type types)))
    :measure (two-nats-measure (acl2-count args) 0))

  :prepwork

  ((define atj-type-annotate-mv-nth-terms ((types atj-type-listp)
                                           (indices nat-listp)
                                           (wrapped-mv pseudo-termp))
     :guard (= (len types) (len indices))
     :returns (terms pseudo-term-listp)
     (b* (((when (endp types)) nil)
          (wrapped-index (atj-type-wrap-term (list 'quote (car indices))
                                             (list :ainteger)
                                             (list :ainteger)))
          (mv-nth-call `(mv-nth ,wrapped-index ,wrapped-mv))
          (wrapped-mv-nth-call (atj-type-wrap-term mv-nth-call
                                                   (list :avalue)
                                                   (list (car types))))
          (rest (atj-type-annotate-mv-nth-terms (cdr types)
                                                (cdr indices)
                                                wrapped-mv)))
       (cons wrapped-mv-nth-call rest))
     ///
     (defret len-of-atj-type-annotate-mv-nth-terms
       (equal (len terms)
              (len types))))

   (define atj-select-mv-term-types ((indices nat-listp)
                                     (mv-types atj-type-listp))
     :returns (selected-mv-types atj-type-listp)
     (b* (((unless (mbt (nat-listp indices)))
           (repeat (len indices) :avalue))
          ((unless (mbt (atj-type-listp mv-types)))
           (repeat (len indices) :avalue))
          ((when (endp indices)) nil)
          (index (car indices))
          ((unless (< index (len mv-types)))
           (raise "Internal error: ~
                   index ~x0 has no corresponding type in ~x1."
                  index mv-types)
           (repeat (len indices) :avalue))
          (type (nth index mv-types))
          (rest-types (atj-select-mv-term-types (cdr indices) mv-types)))
       (cons type rest-types))
     ///
     (defret len-of-atj-select-mv-term-types
       (equal (len selected-mv-types)
              (len indices)))))

  :verify-guards nil ; done below

  ///

  (defret-mutual atj-type-annotate-term
    (defret consp-of-atj-type-annotate-term.resulting-types
      (consp resulting-types)
      :hyp (true-listp required-types?)
      :rule-classes :type-prescription
      :fn atj-type-annotate-term)
    (defret consp-of-atj-type-annotate-mv-let.resulting-types
      (consp resulting-types)
      :hyp (true-listp required-types?)
      :rule-classes :type-prescription
      :fn atj-type-annotate-mv-let)
    (defret consp-of-atj-type-annotate-term/mv-let.resulting-types-aux
      t
      :rule-classes nil
      :fn atj-type-annotate-args)
    :hints (("Goal" :in-theory (enable atj-type-annotate-term
                                       atj-type-annotate-mv-let
                                       atj-type-annotate-args))))

  (defret-mutual atj-type-annotate-term
    (defret true-listp-of-atj-type-annotate-args.annotated-args-aux1
      t
      :rule-classes nil
      :fn atj-type-annotate-term)
    (defret true-listp-of-atj-type-annotate-args.annotated-args-aux2
      t
      :rule-classes nil
      :fn atj-type-annotate-mv-let)
    (defret true-listp-of-atj-type-annotate-args.annotated-args
      (true-listp annotated-args)
      :rule-classes :type-prescription
      :fn atj-type-annotate-args)
    :hints (("Goal" :in-theory (enable atj-type-annotate-term
                                       atj-type-annotate-mv-let
                                       atj-type-annotate-args))))

  (defret-mutual atj-type-annotate-term
    (defret true-listp-of-atj-type-annotate-args.resulting-types-aux1
      t
      :rule-classes nil
      :fn atj-type-annotate-term)
    (defret true-listp-of-atj-type-annotate-args.resulting-types-aux2
      t
      :rule-classes nil
      :fn atj-type-annotate-mv-let)
    (defret true-listp-of-atj-type-annotate-args.resulting-types
      (true-listp resulting-types)
      :rule-classes :type-prescription
      :fn atj-type-annotate-args)
    :hints (("Goal" :in-theory (enable atj-type-annotate-term
                                       atj-type-annotate-mv-let
                                       atj-type-annotate-args))))

  (defrulel verify-guards-lemma-1
    (implies (>= (len x) 1)
             (consp x)))

  (defrulel verify-guards-lemma-2
    (implies (atj-type-listp x)
             (true-listp x)))

  (verify-guards atj-type-annotate-term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-type-annotate-formals+body ((formals symbol-listp)
                                        (body pseudo-termp)
                                        (in-types atj-type-listp)
                                        (out-types atj-type-listp)
                                        (guards$ booleanp)
                                        (wrld plist-worldp))
  :guard (and (int= (len formals) (len in-types))
              (consp out-types))
  :returns (mv (annotated-formals symbol-listp)
               (annotated-body pseudo-termp))
  :short "Add ATJ type annotations to the formal parameters and body
          of an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "The input and output types of the function are supplied as arguments.
     We annotate the body, using the output types as the required types.
     We initialize the variable-type alist
     to assign the input types to the formal parameters.
     We also annotate the formal parameters,
     but note that @('var-types') has non-annotated variable names."))
  (b* ((var-types (pairlis$ formals in-types))
       (formals (atj-type-annotate-vars formals in-types))
       ((mv body &)
        (atj-type-annotate-term body out-types var-types guards$ wrld)))
    (mv formals body))
  ///

  (defret len-of-atj-type-annotate-formals+body.new-formals
    (equal (len annotated-formals)
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-var-reuse
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          marking of reusable lambda-bound variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "Consider a function body of the form")
   (xdoc::codeblock
    "(let ((x ...))"
    "  (let ((x ...))"
    "    (f x)))")
   (xdoc::p
    "The second @('x') bound by @(tsee let)
     ``overwrites'' the first one completely,
     because in the rest of the term (namely, @('(f x)'))
     only the second one is referenced, not the first one.")
   (xdoc::p
    "In contrast, consider a function body of the form")
   (xdoc::codeblock
    "(let ((x ...))"
    "  (f (let ((x ...)) (f x)) (g x)))")
   (xdoc::p
    "Here, the second @('x') bound by @(tsee let)
     ``overwrites'' the second one only partially, namely in @('(f x)'),
     but other parts of the rest of the term, namely @('(g x)'),
     reference the first one.")
   (xdoc::p
    "When we translate ACL2 to Java,
     @(tsee let)-bound variables become Java local variables.
     In the first example above,
     provided that the two @('x') variables have the same type,
     the Java code can use the same local variable for both:
     for the first binding, the Java code declares and initializes the variable;
     for the second binding, the Java code assigns to the variable,
     destructively updating it,
     which is safe because the old value is no longer needed.
     However, in the second example above,
     there have to be two distinct Java local variables,
     say @('x1') and @('x2'),
     corresponding to the two bound variables:
     both are declared and initialized,
     none can be safely destructively updated.")
   (xdoc::p
    "This pre-translation step analyzes terms
     to find out which lambda-bound (i.e. @(tsee let)-bound) variables
     can be reused and destructively updated.
     The lambda-bound variables are marked as either `new' or `old':
     the first marking means that
     the variable must be a new Java local variable
     that is declared and initilized;
     the second marking means that
     the variable can be an old Java local variable
     that is destructively assigned.
     These markings provide ``instructions'' to the ACL2-to-Java translation.")
   (xdoc::p
    "In the first example above the markings would be")
   (xdoc::codeblock
    "(let (([n]x ...))"
    "  (let (([o]x ...))"
    "    (f [o]x)))")
   (xdoc::p
    "while in the second example above the markings would be")
   (xdoc::codeblock
    "(let (([n]x ...))"
    "  (f (let (([n]x ...)) (f [n]x)) (g [n]x)))")
   (xdoc::p
    "Note that, as we mark the lambda-bound variables,
     we must mark in the same way the occurrences in the lambda bodies,
     to maintain the well-formedness of the ACL2 terms.")
   (xdoc::p
    "This pre-translation step must be performed after the "
    (xdoc::seetopic "atj-pre-translation-type-annotation"
                    "type annotation step")
    ", so that types are kept into account:
      a variable can be reused only if
      it has the same type in both lambda formal parameters.
      Since the type annotation step adds types to variable names,
      by comparing names for equality we also compare their types for equality.
      If two variables have different types,
      they also have different names (since the name includes the type).")
   (xdoc::p
    "After this translation step, the "
    (xdoc::seetopic "atj-pre-translation-var-renaming"
                    "variable renaming step")
    " takes care of renaming apart ACL2 variables with the same name
      that are both marked as `new'."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-var-new ((var symbolp))
  :returns (marked-var symbolp)
  :short "Mark a variable as `new'."
  (packn-pos (list "[N]" var) var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-vars-new ((vars symbol-listp))
  :returns (marked-vars symbol-listp)
  :short "Lift @(tsee atj-mark-var-new) to lists."
  (cond ((endp vars) nil)
        (t (cons (atj-mark-var-new (car vars))
                 (atj-mark-vars-new (cdr vars)))))
  ///

  (defret len-of-atj-mark-vars-new
    (equal (len marked-vars)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-var-old ((var symbolp))
  :returns (marked-var symbolp)
  :short "Mark a variable as `old'."
  (packn-pos (list "[O]" var) var))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-unmark-var ((var symbolp))
  :returns (mv (unmarked-var symbolp)
               (new? booleanp))
  :short "Decompose a marked variable into its marking and its unmarked name."
  :long
  (xdoc::topstring
   (xdoc::p
    "The marking is a boolean: @('t') for `new', @('nil') for `old'."))
  (b* ((string (symbol-name var))
       ((unless (and (>= (length string) 5)
                     (member-equal (subseq string 0 3) '("[N]" "[O]"))))
        (raise "Internal error: ~x0 has the wrong format." var)
        (mv nil nil)) ; irrelevant
       (new? (eql (char string 1) #\N))
       (unmarked-string (subseq string 3 (length string)))
       (unmarked-var (intern-in-package-of-symbol unmarked-string var)))
    (mv unmarked-var new?)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-unmark-vars ((vars symbol-listp))
  :returns (mv (unmarked-vars symbol-listp)
               (new?s boolean-listp))
  :short "Lift @(tsee atj-unmark-var) to lists."
  (b* (((when (endp vars)) (mv nil nil))
       ((mv var new?) (atj-unmark-var (car vars)))
       ((mv vars new?s) (atj-unmark-vars (cdr vars))))
    (mv (cons var vars) (cons new? new?s)))
  ///

  (defret len-of-atj-unmark-vars.unmarked-vars
    (equal (len unmarked-vars)
           (len vars)))

  (defret len-of-atj-unmark-vars.new?s
    (equal (len new?s)
           (len vars))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-mark-term
  :short "Mark the variables in a term as `new' or `old'."
  :long
  (xdoc::topstring
   (xdoc::p
    "Marking a variable as `new' is always ``safe'',
     because it is always safe to introduce a new Java local variable.
     On the other hand, marking a variable as `old' requires care,
     to prevent a Java local variable may be erroneously reused.
     To understand this marking algorithm,
     one has to keep in mind how ACL2 terms are translated to Java:
     see @(tsee atj-gen-shallow-term) and companions.
     This is a delicate algorithm:
     a proof of correctness would be very beneficial.")
   (xdoc::p
    "Two conditions are necessary for reusing a variable:
     (i) the variable must be in scope (i.e. exists and be accessible); and
     (ii) the previous value of the variable must not be used afterwards.
     The parameters @('vars-in-scope') and @('vars-used-after')
     support the checking of these conditions.")
   (xdoc::p
    "The parameter @('vars-in-scope') consists of the variables in scope
     at the point where the term under consideration occurs.
     At the top level (see @(tsee atj-mark-formals+body)),
     it is intialized with the (unmarked) formal parameters
     of the ACL2 function whose formal parameters and body are being marked:
     indeed, the formal parameters of a function are in scope for the body.
     As we descend into subterms, when we encounter a lambda expression,
     we extend @('vars-in-scope') with its (unmarked) formal parameters;
     only the ones that are marked as `new' actually extend the scope,
     while the ones marked as `old' were already in @('vars-in-scope').
     The generated Java code evaluates functions' actual arguments
     left-to-right:
     thus, local variables introduced (for lambda expressions in) an argument
     are generally (see exception shortly) in scope for successive arguments.
     Therefore, @('vars-in-scope') is threaded through the marking functions
     (i.e. passed as argument and returned, possibly updated, as result).
     When processing a lambda expression applied to arguments,
     @('vars-in-scope') is threaded first through the arguments,
     and then through the body (which is evaluated after the argument),
     after augmenting it with the formal parameters.
     The exception mentioned above is for @(tsee if),
     which is turned into a Java @('if')
     whose branches are Java blocks:
     Java variables declared inside these blocks
     have a more limited scope (namely, the respective block),
     and therefore should not be added to the @('vars-in-scope')
     that is passed to mark terms after the @(tsee if).
     The variables introduced in the test of the @(tsee if)
     are declared outside the branches' blocks,
     and so they are threaded through.
     The @('vars-in-scope') resulting from marking the test of the @(tsee if)
     is passed to mark both branches,
     but their returned @('vars-in-scope') is ignored.
     The code for @(tsee if) is a bit more complicated
     because of the special treatment of @('(if a a b)') terms,
     which are treated as @('(or a b)'):
     the Java code generated for this case is a little different
     (see @(tsee atj-gen-shallow-or-app)),
     but the treatment of @('vars-in-scope')
     is essentially the same as just explained
     (there is no `then' branch to mark, because it is the same as the test,
     which has already been marked).")
   (xdoc::p
    "The parameter @('vars-used-after') consists of the variables
     that occur free (i.e. whose current value is used)
     ``after'' the term under consideration.
     At the top level (see @(tsee atj-mark-formals+body)),
     it is initialized with @('nil'),
     because no variables are used after evaluating the body of the function.
     As we descend into subterms,
     @('vars-used-after') is extended as needed,
     based on the ``neighboring'' subterms
     that will be evaluated (in the generated Java code)
     after the subterm under consideration.
     In particular, when marking an actual argument of a function call,
     @('vars-used-after') is extended with all the free variables
     of the actual arguments of the same function call
     that occur after the one being marked;
     recall that arguments are evaluated left-to-right
     in the generated Java code.
     The function @('atj-mark-terms'),
     which is used to mark the actual arguments of a function call,
     augments @('vars-used-after') with the free variables
     in the @(tsee cdr) of the current list of arguments;
     this is somewhat inefficient,
     as the same free variables are collected repeatedly
     as the argument terms are processed,
     but terms are not expected to be too large in the short term;
     this will be optimized when needed.
     Calls of @(tsee if) are treated a little differently,
     because the arguments are not evaluated left-to-right
     in the generated Java code:
     when marking the test, we augment @('vars-used-after')
     with all the free variables in the branches;
     when marking either branch, we use the same @('vars-used-after')
     that was passed for the @(tsee if),
     because the two branches are independent.
     The @(tsee or) form of @(tsee if) is treated slightly differently as usual,
     but the essence is the same.
     Unlike @('vars-in-scope'), @('var-used-after') is not threaded through;
     it is simply passed down, and augmented as needed.
     The body of a lambda expression is evaluated after its actual arguments:
     thus, when marking the actual arguments of a lambda expression
     we must augment @('vars-used-after')
     with the free variables of the lambda expression,
     i.e. the free variables in the body minus the formal parameters.")
   (xdoc::p
    "As we mark the formal parameters of a lambda expression,
     we need to mark in the same way
     all the references to these variables in the body of the lambda expression.
     For this purpose, we pass around a mapping
     from (unmarked) variables to markings:
     this could be an alist from symbols to booleans,
     but we isomorphically use lists (treated as sets) of symbols instead,
     which are the variable marked as `new',
     while the variables not in the list are marked as `old'.
     When the term to be marked is a variable,
     we look it up in this list, and mark it accordingly.")
   (xdoc::p
    "When the term to be marked is a quoted constant,
     it is obviously left unchanged.")
   (xdoc::p
    "When the term to be marked is a function application,
     we first treat the @(tsee if) (and @(tsee or)) case separately.
     We mark the test, and after that the two branches.
     The handling of @('vars-in-scope') and @('vars-used-after') for this case
     has been explained above.")
   (xdoc::p
    "For all other function applications, which are strict,
     we first mark the actual arguments,
     treating @('vars-in-scope') and @('vars-used-after')
     as explained above.
     For calls of named functions, we are done at this point:
     we put the named function in front of the marked arguments and return.
     For calls of lambda expression,
     we use the auxiliary function @('atj-mark-lambda-formals')
     to decide which formal parameters should be marked as `new' or `old'.
     We mark the parameter as `old' (indicating that the variable can be reused)
     iff the following three conditions hold.
     The first condition is that the variable must be in scope;
     note that variables have already been annotated with types at this point,
     and so by testing variable names we also test their types,
     which is needed for Java
     (i.e. we could not reuse a Java variable of type @('Acl2Symbol')
     to store a value of type @('Acl2String')).
     The second condition is that the variable is not used
     after the lambda application term, i.e. it is not in @('vars-used-after'):
     otherwise, we would overwrite something that was supposed to be used later,
     with incorrect results in general.
     The third condition is that the variable is not free
     in any of the actual arguments that correspond to
     the formal parameters of the lambda expression
     that come just after the one being marked:
     this is because, in the generated Java code,
     the lambda variables are assigned one after the other,
     and therefore we should not overwrite a variable
     that may be needed afterwards.
     For instance, consider a swap @('(let ((x y) (y x)) ...)'):
     @('x') cannot be reused
     (even if it is in scope and not used after the @(tsee let))
     because it must be assigned to @('y') after @('y') is assigned to @('x')
     (Java does not support parallel assignment);
     on the other hand, @('y') could be reused,
     if it is in scope and not used after the @(tsee let),
     because at the time of assigning to @('y')
     its (previous) value has already been assigned to @('x')."))

  (define atj-mark-term ((term pseudo-termp)
                         (vars-in-scope symbol-listp)
                         (vars-used-after symbol-listp)
                         (vars-to-mark-new symbol-listp))
    :returns (mv (marked-term pseudo-termp :hyp :guard)
                 (new-vars-in-scope symbol-listp :hyp :guard))
    (b* (((when (variablep term))
          (if (member-eq term vars-to-mark-new)
              (mv (atj-mark-var-new term) vars-in-scope)
            (mv (atj-mark-var-old term) vars-in-scope)))
         ((when (fquotep term)) (mv term vars-in-scope))
         (fn (ffn-symb term))
         ((when (eq fn 'if))
          (b* ((test (fargn term 1))
               (then (fargn term 2))
               (else (fargn term 3)))
            (if (equal test then)
                (b* ((vars-used-after-test (union-eq vars-used-after
                                                     (all-vars-open else)))
                     ((mv test
                          vars-in-scope) (atj-mark-term test
                                                        vars-in-scope
                                                        vars-used-after-test
                                                        vars-to-mark-new))
                     ((mv else &) (atj-mark-term else
                                                 vars-in-scope
                                                 vars-used-after
                                                 vars-to-mark-new)))
                  (mv `(if ,test ,test ,else)
                      vars-in-scope))
              (b* ((vars-used-after-test (union-eq vars-used-after
                                                   (all-vars-open-lst
                                                    (list then else))))
                   ((mv test
                        vars-in-scope) (atj-mark-term test
                                                      vars-in-scope
                                                      vars-used-after-test
                                                      vars-to-mark-new))
                   ((mv then &) (atj-mark-term then
                                               vars-in-scope
                                               vars-used-after
                                               vars-to-mark-new))
                   ((mv else &) (atj-mark-term else
                                               vars-in-scope
                                               vars-used-after
                                               vars-to-mark-new)))
                (mv `(if ,test ,then ,else)
                    vars-in-scope)))))
         (args (fargs term))
         (vars-used-after
          (if (symbolp fn)
              vars-used-after
            (union-eq vars-used-after
                      (set-difference-eq (all-vars-open (lambda-body fn))
                                         (lambda-formals fn)))))
         ((mv marked-args vars-in-scope) (atj-mark-terms args
                                                         vars-in-scope
                                                         vars-used-after
                                                         vars-to-mark-new))
         ((when (symbolp fn)) (mv (fcons-term fn marked-args)
                                  vars-in-scope))
         (formals (lambda-formals fn))
         ((mv marked-formals
              vars-to-mark-new) (atj-mark-lambda-formals formals
                                                         args
                                                         vars-in-scope
                                                         vars-used-after
                                                         vars-to-mark-new))
         (vars-in-scope (union-eq formals vars-in-scope))
         ((mv marked-body
              vars-in-scope) (atj-mark-term (lambda-body fn)
                                            vars-in-scope
                                            vars-used-after
                                            vars-to-mark-new)))
      (mv (fcons-term (make-lambda marked-formals marked-body)
                      marked-args)
          vars-in-scope)))

  (define atj-mark-terms ((terms pseudo-term-listp)
                          (vars-in-scope symbol-listp)
                          (vars-used-after symbol-listp)
                          (vars-to-mark-new symbol-listp))
    :returns (mv (marked-terms (and (pseudo-term-listp marked-terms)
                                    (equal (len marked-terms)
                                           (len terms)))
                               :hyp :guard)
                 (new-vars-in-scope symbol-listp :hyp :guard))
    (b* (((when (endp terms)) (mv nil vars-in-scope))
         (first-term (car terms))
         (rest-terms (cdr terms))
         (vars-used-after-first-term (union-eq vars-used-after
                                               (all-vars-open-lst rest-terms)))
         ((mv marked-first-term
              vars-in-scope) (atj-mark-term first-term
                                            vars-in-scope
                                            vars-used-after-first-term
                                            vars-to-mark-new))
         ((mv marked-rest-terms
              vars-in-scope) (atj-mark-terms rest-terms
                                             vars-in-scope
                                             vars-used-after
                                             vars-to-mark-new)))
      (mv (cons marked-first-term marked-rest-terms)
          vars-in-scope)))

  :prepwork

  ((local (include-book "std/typed-lists/symbol-listp" :dir :system))

   (define atj-mark-lambda-formals ((formals symbol-listp)
                                    (actuals pseudo-term-listp)
                                    (vars-in-scope symbol-listp)
                                    (vars-used-after symbol-listp)
                                    (vars-to-mark-new symbol-listp))
     :guard (= (len formals) (len actuals))
     :returns (mv (marked-formals (and (symbol-listp marked-formals)
                                       (equal (len marked-formals)
                                              (len formals))))
                  (new-vars-to-mark-new
                   symbol-listp
                   :hyp (and (symbol-listp formals)
                             (symbol-listp vars-to-mark-new))))
     (b* (((when (endp formals)) (mv nil vars-to-mark-new))
          (formal (car formals))
          (new? (or (not (member-eq formal vars-in-scope))
                    (member-eq formal vars-used-after)
                    (dumb-occur-var-open-lst formal (cdr actuals))))
          (marked-formal (if new?
                             (atj-mark-var-new formal)
                           (atj-mark-var-old formal)))
          (vars-to-mark-new (if new?
                                (cons formal vars-to-mark-new)
                              (remove-eq formal vars-to-mark-new)))
          ((mv marked-formals
               vars-to-mark-new) (atj-mark-lambda-formals (cdr formals)
                                                          (cdr actuals)
                                                          vars-in-scope
                                                          vars-used-after
                                                          vars-to-mark-new)))
       (mv (cons marked-formal marked-formals)
           vars-to-mark-new))
     ///

     (more-returns
      (marked-formals true-listp :rule-classes :type-prescription)
      (new-vars-to-mark-new true-listp
                            :hyp (true-listp vars-to-mark-new)
                            :rule-classes :type-prescription))

     (defret len-of-atj-mark-lambda-formals.marked-formals
       (equal (len marked-formals)
              (len formals)))))

  :verify-guards nil ; done below

  ///

  (defrulel true-listp-when-symbol-listp
    (implies (symbol-listp x)
             (true-listp x)))

  (verify-guards atj-mark-term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-mark-formals+body ((formals symbol-listp) (body pseudo-termp))
  :returns (mv (new-formals symbol-listp)
               (new-body pseudo-termp :hyp :guard))
  :short "Mark all the variables
          in the formal parameters and body of an ACL2 function definition
          as `new' or `old'"
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the top level of the marking algorithm;
     this top level is discussed in @(tsee atj-mark-term)."))
  (b* ((marked-formals (atj-mark-vars-new formals))
       ((mv marked-body &) (atj-mark-term body formals nil formals)))
    (mv marked-formals marked-body))
  ///

  (defret len-of-atj-mark-formals+body.new-formals
    (equal (len new-formals)
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ atj-pre-translation-var-renaming
  :parents (atj-pre-translation)
  :short "Pre-translation step performed by ATJ:
          renaming of the ACL2 variables."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done only in the shallow embedding.")
   (xdoc::p
    "We systematically rename all the ACL2 variables
     so that their new names are valid Java variable names
     and so that different ACL2 variables with the same name are renamed apart,
     unless the variables have been marked for reuse
     by the previous pre-translation step.
     This simplifies the ACL2-to-Java translation,
     which can just turn each ACL2 variable
     into a Java variable with the same name."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *atj-init-indices*
  :short "Initial variable index alist."
  :long
  (xdoc::topstring
   (xdoc::p
    "When we rename ACL2 variables to Java variables,
     we must avoid the names in @(tsee *atj-disallowed-jvar-names*).
     We do that by initializing the alist from variables to indices
     to associate index 1 to all the disallowed names.
     That is, we pretend that
     variables with the disallowed names have already been used,
     so that an index 1 (or greater) will be appended to any variable
     that would otherwise happen to be a disallowed name.
     Appending an index to a disallowed name always yields an allowed name.")
   (xdoc::p
    "Note that @(tsee *atj-disallowed-jvar-names*) is a list of strings,
     but the keys of the index map must be symbols.
     We use @(tsee str::intern-list) to convert them.
     It is critical to use the same package (currently @('\"JAVA\"'))
     used by @(tsee atj-var-to-jvar)."))
  (pairlis$ (str::intern-list *atj-disallowed-jvar-names* (pkg-witness "JAVA"))
            (repeat (len *atj-disallowed-jvar-names*) 1))
  ///
  (assert-event (symbol-pos-alistp *atj-init-indices*)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formal ((var symbolp)
                           (indices symbol-pos-alistp)
                           (curr-pkg stringp)
                           (vars-by-name string-symbollist-alistp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (new-var symbolp)
               (new-indices symbol-pos-alistp
                            :hyp (and (symbol-pos-alistp indices)
                                      (symbolp var))))
  :short "Rename a formal parameters of
          a defined function or lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-rename-formals),
     the renaming of a variable is established
     when the variable is encountered as a formal parameter.
     This motivates the name of this function.")
   (xdoc::p
    "This function is called only on formal parameters marked as `new'.
     Formal parameters marked as `old' are just renamed
     according to the existing renaming map @('renaming-old').")
   (xdoc::p
    "Each ACL2 function is turned into a Java method,
     whose body is a shallowly embedded representation
     of the ACL2 function body.
     The ACL2 function body may reference the ACL2 function's parameter,
     as well as @(tsee let)-bound variables (via lambda expressions).
     Thus, the same variable symbol may in fact denote different variables
     in different parts of an ACL2 function body.
     Java does not allow different local variables with the same name
     in (nested scopes in) the same method,
     and so we need to map homonymous but different ACL2 variables
     in the same ACL2 function
     to differently named Java variables
     in the same Java method.
     We use numeric indices, one for each variable name,
     which is appended (as explained below) to the Java variable name
     to make it unique within the Java mehtod.")
   (xdoc::p
    "Another need for disambiguation arises because of package prefixes.
     An ACL2 variable is a symbol,
     which consists of a name and also a package name:
     two distinct variables may have the same name
     but different package names.
     However, when we append the package name and the name of the symbol,
     we have unique Java variable names.")
   (xdoc::p
    "We use @(tsee atj-var-to-jvar) to turn @('var')
     into a new symbol whose name is a valid Java variable name.
     Then we ensure its uniqueness by retrieving and using the next index,
     from the parameter @('indices'); more on this below.
     In general, as mentioned in @(tsee atj-var-to-jvar),
     we append the index after the result of @(tsee atj-var-to-jvar);
     but if the index is 0, we do not append it, to improve readability;
     in particular, if there is just one variable with a certain name,
     since we start with index 0, no index is ever added to the name.
     When this function is called,
     the indices alist always associates non-0 indices to
     the symbols whose names are in @(tsee *atj-disallowed-jvar-names*):
     see @(tsee *atj-init-indices*).")
   (xdoc::p
    "The name obtained by optionally appending the index
     may not be a valid Java identifier:
     this happens if it is a Java keyword or literal, or if it is empty.
     (This may actually happen only if no index is appended.)
     If this is the case, we add a single @('$') at the end,
     which makes the name valid and unambiguous.")
   (xdoc::p
    "The index to use for this variable
     is retrieved from the @('indices') parameter,
     which is an alist that associates each variable to its next index to use.
     If a variable is not in the alist, it is as if it had index 0,
     and in that case no index is added, as explained above.
     The alist is updated
     by incrementing the next index to use for the variable,
     and returned along with the new variable.")
   (xdoc::p
    "The keys of the alist are not the original ACL2 variables,
     but the renamed variables resulting from @(tsee atj-var-to-jvar).
     This gives us more flexibility,
     by obviating the requirement that @(tsee atj-var-to-jvar) be injective:
     if this function is not injective,
     then different ACL2 variables may become the same Java variable,
     and the next index must be the same for all of these variables,
     so that they can be properly disambiguated.")
   (xdoc::p
    "This pre-translation step is performed
     after the type annotation and new/old marking steps,
     but the caller of this function decomposes the marked annotated variable
     into its unmarked unannotated name, type, and marking,
     and only passes the unannotated name @('var') to this function.
     The @('vars-by-name') parameter of this function
     consists of variable names without annotations and markings."))
  (b* ((jvar (atj-var-to-jvar var curr-pkg vars-by-name))
       (jvar+index? (assoc-eq jvar indices))
       (index (if jvar+index? (cdr jvar+index?) 0))
       (indices (acons jvar (1+ index) indices))
       (jvar (atj-var-add-index jvar index)))
    (mv jvar indices))

  :prepwork
  ((defrulel returns-lemma
     (implies (posp x)
              (posp (1+ x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formals ((formals symbol-listp)
                            (renaming-new symbol-symbol-alistp)
                            (renaming-old symbol-symbol-alistp)
                            (indices symbol-pos-alistp)
                            (curr-pkg stringp)
                            (vars-by-name string-symbollist-alistp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (new-formals symbol-listp
                            :hyp (and (symbol-listp formals)
                                      (symbol-symbol-alistp renaming-new)))
               (new-renaming-new symbol-symbol-alistp
                                 :hyp (and (symbol-listp formals)
                                           (symbol-symbol-alistp renaming-new)))
               (new-renaming-old symbol-symbol-alistp
                                 :hyp (and (symbol-listp formals)
                                           (symbol-symbol-alistp renaming-old)))
               (new-indices symbol-pos-alistp
                            :hyp (and (symbol-listp formals)
                                      (symbol-pos-alistp indices))))
  :short "Rename the formal parameters of
          a defined function or lambda expression."
  :long
  (xdoc::topstring
   (xdoc::p
    "As explained in @(tsee atj-rename-formal),
     the shallowly embedded ACL2 variables are made unique via indices.
     There is an independent index for each ACL2 variable,
     so we use an alist from symbols to natural numbers
     to keep track of these indices.
     This alist is threaded through the functions
     that rename all the variables in ACL2 terms.
     This pre-translation step happens
     after the type annotation and new/old marking step,
     but the variables in this alist are without annotations and markings,
     because annotations and markings are discarded
     when generating Java variables,
     and thus two ACL2 variables that only differ in annotations or markings
     must be renamed apart and must share the same index in the alist.")
   (xdoc::p
    "In ACL2, a variable is ``introduced''
     as a formal parameter of a function or lambda expression,
     and then referenced in the body of the function or lambda expression.
     The choice and use of the index must be done at this introduction time,
     and not at every reference to the variable after its introduction.
     Thus, when we encounter the formals of a function or lambda expression,
     we generate the Java variable names for these ACL2 variables,
     using the current indices, and update and return the indices.
     This is the case only if the formal parameter is marked as `new';
     if instead it is marked as `old',
     we look it up in a renaming map,
     which is an alist from the old variable names to the new variable names,
     i.e. it expresses the current renaming of variables.
     There are actually two renaming alists:
     one for the variables marked as `new',
     and one for the variables marked as `old':
     see @(tsee atj-rename-term) for more information.
     This function takes both renaming maps,
     and augments both of them with the renamings for the formal parameters
     that are marked as `new'.
     The variables in the renaming maps are all type-annotated,
     for faster lookup when renaming variables in terms.
     The variables in the renaming maps are not marked as `new' or `old';
     as mentioned above, we have two separate maps for new and old variables.")
   (xdoc::p
    "Each ACL2 formal parameter in the input list
     is processed differently based on whether it is marked `new' or `old'.
     If it is marked `old',
     it is simply renamed according to the @('renaming-old') alist,
     which must include an entry for the variable.
     When it is marked as `new',
     it is unmarked and unannotated and passed to @(tsee atj-rename-formal),
     which uses and updates the index associated to the variable.")
   (xdoc::p
    "The formals @('formals') being renamed are annotated,
     because this pre-translation step happens after the type annotation step.
     Thus, the type annotations are removed prior to the renaming
     and added back after the renaming."))
  (b* (((when (endp formals)) (mv nil renaming-new renaming-old indices))
       (formal (car formals))
       ((mv uformal new?) (atj-unmark-var formal))
       ((when (not new?)) ; i.e. old
        (b* ((renaming-pair (assoc-eq uformal renaming-old))
             ((unless (consp renaming-pair))
              (raise "Internal error: ~x0 has no renaming." formal)
              ;; irrelevant:
              (mv (true-list-fix formals)
                  renaming-new
                  renaming-old
                  indices))
             (new-uformal (cdr renaming-pair))
             (new-formal (atj-mark-var-old new-uformal))
             ((mv new-formals
                  renaming-new
                  renaming-old
                  indices) (atj-rename-formals (cdr formals)
                                               renaming-new
                                               renaming-old
                                               indices
                                               curr-pkg
                                               vars-by-name)))
          (mv (cons new-formal new-formals) renaming-new renaming-old indices)))
       ((mv uuformal types) (atj-type-unannotate-var uformal))
       ((mv new-uuformal indices)
        (atj-rename-formal uuformal indices curr-pkg vars-by-name))
       (new-uformal (atj-type-annotate-var new-uuformal types))
       (renaming-new (acons uformal new-uformal renaming-new))
       (renaming-old (acons uformal new-uformal renaming-old))
       (new-formal (atj-mark-var-new new-uformal))
       ((mv new-formals
            renaming-new
            renaming-old
            indices) (atj-rename-formals (cdr formals)
                                         renaming-new
                                         renaming-old
                                         indices
                                         curr-pkg
                                         vars-by-name)))
    (mv (cons new-formal new-formals) renaming-new renaming-old indices))

  ///

  (more-returns
   (new-formals true-listp :rule-classes :type-prescription))

  (defret len-of-atj-rename-formals.new-formals
    (equal (len new-formals)
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defines atj-rename-term
  :short "Rename all the ACL2 variables in an ACL2 term to their Java names."
  :long
  (xdoc::topstring
   (xdoc::p
    "The alist from variables to indices
     is threaded through this function and its mutually recursive companion,
     in the same way as the renaming alist for the `old' variables;
     thus different variables in different Java scopes may have the same index.
     This alist contains variables without annotations or markings;
     see @(tsee atj-rename-formals) for motivation.")
   (xdoc::p
    "The renaming alist for variables marked as `new'
     is not threaded through:
     it is just passed down, according to ACL2's scoping.
     This alist contains variables with type annotations
     but without markings for `old' or `new';
     see @(tsee atj-rename-formals) for motivation.")
   (xdoc::p
    "The renaming alist for variables marked as `old'
     is threaded through instead,
     in the same way as the set of variables in scope in @(tsee atj-mark-term)
     (see that function for details).
     This is because variables are marked for reuse
     based (also) on that threading of the variables in scope:
     when we encounter a variable to rename that is marked for reuse,
     we must have its name available in the renaming alist.
     This alist contains variables with type annotations
     but without markings for `old' or `new';
     see @(tsee atj-rename-formals) for motivation.")
   (xdoc::p
    "If the term is a variable,
     it is unmarked,
     looked up in the appropriate renaming alist based on the marking,
     and replaced with the renamed variable, which is re-marked.
     Recall that variable names are generated
     via @(tsee atj-rename-formals) when variables are introduced,
     i.e. from formal parameters of defined functions and lambda expressions.")
   (xdoc::p
    "If the term is a quoted constant, it is obviously left unchanged.")
   (xdoc::p
    "If the term is a function application,
     its actual arguments are recursively processed,
     renaming all their variables.
     If the function is a named one, it is of course left unchanged.
     If instead it is a lambda expression,
     we process the renaming of its formal parameters,
     which in general augments the two renaming alists,
     and then recursively process the body of the lambda expression."))

  (define atj-rename-term ((term pseudo-termp)
                           (renaming-new symbol-symbol-alistp)
                           (renaming-old symbol-symbol-alistp)
                           (indices symbol-pos-alistp)
                           (curr-pkg stringp)
                           (vars-by-name string-symbollist-alistp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (new-term pseudo-termp :hyp :guard)
                 (new-renaming-old symbol-symbol-alistp :hyp :guard)
                 (new-indices symbol-pos-alistp :hyp :guard))
    (b* (((when (variablep term))
          (b* (((mv var new?) (atj-unmark-var term))
               (renaming-pair (assoc-eq var (if new?
                                                renaming-new
                                              renaming-old)))
               ((unless (consp renaming-pair))
                (raise "Internal error: no renaming found for variable ~x0."
                       term)
                (mv nil nil nil)) ; irrelevant
               (new-var (cdr renaming-pair))
               (new-term (if new?
                             (atj-mark-var-new new-var)
                           (atj-mark-var-old new-var))))
            (mv new-term renaming-old indices)))
         ((when (fquotep term)) (mv term renaming-old indices))
         (fn (ffn-symb term))
         ((when (eq fn 'if))
          (b* ((test (fargn term 1))
               (then (fargn term 2))
               (else (fargn term 3)))
            (if (equal test then)
                (b* (((mv new-test
                          renaming-old
                          indices) (atj-rename-term test
                                                    renaming-new
                                                    renaming-old
                                                    indices
                                                    curr-pkg
                                                    vars-by-name))
                     ((mv new-else
                          &
                          &) (atj-rename-term else
                                              renaming-new
                                              renaming-old
                                              indices
                                              curr-pkg
                                              vars-by-name)))
                  (mv `(if ,new-test ,new-test ,new-else)
                      renaming-old
                      indices))
              (b* (((mv new-test
                        renaming-old
                        indices) (atj-rename-term test
                                                  renaming-new
                                                  renaming-old
                                                  indices
                                                  curr-pkg
                                                  vars-by-name))
                   ((mv new-then
                        &
                        &) (atj-rename-term then
                                            renaming-new
                                            renaming-old
                                            indices
                                            curr-pkg
                                            vars-by-name))
                   ((mv new-else
                        &
                        &) (atj-rename-term else
                                            renaming-new
                                            renaming-old
                                            indices
                                            curr-pkg
                                            vars-by-name)))
                (mv `(if ,new-test ,new-then ,new-else)
                    renaming-old
                    indices)))))
         (args (fargs term))
         ((mv new-args
              renaming-old
              indices) (atj-rename-terms args
                                         renaming-new
                                         renaming-old
                                         indices
                                         curr-pkg
                                         vars-by-name))
         ((when (symbolp fn)) (mv (fcons-term fn new-args)
                                  renaming-old
                                  indices))
         (formals (lambda-formals fn))
         (body (lambda-body fn))
         ((mv new-formals
              renaming-new
              renaming-old
              indices) (atj-rename-formals formals
                                           renaming-new
                                           renaming-old
                                           indices
                                           curr-pkg
                                           vars-by-name))
         ((mv new-body
              renaming-old
              indices) (atj-rename-term body
                                        renaming-new
                                        renaming-old
                                        indices
                                        curr-pkg
                                        vars-by-name)))
      (mv (fcons-term (make-lambda new-formals new-body)
                      new-args)
          renaming-old
          indices)))

  (define atj-rename-terms ((terms pseudo-term-listp)
                            (renaming-new symbol-symbol-alistp)
                            (renaming-old symbol-symbol-alistp)
                            (indices symbol-pos-alistp)
                            (curr-pkg stringp)
                            (vars-by-name string-symbollist-alistp))
    :guard (not (equal curr-pkg ""))
    :returns (mv (new-terms (and (pseudo-term-listp new-terms)
                                 (equal (len new-terms) (len terms)))
                            :hyp :guard)
                 (new-renaming-old symbol-symbol-alistp :hyp :guard)
                 (new-indices symbol-pos-alistp :hyp :guard))
    (cond ((endp terms) (mv nil renaming-old indices))
          (t (b* (((mv new-term
                       renaming-old
                       indices) (atj-rename-term (car terms)
                                                 renaming-new
                                                 renaming-old
                                                 indices
                                                 curr-pkg
                                                 vars-by-name))
                  ((mv new-terms
                       renaming-old
                       indices) (atj-rename-terms (cdr terms)
                                                  renaming-new
                                                  renaming-old
                                                  indices
                                                  curr-pkg
                                                  vars-by-name)))
               (mv (cons new-term new-terms)
                   renaming-old
                   indices)))))

  :verify-guards nil ; done below
  ///
  (verify-guards atj-rename-term))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-rename-formals+body ((formals symbol-listp)
                                 (body pseudo-termp)
                                 (curr-pkg stringp))
  :guard (not (equal curr-pkg ""))
  :returns (mv (new-formals symbol-listp :hyp :guard)
               (new-body pseudo-termp :hyp :guard))
  :short "Rename all the ACL2 variables to their Java names,
          in the formal parameters and body of an ACL2 function."
  :long
  (xdoc::topstring
   (xdoc::p
    "We collect all the variables in the formals and body,
     remove their markings and annotations
     (recall that the type annotation and new/old marking pre-translation steps
     take place before this renaming step),
     and organize them by symbol name:
     the resulting alist is passed to the renaming functions.")
   (xdoc::p
    "Starting with the empty alist of indices and the empty renaming alists,
     we introduce renamed variables for the formal parameters,
     and we use the resulting renaming alists to process the body."))
  (b* ((vars (union-eq formals (all-free/bound-vars body)))
       ((mv vars &) (atj-unmark-vars vars))
       (vars (atj-type-unannotate-vars vars))
       (vars-by-name (organize-symbols-by-name vars))
       ((mv new-formals renaming-new renaming-old indices)
        (atj-rename-formals
         formals nil nil *atj-init-indices* curr-pkg vars-by-name))
       ((mv new-body & &)
        (atj-rename-term
         body renaming-new renaming-old indices curr-pkg vars-by-name)))
    (mv new-formals new-body))
  ///

  (defret len-of-atj-rename-formals+body.new-formals
    (equal (len new-formals)
           (len formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define atj-pre-translate ((fn symbolp)
                           (formals symbol-listp)
                           (body pseudo-termp)
                           (in-types atj-type-listp)
                           (out-types atj-type-listp)
                           (deep$ booleanp)
                           (guards$ booleanp)
                           (wrld plist-worldp))
  :guard (and (= (len formals) (len in-types))
              (consp out-types))
  :returns (mv (new-formals symbol-listp :hyp :guard)
               (new-body pseudo-termp :hyp :guard))
  :parents (atj-pre-translation)
  :short "Pre-translate the formal parameters and body
          of an ACL2 function definition."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is done before the translation from ACL2 to Java proper.
     The pre-translation steps are described "
    (xdoc::seetopic "atj-pre-translation" "here")
    "."))
  (b* ((body (atj-remove-return-last body guards$))
       (body (remove-dead-if-branches body))
       (body (remove-unused-vars body))
       ((when deep$) (mv formals body))
       (body (remove-trivial-vars body))
       (body (atj-restore-mv-terms body out-types))
       ((mv formals body) (atj-type-annotate-formals+body
                           formals body in-types out-types guards$ wrld))
       ((mv formals body) (atj-mark-formals+body formals body))
       ((mv formals body) (atj-rename-formals+body
                           formals body (symbol-package-name fn))))
    (mv formals body))
  ///

  (defret len-of-atj-pre-translate.new-formals
    (equal (len new-formals)
           (len formals))))
