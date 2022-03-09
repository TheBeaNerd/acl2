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

(include-book "integers")
(include-book "portable-ascii-identifiers")

(include-book "kestrel/fty/pseudo-event-form" :dir :system)
(include-book "kestrel/std/system/table-alist-plus" :dir :system)
(include-book "kestrel/std/util/tuple" :dir :system)
(include-book "kestrel/utilities/er-soft-plus" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ shallow-structures
  :parents (atc-shallow-embedding)
  :short "A model of C structures in the shallow embedding."
  :long
  (xdoc::topstring
   (xdoc::p
    "Our initial model of C structures is fairly simple,
     but we will extend it as needed.")
   (xdoc::p
    "Since C structure types are user-defined,
     we provide a macro @(tsee struct) to define
     an ACL2 representation of a C structure type.
     The user must call this macro
     to introduce the structure types that the C code must use.")
   (xdoc::p
    "The @(tsee struct) macro takes as inputs
     the name (i.e. tag [C:6.7.2.3]) of the structure type
     and a list of fields,
     each of which consists of a name and a designation of an integer type.
     The names of the structure type and of the fields
     must be distinct symbols whose @(tsee symbol-name) is
     a portable ASCII C identifier as defined in the user documentation.
     The designation of the integer types is one of the symbols")
   (xdoc::ul
    (xdoc::li "@('schar')")
    (xdoc::li "@('uchar')")
    (xdoc::li "@('sshort')")
    (xdoc::li "@('ushort')")
    (xdoc::li "@('sint')")
    (xdoc::li "@('uint')")
    (xdoc::li "@('slong')")
    (xdoc::li "@('ulong')")
    (xdoc::li "@('sllong')")
    (xdoc::li "@('ullong')"))
   (xdoc::p
    "which are the names of the corresponding fixtypes.
     For now we only support integer fields in structures.")
   (xdoc::p
    "The @(tsee struct) macro introduces
     a recognizer called @('struct-<tag>-p'),
     where @('<tag>') is the tag of the structure type.
     It also introduces functions to read and write the fields,
     called @('struct-<tag>-read-<field>') and @('struct-<tag>-write-<field>'),
     where @('<tag>') is the tag and @('<field>') is the field name.
     Under the hood, the @(tsee struct) macro generates a @(tsee fty::defprod),
     but that should not be directly accessed,
     as @(tsee struct) provides a layer of abstraction;
     in fact, in principle it should be possible to change @(tsee struct)
     to not even use @(tsee fty::defprod),
     without affecting the representation of
     shallowly embedded C code in ACL2.")
   (xdoc::p
    "The field readers and writers generated by @(tsee struct)
     are analogous to the integer array readers and writers
     in the model of C integer arrays in the shallow embedding.
     A field reader returns the value of the field,
     while a field writer returns an updated structure value.")
   (xdoc::p
    "C code shallowly embedded in ACL2 can use
     the recognizers @('struct-<tag>-p') in guards
     to specify structure types for parameters;
     more precisely, pointers to structure types, initially.
     That is, similarly to arrays, structures are in the heap,
     and pointers to them are passed to the represented C functions,
     which may side-effect those structures via the field writers,
     which represent assignment to structure field
     accessed via the C @('->') operator (not the @('.') operator).
     C structures may also be passed around by value in general,
     but initially we support only passing by pointer.
     Note that C arrays may only be passed by pointers, in effect,
     as arrays are not first-class entities in C,
     but merely collections of contiguous objects,
     accessed via pointers to the first object of the collections.")
   (xdoc::p
    "The @(tsee struct) macro also records, in an ACL2 table,
     information about the shallowly embedded structures it defines."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *struct-table*
  :short "Name of the table of shallowly embedded C structures."
  'struct-table)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defalist string-type-alist
  :short "Fixtype of alists from ACL2 strings to C types."
  :key-type string
  :val-type type
  :true-listp t
  :keyp-of-nil nil
  :valp-of-nil nil
  :pred string-type-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod struct-info
  :short "Fixtype of information about shallowly embedded C structures."
  :long
  (xdoc::topstring
   (xdoc::p
    "For each C structure, we store the following information.")
   (xdoc::p
    "We store an alist from strings to types,
     which represents the typed fields of the structure.
     The keys are the field names, in the order they appear in the structure,
     and the values are the corresponding types.
     The keys are always unique portable ASCII C identifiers,
     but this is not currently enforced in this fixtype.")
   (xdoc::p
    "We also store the call of @(tsee struct) that defines the structure.
     This supports redundancy checking."))
  ((fields string-type-alist)
   (call pseudo-event-form))
  :pred struct-infop)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defoption struct-info-option
  struct-info
  :short "Fixtype of
          optional information about shallowly embedded C structures."
  :pred struct-info-optionp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection struct-table-definition
  :short "Definition of the table of shallowly embedded C structures."
  :long
  (xdoc::topstring
   (xdoc::p
    "The keys are symbols that represent the tags of the structures.
     The name of each such symbol is a portable ASCII C identifiers,
     but this constraint is not enforced in the table's guard.
     The symbol names of the keys are unique.")
   (xdoc::p
    "The values are the information about the structures.
     See @(tsee struct-info)."))

  (make-event
   `(table ,*struct-table* nil nil
      :guard (and (symbolp acl2::key)
                  (struct-infop acl2::val)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-table-lookup ((tag symbolp) (wrld plist-worldp))
  :returns (info? struct-info-optionp)
  :short "Retrieve information about a shallowly embedded C structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "The lookup is based on the name of the symbol,
     because we disallow shallowly embedded C structures
     to have different symbols with the same name,
     since it is the symbol name that represents the C structure tag."))
  (b* ((table (table-alist+ *struct-table* wrld))
       (info? (struct-table-lookup-aux (symbol-name tag) table)))
    (if (struct-info-optionp info?)
        info?
      (raise "Internal error: malformed structure information ~x0 for ~x1."
             info? tag)))

  :prepwork

  ((local (include-book "std/alists/top" :dir :system))

   (define struct-table-lookup-aux ((tag-name stringp) (table alistp))
     :parents nil
     (b* (((when (endp table)) nil)
          ((cons key val) (car table))
          ((when (and (symbolp key)
                      (equal tag-name
                             (symbol-name key))))
           val))
       (struct-table-lookup-aux tag-name (cdr table))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-table-record-event ((tag symbolp) (info struct-infop))
  :returns (event pseudo-event-formp)
  :short "Event to update the table of shallowly embedded C structures
          by recording a new C structure in it."
  `(table ,*struct-table* ',tag ',info))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-process-fields ((fields true-listp) (ctx ctxp) state)
  :returns (mv erp (alist string-type-alistp) state)
  :short "Process the field inputs of a @(tsee struct) call."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the inputs of @(tsee struct) after the first one,
     which specifies the structure tag.
     Each such input must be a doublet consisting of two symbols.
     The first symbol represents the field name:
     the name of the symbol must be a portable ASCII C identifier
     that is distinct from the other field names.
     The second symbol represents the field type:
     it must be one of the fixtype names of the C integer types
     (see @(see shallow-structures))."))
  (b* (((when (endp fields)) (acl2::value nil))
       (field (car fields))
       ((unless (std::tuplep 2 field))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE), ~
                   but the input ~x0 does not have this form."
                  field))
       (name (first field))
       (type (second field))
       ((unless (symbolp name))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE) of symbols, ~
                   but the first component of ~x0 is not a symbol."
                  field))
       (name (symbol-name name))
       ((unless (atc-ident-stringp name))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE) of symbols ~
                   where the SYMBOL-NAME of NAME is ~
                   a portable ASCII C identifier (see ATC user documentation), ~
                   but the SYMBOL-NAME of the first component of ~x0 ~
                   is not a portable ASCII C identifier."
                  field))
       ((unless (symbolp type))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE) of symbols, ~
                   but the second component of ~x0 is not a symbol."
                  field))
       (type (fixtype-to-integer-type type))
       ((when (not type))
        (er-soft+ ctx t nil
                  "Each input after the first one ~
                   must be a doublet (NAME TYPE) of symbols ~
                   where TYPE is one of the symbols in ~&0, ~
                   but the second component of ~x1 ~
                   is not one of those symbols."
                  '(schar
                    uchar
                    sshort
                    ushort
                    sint
                    uint
                    slong
                    ulong
                    sllong
                    ullong)
                  field))
       ((er alist) (struct-process-fields (cdr fields) ctx state)))
    (acl2::value (acons name type alist)))
  :verify-guards :after-returns)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-process-inputs ((args true-listp)
                               (call pseudo-event-formp)
                               (ctx ctxp)
                               state)
  :returns (mv erp
               (val (tuple (tag symbolp)
                           (fields string-type-alistp)
                           (redundant booleanp)
                           val))
               state)
  :short "Process the inputs of a @(tsee struct) call."
  :long
  (xdoc::topstring
   (xdoc::p
    "We process the tag and the fields.
     If the table already contains an entry for this tag,
     the call must be identical, in which case the call is redundant;
     if the call is not identical, it is an error."))
  (b* ((irrelevant (list nil nil nil))
       ((unless (consp args))
        (er-soft+ ctx t irrelevant
                  "There must be at least one input, ~
                   but no inputs were supplied."))
       (tag (car args))
       ((unless (symbolp tag))
        (er-soft+ ctx t irrelevant
                  "The first input must be a symbol, ~
                   but ~x0 is not."
                  tag))
       ((unless (atc-ident-stringp (symbol-name tag)))
        (er-soft+ ctx t irrelevant
                  "The name of the symbol ~x0 passed as first input, ~
                   which defines the name of the structure, ~
                   must be a portable ASCII C identifier, ~
                   but its name ~x1 is not."
                  tag (symbol-name tag)))
       (info (struct-table-lookup tag (w state)))
       ((when info)
        (if (equal (struct-info->call info) call)
            (acl2::value (list tag nil t))
          (er-soft+ ctx t irrelevant
                    "There is already a structure with tag ~x0 ~
                     recorded in the table of shallowly embedded C structures, ~
                     but its call ~x1 differs from the current ~x2, ~
                     so the call is not redundant."
                    tag (struct-info->call info) call)))
       (fields (cdr args))
       ((mv erp fields state) (struct-process-fields fields ctx state))
       ((when erp) (mv erp irrelevant state)))
    (acl2::value (list tag fields nil)))
  ///
  (more-returns
   (val true-listp :rule-classes :type-prescription)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-gen-defprod-fields ((tag symbolp) (fields string-type-alistp))
  :returns (list true-listp)
  :short "Generate the @(tsee fty::defprod) fields for the structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "This generates the list of fields that goes into the @(tsee fty::defprod),
      which is a list of doublets
      whose first components are symbols that name the fields
      and whose second components are symbols that name fixtypes.
      (These second components may be more general in @(tsee fty::defprod),
      but for @(tsee struct) we only need fixtype names there.)")
   (xdoc::p
    "Each field name is put in the package of the tag.")
   (xdoc::p
    "The types are all expected to be integers,
     because of the checks done when processing the inputs of @(tsee struct)."))
  (b* (((when (endp fields)) nil)
       ((cons name type) (car fields))
       ((unless (type-integerp type))
        (raise "Internal error: ~
                the type ~x0 of field ~x1 of structure ~x2 ~
                is not an integer type."
               type name tag))
       (defprod-field-name (intern-in-package-of-symbol name tag))
       (defprod-field-type (integer-type-to-fixtype type))
       (defprod-field (list defprod-field-name
                            defprod-field-type))
       (defprod-fields (struct-gen-defprod-fields tag (cdr fields))))
    (cons defprod-field defprod-fields)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-gen-defprod ((tag symbolp) (fields string-type-alistp))
  :returns (event pseudo-event-formp)
  :short "Generate the @(tsee fty::defprod) for the structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "The name of the fixtype is the tag preceded by @('struct-'),
     in the same package as the tag.")
   (xdoc::p
    "The fields are as explained in @(tsee struct-gen-defprod-fields).")
   (xdoc::p
    "The predicate is the fixtype name with @('-p') after it,
     which is the default for @(tsee fty::defprod).")
   (xdoc::p
    "We also tag the structure with a keyword whose name
     is the same as the structure tag."))
  (b* ((defprod-name (packn-pos (list 'struct- tag) tag))
       (defprod-fields (struct-gen-defprod-fields tag fields))
       (defprod-tag (intern (symbol-name defprod-name) "KEYWORD")))
    `(fty::defprod ,defprod-name
       ,defprod-fields
       :tag ,defprod-tag)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-gen-readers/writers ((tag symbolp) (fields string-type-alistp))
  :returns (events pseudo-event-form-listp)
  :short "Generate the functions to read and write structure fields."
  :long
  (xdoc::topstring
   (xdoc::p
    "The function names have the form described in @(see shallow-structures),
     in the same package as the tag."))
  (b* (((when (endp fields)) nil)
       ((cons name type) (car fields))
       (struct-tag (packn-pos (list 'struct- tag) tag))
       (struct-tag-p (packn-pos (list struct-tag '-p) tag))
       (struct-tag->name (packn-pos (list struct-tag '-> name) tag))
       (change-struct-tag (packn-pos (list 'change- struct-tag) tag))
       (struct-tag-read-name (packn-pos (list struct-tag '-read- name) tag))
       (struct-tag-write-name (packn-pos (list struct-tag '-write- name) tag))
       ((unless (type-integerp type))
        (raise "Internal error: ~
                the type ~x0 of field ~x1 of structure ~x2 ~
                is not an integer type."
               type name tag))
       (typep (pack (integer-type-to-fixtype type) 'p))
       (field-keyword (intern name "KEYWORD"))
       (struct-var tag)
       (new-struct-var (packn-pos (list struct-var '-new) tag))
       (field-var (intern-in-package-of-symbol name tag))
       (reader `(define ,struct-tag-read-name ((,struct-var ,struct-tag-p))
                  :returns (,field-var ,typep)
                  (,struct-tag->name ,struct-var)
                  :hooks (:fix)))
       (writer `(define ,struct-tag-write-name ((,struct-var ,struct-tag-p)
                                                (,field-var ,typep))
                  :returns (,new-struct-var ,struct-tag-p)
                  (,change-struct-tag ,struct-var ,field-keyword ,field-var)
                  :hooks (:fix)))
       (more-readers/writers (struct-gen-readers/writers tag (cdr fields))))
    (list* reader writer more-readers/writers)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-gen-everything ((tag symbolp)
                               (fields string-type-alistp)
                               (call pseudo-event-formp))
  :returns (event pseudo-event-formp)
  :short "Generate all the events."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the @(tsee fty::defprod),
     the readers and writers,
     and the table event."))
  (b* ((defprod-event (struct-gen-defprod tag fields))
       (readers/writers-events (struct-gen-readers/writers tag fields))
       (info (make-struct-info :fields fields :call call))
       (table-event (struct-table-record-event tag info)))
    `(progn
       ,defprod-event
       ,@readers/writers-events
       ,table-event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define struct-fn ((args true-listp)
                   (call pseudo-event-formp)
                   (ctx ctxp)
                   state)
  :returns (mv erp (event pseudo-event-formp) state)
  :short "Process the inputs and generate the events."
  (b* (((mv erp (list tag fields redundant) state)
        (struct-process-inputs args call ctx state))
       ((when erp) (mv erp '(_) state))
       ((when redundant) (acl2::value '(value-triple :redundant)))
       (event (struct-gen-everything tag fields call)))
    (acl2::value event)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro+ struct (&whole call &rest args)
  :short "Define a shallowly embedded C structure."
  :long
  (xdoc::topstring
   (xdoc::p
    "See @(see shallow-structures)."))
  `(make-event (struct-fn ',args ',call 'struct state)))
