; Propagate-iso Transformation -- Documentation
;
; Copyright (C) 2020 Kestrel Institute
;
; License: A 3-clause BSD license.  See the file books/3BSD-mod.txt.
;
; Author: Stephen Westfold (westfold@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file documents the propagate_iso, a transformation to propagate an isomorphism from
; supplied isomorphic translations of interface functions of a data type to their direct
; and indirect users.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "kestrel/event-macros/xdoc-constructors" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc propagate-iso
  :parents (apt)
  :short "Propagate an isomorphism from a set of isomorphically transformed functions to events that use them."

  :long

  (xdoc::topstring

   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

    (xdoc::evmac-section-intro

      (xdoc::p
        "@('propagate-iso') takes one or more isomorphisms and a set of functions and a sequence of events
         and propagates the isomorphisms from the given set of functions to those events that reference any of
         these functions either directly or directly. It maintains a substitution from old functions to their new isomorphic
         functions. For function definitions it creates a new function by applying the substitution to the old body and
         extends the substitution to map the old function name to the newly created function name. Similarly, it applies
         the substitution to existing theorems to generate theorems on the new functions.  Currently does not handle
         mutual recursion.")

      (xdoc::evmac-section-form
        (xdoc::codeblock
          " (propagate-iso isomorphism-name-or-names"
          "                fn-iso-specs"
          "                &key"
          "                :first-event       ; required name of an event"
          "                :last-event        ; required name of an event"
          "                :dont-verify-guards   ; default nil"
          "                :enabled           ; default nil"
          "                :iso-rules         ; default nil"
          "                :osi-rules         ; default nil"
          "                :hints-map         ; default nil"
          "                )"))

      (xdoc::desc
        "@('isomorphism-name-or-names')"
        (xdoc::p
          "A single name or a list of names of isomorphisms defined using @(tsee defiso)."))

      (xdoc::desc
        "@('fn-iso-specs')"
        (xdoc::p
          "A list of functions associated with information about their isomorphics translations and
      signatures.  Each element of the list has the form:")

        (xdoc::codeblock
          "(fn iso-fn fn-->iso-fn--thm iso-fn-->fn--thm arg-sig => result-sig)"
          )

        (xdoc::p
          "where @('iso-fn') is the isomorphic version of @('fn') and @('fn-->iso-fn--thm') is a
           theorem for rewriting @('fn') to @('iso-fn'), and and @('iso-fn-->fn--thm') is a
           theorem for rewriting @('iso-fn') to @('fn').  @('arg-sig') gives the signature of
           the argument list of @('fn') with respect to the isomorphism, i.e. if an argument of
           @('fn') is of one of the isomorphism types (predicate) then the corresponding element
           of the signature is that predicate, otherwise it is @('*').  Similarly, if @('fn')
           returns a single value then it is @('*') or the name of an isomorphism predicate, or if
           it returns multiple values then it is a list of such values."))

      (xdoc::desc
        "@(':first-event') and @(':last-event') "
        (xdoc::p
          "These give the first and last event that @('propagate-iso')
           considers.  Functions definitions and theorems are ignored if they do not reference any of the functions in
           @('fn-iso-specs') or any of the functions for which @('propagate-iso') has already generated an
           isomorphic version."))

      (xdoc::p
        "The remaining options are only useful in the cases where the hints generated by @('propagate-iso') are not
         sufficient to allow any proofs to go through.")

      (xdoc::desc
        "@(':dont-verify-guards')"
        (xdoc::p
          "@('T') means do not verify guards of any of the generated events."))

      (xdoc::desc
        "@(':enabled')"
        (xdoc::p
          "A list of runes to use in proofs to add to the lists that @('propagate-iso')
      determines to be appropriate."))

      (xdoc::desc
        "@(':iso-rules')"
        (xdoc::p
          "A list of runes to use in proofs for theorems where @('propagate-iso')
           is using a strategy that transforms old functions into new functions."))

      (xdoc::desc
        "@(':osi-rules')"
        (xdoc::p
          "A list of runes to use in proofs for theorems where @('propagate-iso')
           is using a strategy that transforms new functions into old functions."))

      (xdoc::p
        "@('propagate-iso') ensures that rules in @(':iso-rules') and @(':osi-rules') are not enabled at the
         same time.")

      (xdoc::desc
        "@(':hints-map')"
        (xdoc::p
          "Used to override or augment the hints generated by  @('propagate-iso')"))

      )))
