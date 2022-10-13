; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

; the order of the following INCLUDE-BOOKs should determine
; the order of the subtopics of the ABNF topic below:
(include-book "abstract-syntax")
(include-book "semantics")
(include-book "operations/top")
(include-book "core-rules")
(include-book "core-rules-validation")
(include-book "concrete-syntax-rules")
(include-book "concrete-syntax-rules-validation")
(include-book "concrete-syntax")
(include-book "concrete-syntax-validation")
(include-book "parsing-primitives-seq")
(include-book "parsing-primitives-defresult")
(include-book "parser")
(include-book "parser-verification")
(include-book "abstractor")
(include-book "parser-and-abstractor-validation")
(include-book "parser-generators")
(include-book "examples/top")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ abnf

  :parents (acl2::kestrel-books acl2::projects)

  :short "A library for ABNF (Augmented Backus-Naur Form)."

  :long

  (xdoc::topstring

   (xdoc::p
    "ABNF is a standardized formal grammar notation
     used in several Internet syntax specifications,
     e.g. "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc3986" "URI") ", "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc7230" "HTTP") ", "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc5322" "IMF") ", "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc5321" "SMTP") ", "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc3501" "IMAP") ", and "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc7159" "JSON")
    ". ABNF is specified by "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc5234" "RFC 5234")
    " and "
    (xdoc::ahref "https://www.rfc-editor.org/info/rfc7405" "RFC 7405")
    "; the latter updates two portions of the former.
     The syntax of ABNF is specified in ABNF itself.")

   (xdoc::p
    "This ACL2 library provides:")
   (xdoc::ul
    (xdoc::li
     "A formalization of the syntax and semantics of the ABNF notation.")
    (xdoc::li
     "A verified parser that turns ABNF grammar text
      (e.g. from the HTTP RFC)
      into a formal representation suitable for formal specification
      (e.g. for HTTP parsing).")
    (xdoc::li
     "An abstractor from ABNF concrete syntax to ABNF abstract syntax.")
    (xdoc::li
     "Executable operations on ABNF grammars,
      e.g. to check their well-formedness and to compose them.")
    (xdoc::li
     "Some basic parsing primitives usable as part of larger parsers.")
    (xdoc::li
     "Some very preliminary tools to generate
      parsing functions from grammar rules.")
    (xdoc::li
     "Examples of use of the parser, the abstractor, and some grammar operations
      on a few real-world ABNF grammars (e.g. for HTTP)."))

   (xdoc::p
    "Besides the aforementioned examples,
     the parser, abstractor, and some grammar operations have been used on "
    (xdoc::seetopic "java::grammar" "an ABNF grammar of Java")
    ", "
    (xdoc::seetopic "yul::concrete-syntax" "an ABNF grammar of Yul")
    ", and "
    (xdoc::seetopic "c::grammar" "an ABNF grammar of a subset of C")
    ". The parsing generation tools have been used to generate part of "
    (xdoc::seetopic "yul::lexer" "a Yul lexer")
    ".")

   (xdoc::p
    "In the documentation of this library,
     `[RFC]' refers to the result of updating RFC 5234 as specified by RFC 7405.
     Sections and subsections of [RFC] are referenced
     by appending their designations separated by colon:
     for example, `[RFC:3]' refers to Section 3 of RFC 5234.
     As another example, `[RFC:2.3]' refers to
     the result of updating Section 2.3 of RFC 5234
     as specified in Section 2.1 of RFC 7405.
     These square-bracketed references may be used
     as nouns or parenthetically.")

   (xdoc::p
    "This "
    (xdoc::ahref
     "https://www.kestrel.edu/home/people/coglio/vstte18.pdf"
     "VSTTE 2018 paper")
    " provides an overview
     of the ABNF notation formalization,
     of the verified parser,
     and of the syntax abstractor
     (but not of the operations on ABNF grammars,
     of the parsing primitives,
     of the parsing generation tools,
     or of the real-world examples).
     The differences between the paper and the ABNF library
     are described "
    (xdoc::seetopic "differences-with-paper" "here")
    "."))

  :order-subtopics t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc differences-with-paper

  :parents (abnf)

  :short "Differences with the paper."

  :long

  (xdoc::topstring

   (xdoc::p
    "For brevity, the paper makes the following slight simplfications
     compared to the ABNF library:")

   (xdoc::ul

    (xdoc::li
     "The forms in the paper omit
      guards,
      rule classes,
      measures,
      hints,
      keyed options for documentation (e.g. @(':short')),
      and some keyed options for "
     (xdoc::seetopic "fty::fty" "FTY")
     " types (e.g. @(':pred')).")

    (xdoc::li
     "The paper uses
      @(tsee defun),
      @(tsee mutual-recursion),
      @(tsee defthm), and
      @(tsee defun-sk)
      instead of
      @(tsee define),
      @(tsee defines),
      @(tsee defrule), and
      @(tsee define-sk).")

    (xdoc::li
     "The paper uses slightly shorter names
      for the parameters of some functions
      (e.g. @('alt') instead of @('alternation')).")

    (xdoc::li
     "The paper uses @('*abnf-grammar*')
      as the name of the constant @(tsee *grammar*)."))))
