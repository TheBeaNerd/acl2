; ABNF (Augmented Backus-Naur Form) Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ABNF")

(include-book "../grammar-definer/defgrammar")
(include-book "../grammar-definer/deftreeops")
(include-book "../operations/in-terminal-set")
(include-book "../operations/plugging")
(include-book "../notation/core-rules")

; (depends-on "uri.abnf")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ uri-example
  :parents (examples)
  :short "The ABNF grammar of the URI (Uniform Resource Identifier) syntax."
  :long
  (xdoc::topstring-p
   "The URI syntax is specified by "
   (xdoc::ahref "https://www.rfc-editor.org/info/rfc3986" "RFC 3968")
   ".")
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgrammar *uri-grammar-rules*
  :short "The URI grammar rules from RFC 3986."
  :long
  (xdoc::topstring
   (xdoc::p
    "The file @('uri.abnf') contains the URI grammar rules,
     copied and pasted from RFC 3986.
     The ABNF grammar parser and abstractor are used
     to build an ACL2 representation of the URI grammar rules,
     excluding the referenced ABNF core rules.")
   (xdoc::p
    "The URI grammar rules are well-formed.")
   (xdoc::p
    "We keep this constant unexpanded in output."))
  :file "uri.abnf"
  :untranslate t
  :well-formed t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *all-uri-grammar-rules*
  :short "All the URI grammar rules, including the referenced ABNF core rules."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are obtained by plugging the core rules into the URI rules.")
   (xdoc::p
    "The resulting rules are well-formed and closed.
     They generate terminal strings consisting only of ASCII codes;
     more precisely, the ASCII codes of
     all the visible characters (i.e. @('VCHAR') in the ABNF core rules)
     except
     double quote,
     angle brackets,
     backslash,
     caret,
     curly braces, and
     vertical bar.")
   (xdoc::p
    "We keep this constant unexpanded in output."))
  (plug-rules *uri-grammar-rules*
              *core-rules*)
  ///

  (add-const-to-untranslate-preprocess *all-uri-grammar-rules*)

  (defrule rulelist-wfp-of-*all-uri-grammar-rules*
    (rulelist-wfp *all-uri-grammar-rules*))

  (defrule rulelist-closedp-of-*all-uri-grammar-rules*
    (rulelist-closedp *all-uri-grammar-rules*))

  (defrule ascii-only-*all-uri-grammar-rules*
    (rulelist-in-termset-p *all-uri-grammar-rules*
                           (integers-from-to 0 127)))

  (defrule precise-ascii-codes-of-*all-uri-grammar-rules*
    (rulelist-in-termset-p *all-uri-grammar-rules*
                           (difference (integers-from-to 33 126)
                                       (list (char-code #\")
                                             (char-code #\<)
                                             (char-code #\>)
                                             (char-code #\\)
                                             (char-code #\^)
                                             (char-code #\{)
                                             (char-code #\|)
                                             (char-code #\})))))

  (defrule abnf-core-rules-in-*all-uri-grammar-rules*
    (implies (member-equal core-rule *core-rules*)
             (iff (member-equal core-rule *all-uri-grammar-rules*)
                  (member-equal core-rule (list *rule_ALPHA*
                                                *rule_DIGIT*
                                                *rule_HEXDIG*))))
    :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(deftreeops *all-uri-grammar-rules* :prefix uri-cst)
