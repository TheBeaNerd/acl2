(TYPES::NAMED-RULE)
(TYPES::SYMBOLP-PSEUDO-TERMP-T-T-TRUE-LISTP-IMPLIES-TRUE-LISTP-NAMED-RULE)
(TYPES::NAMED-RULE)
(TYPES::NAMED-RULE-LIST
 (7 7 (:TYPE-PRESCRIPTION SYMBOL-FNS::SAFE-WITNESS))
 )
(TYPES::SYMBOLP-SYMBOLP-NATP-PSEUDO-TERM-LISTP-T-T-TRUE-LISTP-IMPLIES-TRUE-LISTP-NAMED-RULE-LIST)
(TYPES::NAMED-RULE-LIST
 (89 10 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (72 1 (:DEFINITION PSEUDO-TERMP))
 (65 11 (:DEFINITION SYMBOL-LISTP))
 (48 48 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (48 8 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (40 39 (:REWRITE DEFAULT-CDR))
 (38 37 (:REWRITE DEFAULT-CAR))
 (32 4 (:DEFINITION TRUE-LISTP))
 (26 5 (:REWRITE DEFAULT-COERCE-3))
 (16 16 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (16 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (16 8 (:REWRITE DEFAULT-COERCE-1))
 (15 3 (:DEFINITION LEN))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (12 1 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (10 10 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (8 8 (:REWRITE SET::IN-SET))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (7 7 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (7 4 (:REWRITE DEFAULT-+-2))
 (6 1 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (2 1 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (2 1 (:REWRITE DEFAULT-PKG-IMPORTS))
 (1 1 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(TYPES::REFINED-TYPE-FIX)
(TYPES::EXTENDED-TYPE-FIX)
(TYPES::XEQUIV)
(TYPES::REFINED-TYPE-EQUIV)
(TYPES::EXTENDED-TYPE-EQUIV)
(TYPES::EXTENDED-TYPE-EQUIV-IS-AN-EQUIVALENCE)
(TYPES::REFINED-TYPE-EQUIV-IS-AN-EQUIVALENCE)
(TYPES::XEQUIV-IS-AN-EQUIVALENCE)
(TYPES::XEQUIV-REFINED-TYPE-FIX-EXTENDED-TYPE-FIX)
(TYPES::REFINED-TYPE-EQUIV-DEFINITION)
(TYPES::EXTENDED-TYPE-EQUIV-DEFINITION)
(TYPES::XEQUIV-IMPLIES-XEQUIV-REFINED-TYPE-FIX-1)
(TYPES::CANARY-LEMMA)
(TYPES::EXTENDED-TYPE-EQUIV-XEQUIV-REFINED-TYPE-FIX-CONGRUENCE)
(TYPES::EXTENDED-TYPE-EQUIV-REFINED-TYPE-EQUIV-REFINEMENT)
(TYPES::EXTEND-IN-THEORY)
(TYPES::TYPE-REFINEMENT-EVENTS)
(TYPES::SYMBOLP-SYMBOLP-SYMBOLP-KWARGS-ALISTP-IMPLIES-TRUE-LISTP-TYPE-REFINEMENT-EVENTS
 (46 45 (:REWRITE DEFAULT-CAR))
 (43 11 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (36 6 (:DEFINITION TYPES::ASSOC-KEYWORD!))
 (31 30 (:REWRITE DEFAULT-CDR))
 (24 8 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (11 11 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (9 1 (:DEFINITION TYPES::KWARGS-ALISTP))
 (8 8 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (3 1 (:DEFINITION KEYWORDP))
 (2 2 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (1 1 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 )
(TYPES::TYPE-REFINEMENT-EVENTS
 (85 21 (:REWRITE DEFUN::SYMBOL-LISTP-IS-PSEUDO-TERM-LISTP))
 (80 80 (:REWRITE DEFAULT-CAR))
 (59 59 (:REWRITE DEFAULT-CDR))
 (48 16 (:DEFINITION SYMBOL-LISTP))
 (36 6 (:DEFINITION TYPES::ASSOC-KEYWORD!))
 (24 24 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (21 21 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (16 16 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (12 4 (:DEFINITION BINARY-APPEND))
 (2 2 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 )
(TYPES::ALL-TYPE-REFINEMENT-EVENTS)
(TYPES::SYMBOLP-SYMBOLP-BOOLEANP-SYMBOL-LISTP-ALISTP-KWARGS-ALISTP-IMPLIES-TRUE-LISTP-ALL-TYPE-REFINEMENT-EVENTS)
(TYPES::ALL-TYPE-REFINEMENT-EVENTS
 (35 34 (:REWRITE DEFAULT-CDR))
 (34 34 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (3 3 (:REWRITE SYMBOL-FIX-WHEN-SYMBOLP))
 )
(TYPES::MAKE-TYPE-REFINEMENT-EVENTS)
(TYPES::SYMBOLP-ALISTP-KWARGS-ALISTP-IMPLIES-TRUE-LISTP-MAKE-TYPE-REFINEMENT-EVENTS)
(TYPES::MAKE-TYPE-REFINEMENT-EVENTS
 (99 96 (:REWRITE DEFAULT-CAR))
 (96 16 (:DEFINITION TYPES::ASSOC-KEYWORD!))
 (83 80 (:REWRITE DEFAULT-CDR))
 (18 3 (:DEFINITION BINARY-APPEND))
 (10 10 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (9 9 (:TYPE-PRESCRIPTION TYPES::TYPE-REFINEMENT-EVENTS))
 (3 3 (:REWRITE SYMBOL-FIX-WHEN-SYMBOLP))
 (2 2 (:TYPE-PRESCRIPTION TYPES::CHECK-KEYWORDS))
 )
(TYPES::REFINEMENT-PROOF-EVENTS-FN)
(TYPES::REFINEMENT-PROOF-EVENTS)
(TYPES::BASE-REFINES-ALL)
(TYPES::ALL-REFINE-BASE)
(TYPES::DEF-REFINEMENT-FN)
(TYPES::DEF-REFINEMENT-FN-WRAPPER)
(TYPES::EQUAL-TYPE-IMPLIES-TYPE)
(TYPES::EQUAL-NFIX-IFIX
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(TYPES::NAT-EQUIV-DEFINITION)
(TYPES::INT-EQUIV-DEFINITION)
(TYPES::EQUAL-IS-AN-EQUIVALENCE)
(TYPES::CANARY-LEMMA-INSTANCE)
(INT-EQUIV-EQUAL-NFIX-CONGRUENCE)
(INT-EQUIV-NAT-EQUIV-REFINEMENT)
(TYPES::EQUAL-TYPE-IMPLIES-TYPE)
(TYPES::EQUAL-IFIX-FIX
 (24 24 (:REWRITE TYPES::EQUAL-TYPE-IMPLIES-TYPE))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(TYPES::INT-EQUIV-DEFINITION)
(TYPES::NUMBER-EQUIV-DEFINITION)
(TYPES::EQUAL-IS-AN-EQUIVALENCE)
(TYPES::CANARY-LEMMA-INSTANCE)
(NUMBER-EQUIV-EQUAL-IFIX-CONGRUENCE)
(NUMBER-EQUIV-INT-EQUIV-REFINEMENT)
(TYPES::FIX-EQUIV-IFIX)
(TYPES::EQUAL-TYPE-IMPLIES-TYPE)
(TYPES::EQUAL-RFIX-FIX
 (26 26 (:REWRITE TYPES::EQUAL-TYPE-IMPLIES-TYPE))
 (4 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE-QUOTED-CONSTANT RFIX-UNDER-RATIONAL-EQUIV))
 )
(TYPES::RATIONAL-EQUIV-DEFINITION)
(TYPES::NUMBER-EQUIV-DEFINITION)
(TYPES::EQUAL-IS-AN-EQUIVALENCE)
(TYPES::CANARY-LEMMA-INSTANCE)
(NUMBER-EQUIV-EQUAL-RFIX-CONGRUENCE)
(NUMBER-EQUIV-RATIONAL-EQUIV-REFINEMENT)
(TYPES::EQUAL-TYPE-IMPLIES-TYPE)
(TYPES::EQUAL-IFIX-RFIX
 (24 24 (:REWRITE TYPES::EQUAL-TYPE-IMPLIES-TYPE))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(TYPES::INT-EQUIV-DEFINITION)
(TYPES::RATIONAL-EQUIV-DEFINITION)
(TYPES::EQUAL-IS-AN-EQUIVALENCE)
(TYPES::CANARY-LEMMA-INSTANCE)
(RATIONAL-EQUIV-EQUAL-IFIX-CONGRUENCE)
(RATIONAL-EQUIV-INT-EQUIV-REFINEMENT)
(TYPES::EQUAL-TYPE-IMPLIES-TYPE)
(TYPES::EQUAL-NFIX-IFIX
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(TYPES::NAT-EQUIV-DEFINITION)
(TYPES::INT-EQUIV-DEFINITION)
(TYPES::EQUAL-IS-AN-EQUIVALENCE)
(TYPES::CANARY-LEMMA-INSTANCE)
(INT-EQUIV-EQUAL-NFIX-CONGRUENCE)
(INT-EQUIV-NAT-EQUIV-REFINEMENT)
(TYPES::EQUAL-TYPE-IMPLIES-TYPE)
(TYPES::EQUAL-POS-FIX-NFIX
 (25 14 (:REWRITE TYPES::EQUAL-TYPE-IMPLIES-TYPE))
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 )
(TYPES::POS-EQUIV-DEFINITION)
(TYPES::NAT-EQUIV-DEFINITION)
(TYPES::EQUAL-IS-AN-EQUIVALENCE)
(TYPES::CANARY-LEMMA-INSTANCE)
(NAT-EQUIV-EQUAL-POS-FIX-CONGRUENCE)
(NAT-EQUIV-POS-EQUIV-REFINEMENT)
(TYPES::EQUAL-TYPE-IMPLIES-TYPE)
(TYPES::EQUAL-BFIX-NFIX
 (12 2 (:REWRITE BFIX-BITP))
 (4 4 (:TYPE-PRESCRIPTION BITP))
 (4 4 (:REWRITE TYPES::EQUAL-TYPE-IMPLIES-TYPE))
 (3 2 (:DEFINITION BITP))
 (2 2 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(TYPES::BIT-EQUIV-DEFINITION)
(TYPES::NAT-EQUIV-DEFINITION)
(TYPES::EQUAL-IS-AN-EQUIVALENCE)
(TYPES::CANARY-LEMMA-INSTANCE)
(NAT-EQUIV-EQUAL-BFIX-CONGRUENCE)
(NAT-EQUIV-BIT-EQUIV-REFINEMENT)
