(R1CS::MAKE-PRODUCT-CONSTRAINT
 (9 9 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (3 3 (:REWRITE DEFAULT-+-1))
 )
(R1CS::R1CS-CONSTRAINTP-OF-MAKE-PRODUCT-CONSTRAINT
 (9 9 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (3 3 (:REWRITE DEFAULT-+-1))
 )
(R1CS::MAKE-PRODUCT-CONSTRAINT-CORRECT
 (33 33 (:REWRITE R1CS::VALUATION-BINDSP-WHEN-VALUATION-BINDS-ALLP))
 (17 17 (:REWRITE R1CS::R1CS-VALUATIONP-WHEN-NOT-CONSP))
 (15 15 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (15 15 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (14 7 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (12 12 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG2))
 (12 12 (:REWRITE PFIELD::ADD-SUBST-CONSTANT-ARG1))
 (12 6 (:REWRITE IFIX-WHEN-NOT-INTEGERP-UNLIMITED))
 (12 6 (:REWRITE DEFAULT-<-1))
 (12 6 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (11 7 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (9 9 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (9 9 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (9 9 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (9 9 (:REWRITE PFIELD::MUL-OF--1-BECOMES-NEG-ALT))
 (9 9 (:REWRITE DEFAULT-CAR))
 (9 9 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (9 6 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (7 7 (:REWRITE PFIELD::MUL-COMMUTATIVE))
 (6 6 (:REWRITE PFIELD::FEP-WHEN-FE-LISTP-AND-MEMBER-EQUAL))
 (6 6 (:REWRITE PFIELD::FEP-WHEN-CONSTANT))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE PFIELD::ADD-COMMUTATIVE-WHEN-CONSTANT))
 (3 3 (:TYPE-PRESCRIPTION R1CS::DOT-PRODUCT))
 (3 3 (:REWRITE NOT-PRIMEP-WHEN-DIVIDES))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS-ALT))
 (2 2 (:REWRITE PFIELD::EQUAL-OF-MUL-CONSTANTS))
 )
