(PFIELD::MUL$NOT-NORMALIZED)
(PFIELD::MUL-CONSTANT-OPENER)
(PFIELD::ADD$NOT-NORMALIZED)
(PFIELD::ADD-CONSTANT-OPENER)
(PFIELD::FEP$NOT-NORMALIZED)
(PFIELD::FEP-CONSTANT-OPENER)
(PFIELD::INTEGERP-OF-ADD)
(PFIELD::RATIONALP-OF-ADD)
(PFIELD::INTEGERP-OF-SUB)
(PFIELD::RATIONALP-OF-SUB)
(PFIELD::INTEGERP-OF-NEG)
(PFIELD::RATIONALP-OF-NEG)
(PFIELD::INTEGERP-OF-MUL)
(PFIELD::RATIONALP-OF-MUL)
(PFIELD::INTEGERP-OF-POW)
(PFIELD::RATIONALP-OF-POW)
(PFIELD::INTEGERP-OF-INV)
(PFIELD::RATIONALP-OF-INV)
(PFIELD::INTEGERP-OF-DIV)
(PFIELD::RATIONALP-OF-DIV)
(PFIELD::ADD-COMMUTATIVE-AXE
 (3 3 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (3 3 (:REWRITE PFIELD::ADD-CONSTANT-OPENER))
 (2 2 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (2 2 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 )
(PFIELD::ADD-COMMUTATIVE-2-AXE
 (7 5 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (6 6 (:REWRITE PFIELD::ADD-OF-CONSTANTS))
 (6 6 (:REWRITE PFIELD::ADD-CONSTANT-OPENER))
 (5 5 (:REWRITE PFIELD::ADD-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (5 5 (:REWRITE PFIELD::ADD-COMMUTATIVE))
 (3 3 (:REWRITE PFIELD::ADD-OF-ADD-COMBINE-CONSTANTS))
 )
(PFIELD::MUL-COMMUTATIVE-AXE
 (3 3 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (3 3 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (3 3 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (3 3 (:REWRITE PFIELD::MUL-CONSTANT-OPENER))
 (2 2 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (2 2 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 )
(PFIELD::MUL-COMMUTATIVE-2-AXE
 (7 5 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG2-CHEAP))
 (6 6 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG2))
 (6 6 (:REWRITE PFIELD::MUL-WHEN-EQUAL-OF-MOD-SUBST-ARG1))
 (6 6 (:REWRITE PFIELD::MUL-WHEN-CONSTANT-REDUCE-ARG1))
 (6 6 (:REWRITE PFIELD::MUL-CONSTANT-OPENER))
 (5 5 (:REWRITE PFIELD::MUL-WHEN-NOT-INTEGERP-ARG1-CHEAP))
 (5 5 (:REWRITE PFIELD::MUL-COMMUTATIVE))
 (3 3 (:REWRITE PFIELD::MUL-OF-MUL-COMBINE-CONSTANTS))
 )
(EQUAL-SELF)
(PRIMEP$-KNOWN-BOOLEANS-JUSTIFICATION)
(FEP$-KNOWN-BOOLEANS-JUSTIFICATION)
