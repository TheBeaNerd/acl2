(BYTES-TO-BITS-LITTLE$NOT-NORMALIZED)
(BYTES-TO-BITS-LITTLE-BASE)
(BYTES-TO-BITS-LITTLE-UNROLL)
(LEN-MULT-OF-8P-OF-BYTES-TO-BITS-LITTLE
 (52 4 (:REWRITE MOD-WHEN-MULTIPLE))
 (52 4 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (33 1 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (32 8 (:REWRITE COMMUTATIVITY-OF-*))
 (26 17 (:REWRITE DEFAULT-*-2))
 (25 17 (:REWRITE DEFAULT-*-1))
 (16 8 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (8 4 (:REWRITE MOD-WHEN-<-OF-0))
 (5 1 (:DEFINITION LEN))
 (4 4 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (4 4 (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG2))
 (4 4 (:REWRITE MOD-OF-*-SUBST-CONSTANT-ARG1))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(UNSIGNED-BYTE-LISTP-OF-BYTES-TO-BITS-LITTLE)
