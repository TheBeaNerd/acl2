(ALL-JAVA-CHARP)
(JVM::CODE-CHAR-LIST
 (24 3 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (22 1 (:REWRITE BVCHOP-IDENTITY))
 (20 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE BOUND-WHEN-USB))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (2 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(JVM::CHAR-LIST-TO-STRING
 (230 3 (:REWRITE DEFAULT-CODE-CHAR))
 (126 9 (:REWRITE BVCHOP-IDENTITY))
 (79 3 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (79 3 (:LINEAR BVCHOP-UPPER-BOUND))
 (72 9 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (48 12 (:REWRITE DEFAULT-<-1))
 (26 26 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (24 3 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (18 18 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (18 9 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (12 12 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (12 12 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (12 12 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (12 11 (:REWRITE DEFAULT-CAR))
 (11 10 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (9 9 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (9 9 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (9 9 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (9 9 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (9 9 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (9 9 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (9 9 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (9 9 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (9 9 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (9 3 (:REWRITE BVCHOP-BOUND))
 (6 6 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (6 6 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (6 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:REWRITE BOUND-WHEN-USB))
 )
(JVM::CHAR-CODE-LIST
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(JVM::CHAR-CODE-LIST-IFF
 (5 5 (:REWRITE DEFAULT-CHAR-CODE))
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(JVM::STRING-TO-CHAR-LIST)
(JVM::EQUAL-NIL-STRING-TO-CHAR-LIST-HELPER
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(JVM::EQUAL-NIL-STRING-TO-CHAR-LIST
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (4 1 (:DEFINITION JVM::CHAR-CODE-LIST))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE DEFAULT-CHAR-CODE))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(JVM::CODE-CHAR-LIST-OF-CHAR-CODE-LIST
 (312 4 (:REWRITE DEFAULT-CODE-CHAR))
 (112 3 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (112 3 (:LINEAR BVCHOP-UPPER-BOUND))
 (99 9 (:DEFINITION UNSIGNED-BYTE-P))
 (90 9 (:DEFINITION INTEGER-RANGE-P))
 (68 32 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-<-2))
 (27 3 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (26 26 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (18 18 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (18 9 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (14 14 (:REWRITE BOUND-WHEN-USB))
 (13 13 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (12 12 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 12 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (12 12 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (12 11 (:REWRITE DEFAULT-CAR))
 (10 10 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (10 9 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (9 9 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (9 9 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (9 9 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (9 9 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (9 9 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (9 9 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (9 9 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (9 3 (:REWRITE BVCHOP-BOUND))
 (6 6 (:REWRITE DEFAULT-CHAR-CODE))
 (6 6 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (6 6 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (6 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(JVM::CHAR-LIST-TO-STRING-OF-STRING-TO-CHAR-LIST
 (4 1 (:DEFINITION JVM::CHAR-CODE-LIST))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-3))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE DEFAULT-CHAR-CODE))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
