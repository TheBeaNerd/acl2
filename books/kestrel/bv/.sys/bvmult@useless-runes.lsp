(BVMULT)
(INTEGERP-OF-BVMULT)
(NATP-OF-BVMULT)
(BVMULT-OF-0-ARG1)
(BVMULT-OF-0-ARG2)
(BVMULT-OF-0-ARG3
 (4 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (3 1 (:REWRITE BVCHOP-IDENTITY))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (2 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (2 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(BVMULT-OF-1-ARG2
 (88 4 (:DEFINITION EXPT))
 (24 8 (:REWRITE DEFAULT-*-2))
 (24 8 (:REWRITE COMMUTATIVITY-OF-+))
 (24 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (22 17 (:REWRITE DEFAULT-<-2))
 (21 17 (:REWRITE DEFAULT-<-1))
 (21 6 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (20 4 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (18 18 (:TYPE-PRESCRIPTION FIX))
 (18 6 (:REWRITE BVCHOP-IDENTITY))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 (16 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (12 12 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (12 6 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (12 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (12 4 (:DEFINITION NATP))
 (8 8 (:REWRITE DEFAULT-*-1))
 (8 8 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (8 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (4 4 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOPS-SAME-WHEN-BVCHOPS-SAME))
 (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 )
(BVMULT-OF-BVCHOP-ARG3
 (657 11 (:REWRITE <-OF-*-AND-0))
 (624 48 (:DEFINITION EXPT))
 (472 158 (:REWRITE BVCHOP-IDENTITY))
 (314 314 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (301 15 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (295 15 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (216 216 (:TYPE-PRESCRIPTION IFIX))
 (204 183 (:REWRITE DEFAULT-<-1))
 (202 183 (:REWRITE DEFAULT-<-2))
 (188 86 (:REWRITE DEFAULT-*-2))
 (172 60 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (168 120 (:REWRITE DEFAULT-+-2))
 (158 158 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (144 48 (:REWRITE COMMUTATIVITY-OF-+))
 (120 120 (:REWRITE DEFAULT-+-1))
 (96 60 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (95 95 (:TYPE-PRESCRIPTION POSP))
 (93 86 (:REWRITE DEFAULT-*-1))
 (77 77 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (60 60 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (60 60 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (48 48 (:REWRITE ZIP-OPEN))
 (30 30 (:LINEAR <-OF-*-AND-*-LINEAR))
 (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (12 12 (:REWRITE BVCHOP-OF-*-OF-BVCHOP))
 (11 11 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (2 2 (:REWRITE BVCHOP-BOUND))
 (2 2 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOPS-SAME-WHEN-BVCHOPS-SAME))
 (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 )
(BVMULT-COMMUTATIVE
 (276 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (184 184 (:TYPE-PRESCRIPTION IFIX))
 (140 4 (:REWRITE <-OF-*-AND-0))
 (88 4 (:DEFINITION EXPT))
 (54 37 (:REWRITE DEFAULT-<-2))
 (49 37 (:REWRITE DEFAULT-<-1))
 (32 4 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (32 4 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (27 11 (:REWRITE DEFAULT-*-2))
 (24 8 (:REWRITE COMMUTATIVITY-OF-+))
 (21 6 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (20 4 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 (16 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 6 (:REWRITE BVCHOP-IDENTITY))
 (14 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (14 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (12 6 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (12 4 (:DEFINITION NATP))
 (11 11 (:REWRITE DEFAULT-*-1))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (8 8 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (8 8 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (8 8 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (8 8 (:LINEAR <-OF-*-AND-*-LINEAR))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE ZIP-OPEN))
 (4 4 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(BVMULT-OF-BVCHOP-ARG2
 (8 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (6 2 (:REWRITE BVCHOP-IDENTITY))
 (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (4 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(GETBIT-0-OF-BVMULT
 (1362 9 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (1323 8 (:DEFINITION BITP))
 (420 420 (:TYPE-PRESCRIPTION IFIX))
 (330 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (220 6 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (191 6 (:LINEAR BVCHOP-UPPER-BOUND))
 (158 6 (:REWRITE <-OF-*-AND-0))
 (146 26 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (146 26 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (144 12 (:DEFINITION EXPT))
 (112 92 (:REWRITE DEFAULT-<-2))
 (112 92 (:REWRITE DEFAULT-<-1))
 (67 5 (:REWRITE EQUAL-OF-0-AND-*))
 (52 52 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (52 52 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (52 52 (:LINEAR <-OF-*-AND-*-LINEAR))
 (43 9 (:REWRITE GETBIT-IDENTITY))
 (42 30 (:REWRITE DEFAULT-+-2))
 (40 40 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (40 40 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (39 13 (:REWRITE BVCHOP-IDENTITY))
 (38 38 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (38 14 (:REWRITE DEFAULT-*-2))
 (36 12 (:REWRITE COMMUTATIVITY-OF-+))
 (30 30 (:REWRITE DEFAULT-+-1))
 (29 13 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (29 13 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (26 26 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (26 26 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (26 26 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (26 26 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (18 10 (:DEFINITION FIX))
 (18 9 (:REWRITE GETBIT-WHEN-NOT-1))
 (18 9 (:REWRITE GETBIT-WHEN-NOT-0))
 (18 9 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (14 14 (:REWRITE DEFAULT-*-1))
 (14 6 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (13 13 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (13 13 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (13 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (13 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (13 13 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (13 13 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (13 13 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (12 12 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (10 10 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (9 9 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (9 9 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (9 9 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (9 9 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (9 9 (:REWRITE GETBIT-IDENTITY-FREE))
 (9 3 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (9 3 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP))
 (8 8 (:TYPE-PRESCRIPTION BITP))
 (6 6 (:REWRITE GETBIT-0-OF-TIMES-CONSTANT))
 (6 6 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (3 3 (:REWRITE GETBIT-OF-BVCHOP-TOO-HIGH))
 )
(BVMULT-1-1)
(BVCHOP-OF-BVMULT
 (250 250 (:TYPE-PRESCRIPTION IFIX))
 (145 49 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (133 60 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (130 10 (:DEFINITION EXPT))
 (112 103 (:REWRITE DEFAULT-<-2))
 (112 103 (:REWRITE DEFAULT-<-1))
 (111 49 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (105 3 (:REWRITE <-OF-*-AND-0))
 (69 69 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (67 67 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (60 60 (:TYPE-PRESCRIPTION POSP))
 (60 60 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (49 49 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (49 49 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (45 15 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (39 13 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP))
 (35 25 (:REWRITE DEFAULT-+-2))
 (32 12 (:REWRITE DEFAULT-*-2))
 (30 10 (:REWRITE COMMUTATIVITY-OF-+))
 (25 25 (:REWRITE DEFAULT-+-1))
 (24 3 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (24 3 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (12 12 (:REWRITE DEFAULT-*-1))
 (10 10 (:REWRITE ZIP-OPEN))
 (6 6 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (6 6 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (6 6 (:LINEAR <-OF-*-AND-*-LINEAR))
 (3 3 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 )
(UNSIGNED-BYTE-P-OF-BVMULT
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (3 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (3 1 (:REWRITE BVCHOP-IDENTITY))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(BVMULT-WHEN-SIZE-IS-NOT-POSITIVE)
(BVCHOP-OF-BVMULT2
 (52 4 (:DEFINITION EXPT))
 (22 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (17 17 (:REWRITE DEFAULT-<-2))
 (17 17 (:REWRITE DEFAULT-<-1))
 (14 10 (:REWRITE DEFAULT-+-2))
 (12 4 (:REWRITE DEFAULT-*-2))
 (12 4 (:REWRITE COMMUTATIVITY-OF-+))
 (10 10 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (4 4 (:REWRITE ZIP-OPEN))
 (4 4 (:REWRITE DEFAULT-*-1))
 )
(BVMULT-ASSOCIATIVE
 (276 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (184 184 (:TYPE-PRESCRIPTION IFIX))
 (140 4 (:REWRITE <-OF-*-AND-0))
 (88 4 (:DEFINITION EXPT))
 (54 37 (:REWRITE DEFAULT-<-2))
 (49 37 (:REWRITE DEFAULT-<-1))
 (32 4 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (32 4 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (31 15 (:REWRITE DEFAULT-*-2))
 (24 8 (:REWRITE COMMUTATIVITY-OF-+))
 (21 6 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (20 4 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 (16 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 6 (:REWRITE BVCHOP-IDENTITY))
 (15 15 (:REWRITE DEFAULT-*-1))
 (14 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (14 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (12 6 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (12 4 (:DEFINITION NATP))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (8 8 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (8 8 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (8 8 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (8 8 (:LINEAR <-OF-*-AND-*-LINEAR))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE ZIP-OPEN))
 (4 4 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (3 3 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 )
(BVMULT-COMMUTATIVE-2
 (17 11 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(BVMULT-COMBINE-CONSTANTS)
(BVMULT-COMMUTE-CONSTANT
 (6 3 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(BVMULT-WHEN-ARG1-IS-NOT-AN-INTEGER
 (69 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (46 46 (:TYPE-PRESCRIPTION IFIX))
 (35 1 (:REWRITE <-OF-*-AND-0))
 (22 1 (:DEFINITION EXPT))
 (13 9 (:REWRITE DEFAULT-<-2))
 (12 9 (:REWRITE DEFAULT-<-1))
 (8 1 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (8 1 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (6 2 (:REWRITE DEFAULT-*-2))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (6 2 (:REWRITE BVCHOP-IDENTITY))
 (5 1 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (4 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (3 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (3 1 (:DEFINITION NATP))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (2 2 (:LINEAR <-OF-*-AND-*-LINEAR))
 (2 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(BVMULT-WHEN-ARG2-IS-NOT-AN-INTEGER
 (69 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (46 46 (:TYPE-PRESCRIPTION IFIX))
 (35 1 (:REWRITE <-OF-*-AND-0))
 (22 1 (:DEFINITION EXPT))
 (13 9 (:REWRITE DEFAULT-<-2))
 (12 9 (:REWRITE DEFAULT-<-1))
 (8 1 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (8 1 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (7 3 (:REWRITE DEFAULT-*-2))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (6 2 (:REWRITE BVCHOP-IDENTITY))
 (5 1 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (4 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (4 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (4 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (3 3 (:REWRITE DEFAULT-*-1))
 (3 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (3 1 (:DEFINITION NATP))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (2 2 (:LINEAR <-OF-*-AND-*-LINEAR))
 (2 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(BVMULT-NON-NEGATIVE)
(BVMULT-OF-BVCHOP-1-BETTER
 (1076 24 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (1064 24 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (1040 80 (:DEFINITION EXPT))
 (1014 16 (:REWRITE <-OF-*-AND-0))
 (785 263 (:REWRITE BVCHOP-IDENTITY))
 (522 522 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (480 480 (:TYPE-PRESCRIPTION IFIX))
 (422 142 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (404 362 (:REWRITE DEFAULT-<-1))
 (394 362 (:REWRITE DEFAULT-<-2))
 (326 145 (:REWRITE DEFAULT-*-2))
 (280 200 (:REWRITE DEFAULT-+-2))
 (263 263 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (263 263 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (240 80 (:REWRITE COMMUTATIVITY-OF-+))
 (228 142 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (205 205 (:TYPE-PRESCRIPTION POSP))
 (200 200 (:REWRITE DEFAULT-+-1))
 (160 145 (:REWRITE DEFAULT-*-1))
 (156 156 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (142 142 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (142 142 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (80 80 (:REWRITE ZIP-OPEN))
 (48 48 (:LINEAR <-OF-*-AND-*-LINEAR))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (16 16 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE BVCHOP-OF-*-OF-BVCHOP))
 (4 4 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (4 4 (:REWRITE BVCHOP-BOUND))
 (4 4 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOPS-SAME-WHEN-BVCHOPS-SAME))
 (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 )
(BVMULT-OF-BVCHOP-2-BETTER
 (1076 24 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (1064 24 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (1040 80 (:DEFINITION EXPT))
 (1014 16 (:REWRITE <-OF-*-AND-0))
 (785 263 (:REWRITE BVCHOP-IDENTITY))
 (522 522 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (480 480 (:TYPE-PRESCRIPTION IFIX))
 (422 142 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (404 362 (:REWRITE DEFAULT-<-1))
 (394 362 (:REWRITE DEFAULT-<-2))
 (329 147 (:REWRITE DEFAULT-*-2))
 (280 200 (:REWRITE DEFAULT-+-2))
 (263 263 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (263 263 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (240 80 (:REWRITE COMMUTATIVITY-OF-+))
 (228 142 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (205 205 (:TYPE-PRESCRIPTION POSP))
 (200 200 (:REWRITE DEFAULT-+-1))
 (162 147 (:REWRITE DEFAULT-*-1))
 (156 156 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (142 142 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (142 142 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (80 80 (:REWRITE ZIP-OPEN))
 (48 48 (:LINEAR <-OF-*-AND-*-LINEAR))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (16 16 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (14 14 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE BVCHOP-OF-*-OF-BVCHOP))
 (4 4 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (4 4 (:REWRITE BVCHOP-BOUND))
 (4 4 (:REWRITE <-OF-BVCHOP-WHEN-<-OF-BVCHOP-BIGGER))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOPS-SAME-WHEN-BVCHOPS-SAME))
 (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 )
(BVMULT-SUBST2-CONSTANT-VERSION
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (3 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (3 1 (:REWRITE BVCHOP-IDENTITY))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (2 2 (:REWRITE BVMULT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVMULT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(BVMULT-SUBST2-ALT-CONSTANT-VERSION
 (6 4 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE BVMULT-SUBST2-CONSTANT-VERSION))
 (4 4 (:REWRITE BVMULT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (4 4 (:REWRITE BVMULT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (3 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (3 1 (:REWRITE BVCHOP-IDENTITY))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(BVCHOP-OF-*-BECOMES-BVMULT
 (192 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (92 92 (:TYPE-PRESCRIPTION IFIX))
 (88 4 (:REWRITE <-OF-*-AND-0))
 (88 4 (:DEFINITION EXPT))
 (48 37 (:REWRITE DEFAULT-<-2))
 (43 37 (:REWRITE DEFAULT-<-1))
 (26 10 (:REWRITE DEFAULT-*-2))
 (24 8 (:REWRITE COMMUTATIVITY-OF-+))
 (22 4 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (22 4 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (21 6 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (20 4 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 (16 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 6 (:REWRITE BVCHOP-IDENTITY))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (12 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (12 6 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (12 4 (:DEFINITION NATP))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (10 10 (:REWRITE DEFAULT-*-1))
 (10 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (10 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (8 8 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (8 8 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (8 8 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (8 8 (:LINEAR <-OF-*-AND-*-LINEAR))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (6 6 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (6 6 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE ZIP-OPEN))
 (4 4 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(BVMULT-EQUAL-BVCHOP-TIMES-REWRITE
 (4 2 (:REWRITE BVCHOP-IDENTITY))
 (2 2 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (2 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (2 2 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (2 2 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 2 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(EQUAL-OF-BVMULT-AND-*
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 (3 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (3 1 (:REWRITE BVCHOP-IDENTITY))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(EQUAL-OF-BVMULT-AND-*-ALT
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 (3 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (3 1 (:REWRITE BVCHOP-IDENTITY))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(BVMULT-OF-EXPT
 (91 7 (:DEFINITION EXPT))
 (54 54 (:TYPE-PRESCRIPTION IFIX))
 (48 2 (:REWRITE <-OF-*-AND-0))
 (30 27 (:REWRITE DEFAULT-<-2))
 (30 27 (:REWRITE DEFAULT-<-1))
 (26 10 (:REWRITE DEFAULT-*-2))
 (24 8 (:REWRITE BVCHOP-IDENTITY))
 (21 7 (:REWRITE COMMUTATIVITY-OF-+))
 (18 18 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (18 16 (:REWRITE DEFAULT-+-2))
 (18 6 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (16 16 (:REWRITE DEFAULT-+-1))
 (14 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (14 6 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (13 13 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (13 2 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (13 2 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (12 10 (:REWRITE DEFAULT-*-1))
 (8 8 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (7 7 (:REWRITE ZIP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION POSP))
 (6 6 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (6 6 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (6 6 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (4 4 (:LINEAR <-OF-*-AND-*-LINEAR))
 (3 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (2 2 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(BVMULT-OF-EXPT-ALT
 (13 1 (:DEFINITION EXPT))
 (8 2 (:REWRITE BVMULT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (8 2 (:REWRITE BVMULT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (7 7 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (7 7 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (4 2 (:REWRITE BVMULT-WHEN-SIZE-IS-NOT-POSITIVE))
 (3 1 (:REWRITE DEFAULT-*-2))
 (3 1 (:REWRITE COMMUTATIVITY-OF-+))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE BVMULT-SUBST2-CONSTANT-VERSION))
 (2 2 (:REWRITE BVMULT-SUBST2-ALT-CONSTANT-VERSION))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(GETBIT-OF-*-BECOMES-GETBIT-OF-BVMULT
 (22 11 (:REWRITE GETBIT-WHEN-NOT-1))
 (22 11 (:REWRITE GETBIT-WHEN-NOT-0))
 (22 11 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (16 8 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (11 11 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (11 11 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (11 11 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (11 11 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (9 3 (:REWRITE GETBIT-OF-BVCHOP-TOO-HIGH))
 (8 8 (:TYPE-PRESCRIPTION IFIX))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE BVCHOP-IDENTITY))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
(SLICE-OF-*-BECOMES-SLICE-OF-BVMULT
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (9 3 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (9 3 (:REWRITE SLICE-OUT-OF-ORDER))
 (9 3 (:LINEAR SLICE-UPPER-BOUND-LINEAR))
 (4 4 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (4 4 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (4 4 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (4 4 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (4 4 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (3 3 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (3 3 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE BVCHOP-IDENTITY))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (1 1 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 )
