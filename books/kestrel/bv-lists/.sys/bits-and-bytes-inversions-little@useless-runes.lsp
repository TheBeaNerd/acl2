(BITS-TO-BYTE-LITTLE-OF-BYTE-TO-BITS-LITTLE
 (50 10 (:REWRITE BVCHOP-IDENTITY))
 (30 30 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (17 1 (:LINEAR BVCHOP-UPPER-BOUND))
 (16 8 (:REWRITE GETBIT-WHEN-NOT-1))
 (16 8 (:REWRITE GETBIT-WHEN-NOT-0))
 (16 8 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (13 13 (:REWRITE BVCAT-WHEN-EQUAL-OF-GETBIT-0-HIGH))
 (13 13 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (13 13 (:REWRITE BVCAT-SUBST-1))
 (13 13 (:REWRITE BVCAT-OF-GETBIT-HIGH-TIGHTEN))
 (13 13 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (13 13 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (11 11 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (11 11 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (10 10 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (10 10 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (10 10 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (10 10 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (10 10 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (10 10 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (10 10 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (10 10 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (10 10 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (10 10 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (8 8 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (8 8 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (8 8 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (8 8 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (6 6 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (6 6 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (5 1 (:REWRITE GETBIT-IDENTITY))
 (4 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (3 1 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION BITP))
 (1 1 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (1 1 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (1 1 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (1 1 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (1 1 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (1 1 (:REWRITE SLICE-OUT-OF-ORDER))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE GETBIT-IDENTITY-FREE))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE BVCAT-WHEN-EQUAL-OF-GETBIT-0-LOW))
 (1 1 (:DEFINITION BITP))
 )
(BYTE-TO-BITS-LITTLE-OF-BITS-TO-BYTE-LITTLE
 (8914 1556 (:REWRITE LEN-OF-CDR))
 (4500 62 (:REWRITE DEFAULT-CAR))
 (3743 128 (:REWRITE DEFAULT-CDR))
 (2486 2220 (:REWRITE DEFAULT-+-2))
 (2220 2220 (:REWRITE DEFAULT-+-1))
 (1442 8 (:REWRITE TAKE-DOES-NOTHING))
 (794 794 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (743 36 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (736 736 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (636 36 (:DEFINITION MEMBER-EQUAL))
 (233 233 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (176 176 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (161 119 (:REWRITE DEFAULT-<-2))
 (142 119 (:REWRITE DEFAULT-<-1))
 (132 23 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (96 96 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (54 54 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (36 36 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (28 7 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (24 8 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (23 23 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (21 7 (:REWRITE INTEGERP-OF-NTH-WHEN-ALL-INTEGERP))
 (16 16 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (16 8 (:REWRITE GETBIT-WHEN-NOT-1))
 (16 8 (:REWRITE GETBIT-WHEN-NOT-0))
 (15 7 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (8 8 (:TYPE-PRESCRIPTION BITP))
 (8 8 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (8 8 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (8 8 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (8 8 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (8 8 (:REWRITE GETBIT-IDENTITY-FREE))
 (8 8 (:DEFINITION BITP))
 (7 7 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (7 7 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (7 7 (:REWRITE BVCAT-WHEN-EQUAL-OF-GETBIT-0-HIGH))
 (7 7 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (7 7 (:REWRITE BVCAT-SUBST-1))
 (7 7 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (7 7 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (7 7 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (6 6 (:TYPE-PRESCRIPTION NATP-OF-BVCAT-TYPE))
 (6 6 (:REWRITE BVCAT-COMBINE-CONSTANTS))
 (2 1 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (1 1 (:REWRITE BVCAT-WHEN-EQUAL-OF-GETBIT-0-LOW))
 )
(BYTES-TO-BITS-LITTLE-OF-BITS-TO-BYTES-LITTLE
 (621 28 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (368 12 (:REWRITE LEN-OF-BITS-TO-BYTES-LITTLE))
 (347 4 (:DEFINITION BINARY-APPEND))
 (331 4 (:REWRITE CAR-OF-BYTE-TO-BITS-LITTLE))
 (243 8 (:REWRITE DEFAULT-CAR))
 (232 4 (:DEFINITION CEILING))
 (211 4 (:REWRITE GETBIT-IDENTITY))
 (142 11 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (128 8 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (127 4 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (89 77 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (88 15 (:REWRITE DEFAULT-CDR))
 (74 52 (:REWRITE DEFAULT-<-2))
 (72 8 (:REWRITE CEILING-OF-LEN-WHEN-LEN-MULT-OF-8P-CHEAP))
 (66 6 (:REWRITE TAKE-DOES-NOTHING))
 (64 12 (:REWRITE COMMUTATIVITY-OF-*))
 (63 28 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (56 44 (:REWRITE DEFAULT-+-2))
 (52 52 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (52 52 (:REWRITE DEFAULT-<-1))
 (52 16 (:REWRITE COMMUTATIVITY-OF-+))
 (52 4 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (48 44 (:REWRITE DEFAULT-+-1))
 (48 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (44 4 (:REWRITE LEN-OF-NTHCDR))
 (40 12 (:DEFINITION NFIX))
 (36 28 (:REWRITE DEFAULT-*-2))
 (36 28 (:REWRITE DEFAULT-*-1))
 (36 4 (:DEFINITION MEMBER-EQUAL))
 (36 4 (:DEFINITION BITP))
 (28 28 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (24 4 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (22 22 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (20 20 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (20 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (20 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (20 4 (:REWRITE DISTRIBUTIVITY))
 (13 13 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (12 12 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (12 4 (:REWRITE +-OF---AND-0))
 (11 11 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (8 8 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (8 8 (:TYPE-PRESCRIPTION BYTE-TO-BITS-LITTLE))
 (8 8 (:DEFINITION IFIX))
 (8 4 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (8 4 (:REWRITE GETBIT-WHEN-NOT-1))
 (8 4 (:REWRITE GETBIT-WHEN-NOT-0))
 (8 4 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (7 7 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (7 7 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (7 7 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (4 4 (:TYPE-PRESCRIPTION BITP))
 (4 4 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (4 4 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (4 4 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (4 4 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (4 4 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (4 4 (:REWRITE GETBIT-IDENTITY-FREE))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-NTHCDR-LONGER))
 )
(BITS-TO-BYTES-LITTLE-OF-BYTES-TO-BITS-LITTLE
 (6333 355 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (4484 109 (:REWRITE CAR-OF-BYTE-TO-BITS-LITTLE))
 (2455 109 (:REWRITE GETBIT-IDENTITY))
 (2224 32 (:REWRITE LEN-OF-BITS-TO-BYTES-LITTLE))
 (1865 121 (:REWRITE DEFAULT-CAR))
 (1856 32 (:DEFINITION CEILING))
 (1787 38 (:REWRITE NTHCDR-OF-8-AND-BYTES-TO-BITS-LITTLE))
 (1444 91 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (1210 132 (:REWRITE LEN-OF-BYTES-TO-BITS-LITTLE))
 (1136 780 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1076 64 (:REWRITE CONSP-OF-BITS-TO-BYTES-LITTLE))
 (1036 246 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (1024 48 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (845 157 (:REWRITE LEN-OF-CDR))
 (794 44 (:REWRITE TAKE-DOES-NOTHING))
 (660 402 (:REWRITE DEFAULT-<-2))
 (627 307 (:REWRITE DEFAULT-CDR))
 (574 463 (:REWRITE DEFAULT-+-2))
 (550 78 (:REWRITE CONSP-OF-BYTES-TO-BITS-LITTLE))
 (511 463 (:REWRITE DEFAULT-+-1))
 (497 109 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (496 91 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (450 402 (:REWRITE DEFAULT-<-1))
 (422 84 (:REWRITE DISTRIBUTIVITY))
 (362 280 (:REWRITE DEFAULT-*-2))
 (338 338 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (333 109 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (320 320 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (296 280 (:REWRITE DEFAULT-*-1))
 (288 80 (:REWRITE COMMUTATIVITY-OF-+))
 (247 247 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (247 109 (:DEFINITION BITP))
 (218 109 (:REWRITE GETBIT-WHEN-NOT-1))
 (218 109 (:REWRITE GETBIT-WHEN-NOT-0))
 (218 109 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (192 48 (:DEFINITION NFIX))
 (192 32 (:REWRITE COMMUTATIVITY-OF-*))
 (182 91 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (132 132 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (118 16 (:REWRITE BYTES-TO-BITS-LITTLE-OF-BITS-TO-BYTES-LITTLE))
 (112 80 (:REWRITE DEFAULT-UNARY-MINUS))
 (109 109 (:TYPE-PRESCRIPTION BITP))
 (109 109 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (109 109 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (109 109 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (109 109 (:REWRITE GETBIT-IDENTITY-FREE))
 (91 91 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (84 44 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (64 48 (:DEFINITION IFIX))
 (57 57 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (48 32 (:REWRITE DEFAULT-NUMERATOR))
 (48 32 (:REWRITE DEFAULT-DENOMINATOR))
 (44 44 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (39 13 (:REWRITE FOLD-CONSTS-IN-+))
 (32 32 (:TYPE-PRESCRIPTION LEN-MULT-OF-8P))
 (14 14 (:REWRITE ALL-UNSIGNED-BYTE-P-OF-BYTES-TO-BITS-LITTLE))
 (13 13 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (12 12 (:REWRITE EQUAL-OF-LEN-AND-0))
 (9 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (8 4 (:REWRITE CEILING-OF-LEN-WHEN-LEN-MULT-OF-8P-CHEAP))
 (4 4 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (4 4 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (3 3 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (3 3 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (3 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (3 3 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (3 3 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (3 3 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (3 3 (:REWRITE BVCHOP-SUBST-CONSTANT))
 )
(BITS-TO-BYTES-LITTLE-OF-BYTE-TO-BITS-LITTLE
 (3 2 (:REWRITE DEFAULT-CDR))
 (3 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (2 1 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (1 1 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (1 1 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 )
