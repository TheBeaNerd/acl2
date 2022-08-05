(BYTE-TO-BITS-LITTLE)
(ALL-UNSIGNED-BYTE-P-OF-BYTE-TO-BITS-LITTLE
 (16 16 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (16 8 (:REWRITE GETBIT-WHEN-NOT-1))
 (16 8 (:REWRITE GETBIT-WHEN-NOT-0))
 (16 8 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (9 9 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (9 9 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (9 9 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (8 8 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (8 8 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (8 8 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (8 8 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (8 8 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (5 1 (:REWRITE GETBIT-IDENTITY))
 (3 1 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (1 1 (:TYPE-PRESCRIPTION BITP))
 (1 1 (:REWRITE GETBIT-IDENTITY-FREE))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:DEFINITION BITP))
 )
(ALL-INTEGERP-OF-BYTE-TO-BITS-LITTLE
 (16 8 (:REWRITE GETBIT-WHEN-NOT-1))
 (16 8 (:REWRITE GETBIT-WHEN-NOT-0))
 (16 8 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (10 10 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (8 8 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (8 8 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (8 8 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (8 8 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (8 8 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (8 8 (:REWRITE ALL-UNSIGNED-BYTE-P-IMPLIES-ALL-INTEGERP))
 (8 8 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (5 1 (:REWRITE GETBIT-IDENTITY))
 (3 1 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (1 1 (:TYPE-PRESCRIPTION BITP))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE GETBIT-IDENTITY-FREE))
 (1 1 (:DEFINITION BITP))
 )
(LEN-OF-BYTE-TO-BITS-LITTLE
 (72 72 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (72 36 (:REWRITE GETBIT-WHEN-NOT-1))
 (72 36 (:REWRITE GETBIT-WHEN-NOT-0))
 (72 36 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (38 38 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (36 36 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (36 36 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (36 36 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (36 36 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (36 36 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (14 7 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-+-1))
 (5 1 (:REWRITE GETBIT-IDENTITY))
 (3 1 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (1 1 (:TYPE-PRESCRIPTION BITP))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (1 1 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE GETBIT-IDENTITY-FREE))
 (1 1 (:DEFINITION BITP))
 )
(BYTE-TO-BITS-LITTLE-OF-BVCHOP
 (360 3 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (352 3 (:DEFINITION BITP))
 (127 8 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (108 4 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (91 4 (:LINEAR BVCHOP-UPPER-BOUND))
 (85 17 (:REWRITE BVCHOP-IDENTITY))
 (66 66 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (48 48 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (48 24 (:REWRITE GETBIT-WHEN-NOT-1))
 (48 24 (:REWRITE GETBIT-WHEN-NOT-0))
 (48 24 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (48 4 (:DEFINITION EXPT))
 (27 27 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (24 24 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (24 24 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (24 24 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (24 24 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (21 21 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (21 21 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (21 3 (:REWRITE GETBIT-IDENTITY))
 (17 17 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (17 17 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (17 17 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (17 17 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (17 17 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (17 17 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (17 17 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (17 17 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (17 17 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (16 16 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (16 4 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (14 10 (:REWRITE DEFAULT-+-2))
 (13 9 (:REWRITE DEFAULT-<-1))
 (12 12 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (12 12 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (12 4 (:REWRITE DEFAULT-*-2))
 (12 4 (:REWRITE COMMUTATIVITY-OF-+))
 (10 10 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE GETBIT-OF-BVCHOP-TOO-HIGH))
 (5 1 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-*-1))
 (3 3 (:TYPE-PRESCRIPTION BITP))
 (3 3 (:REWRITE GETBIT-IDENTITY-FREE))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP))
 )
(NTH-OF-BYTE-TO-BITS-LITTLE
 (82 41 (:REWRITE GETBIT-WHEN-NOT-1))
 (82 41 (:REWRITE GETBIT-WHEN-NOT-0))
 (82 41 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (41 41 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (41 41 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (41 41 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (41 41 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (41 41 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (25 5 (:REWRITE GETBIT-IDENTITY))
 (15 15 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-+-1))
 (15 5 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE NTH-OF-CONS-CONSTANT-VERSION))
 (5 5 (:TYPE-PRESCRIPTION BITP))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (5 5 (:REWRITE GETBIT-IDENTITY-FREE))
 (5 5 (:DEFINITION BITP))
 (2 1 (:REWRITE NTH-WHEN-ZP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(CAR-OF-BYTE-TO-BITS-LITTLE
 (18 9 (:REWRITE GETBIT-WHEN-NOT-1))
 (18 9 (:REWRITE GETBIT-WHEN-NOT-0))
 (18 9 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (10 2 (:REWRITE GETBIT-IDENTITY))
 (9 9 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (9 9 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (9 9 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (9 9 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (9 9 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (6 2 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 2 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (2 2 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE GETBIT-IDENTITY-FREE))
 (2 2 (:DEFINITION BITP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
