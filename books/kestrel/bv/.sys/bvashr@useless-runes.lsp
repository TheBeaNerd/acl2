(BVASHR
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(INTEGERP-OF-BVASHR)
(NATP-OF-BVASHR)
(BVCHOP-OF-BVASHR
 (178 10 (:DEFINITION EXPT))
 (158 149 (:REWRITE DEFAULT-<-2))
 (149 149 (:REWRITE DEFAULT-<-1))
 (138 15 (:REWRITE BVCAT-WHEN-HIGHSIZE-IS-NOT-POSP))
 (136 126 (:REWRITE DEFAULT-+-2))
 (126 126 (:REWRITE DEFAULT-+-1))
 (77 20 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (63 63 (:TYPE-PRESCRIPTION MIN))
 (47 47 (:TYPE-PRESCRIPTION NATP-OF-BVSHR))
 (42 14 (:REWRITE DEFAULT-*-2))
 (42 14 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (38 38 (:TYPE-PRESCRIPTION POSP))
 (38 38 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (34 34 (:REWRITE DEFAULT-UNARY-MINUS))
 (32 32 (:REWRITE FOLD-CONSTS-IN-+))
 (30 15 (:REWRITE BVCAT-WHEN-LOWVAL-IS-NOT-AN-INTEGER))
 (30 15 (:REWRITE BVCAT-WHEN-HIGHVAL-IS-NOT-AN-INTEGER))
 (29 14 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (29 14 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (27 9 (:DEFINITION MIN))
 (24 15 (:REWRITE BVCAT-WHEN-LOWSIZE-IS-NOT-POSP))
 (21 21 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (21 21 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (21 21 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (21 21 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (21 21 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (20 20 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (20 20 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (18 18 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (18 18 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (18 3 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (17 17 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (16 5 (:LINEAR SLICE-UPPER-BOUND-LINEAR))
 (16 2 (:REWRITE REPEATBIT-BASE))
 (15 15 (:TYPE-PRESCRIPTION REPEATBIT))
 (15 15 (:REWRITE BVCAT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (15 15 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG4))
 (15 15 (:REWRITE BVCAT-NORMALIZE-CONSTANT-ARG2))
 (14 14 (:REWRITE DEFAULT-*-1))
 (14 14 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (14 14 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (14 14 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (14 10 (:REWRITE ZIP-OPEN))
 (12 2 (:REWRITE ZP-OPEN))
 (7 1 (:REWRITE BVSX-WHEN-UNSIGNED-BYTE-P))
 (6 6 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (5 5 (:LINEAR SLICE-UPPER-BOUND-LINEAR-CONSTANT-VERSION))
 (4 4 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (4 2 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (4 2 (:REWRITE GETBIT-WHEN-NOT-1))
 (4 2 (:REWRITE GETBIT-WHEN-NOT-0))
 (4 2 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (2 2 (:TYPE-PRESCRIPTION ZP))
 (2 2 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (2 2 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (2 2 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (2 2 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (2 2 (:LINEAR BVCAT-LOWER-BOUND-LINEAR-ARG4-CONSTANT))
 (2 2 (:LINEAR BVCAT-LOWER-BOUND-LINEAR-ARG2-CONSTANT))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE BVSX-WHEN-SIZES-MATCH))
 (1 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 )
(BVASHR-REWRITE-FOR-CONSTANT-SHIFT-AMOUNT
 (14 2 (:REWRITE BVSX-WHEN-UNSIGNED-BYTE-P))
 (8 6 (:REWRITE DEFAULT-+-2))
 (8 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE BVSX-WHEN-SIZES-MATCH))
 )
(BVASHR-OF-0-ARG2
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE BVSX-WHEN-SIZES-MATCH))
 )
(UNSIGNED-BYTE-P-OF-BVASHR
 (31 1 (:REWRITE BVSX-WHEN-UNSIGNED-BYTE-P))
 (24 1 (:REWRITE UNSIGNED-BYTE-P-OF-SLICE-GEN))
 (11 10 (:REWRITE DEFAULT-+-2))
 (11 10 (:REWRITE DEFAULT-+-1))
 (9 5 (:REWRITE FOLD-CONSTS-IN-+))
 (6 5 (:REWRITE DEFAULT-<-2))
 (6 5 (:REWRITE DEFAULT-<-1))
 (6 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 1 (:REWRITE SLICE-WHEN-LOW-IS-NEGATIVE))
 (4 1 (:REWRITE SLICE-TOO-HIGH-IS-0))
 (4 1 (:REWRITE SLICE-OUT-OF-ORDER))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (3 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 1 (:REWRITE UNICITY-OF-0))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-BVSX))
 (1 1 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE SLICE-WHEN-VAL-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE SLICE-WHEN-BVCHOP-KNOWN))
 (1 1 (:REWRITE SLICE-TOO-HIGH-LEMMA))
 (1 1 (:REWRITE SLICE-SUBST-IN-CONSTANT-ALT))
 (1 1 (:REWRITE SLICE-SUBST-IN-CONSTANT))
 (1 1 (:REWRITE BVSX-WHEN-SIZES-MATCH))
 (1 1 (:DEFINITION FIX))
 )
(BVASHR-OF-BVCHOP
 (14 2 (:REWRITE BVSX-WHEN-UNSIGNED-BYTE-P))
 (8 2 (:REWRITE BVCHOP-IDENTITY))
 (7 7 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE BVSX-WHEN-SIZES-MATCH))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (2 2 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (2 2 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (1 1 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (1 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 )
(BVASHR-CASES-TERM-FN-AUX
 (6 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(BVASHR-CASES-TERM-FN)
(BVASHR-16-CASES
 (74 16 (:REWRITE BVSX-WHEN-UNSIGNED-BYTE-P))
 (38 38 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (32 5 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (21 21 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (21 21 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (17 17 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (16 16 (:REWRITE BVSX-WHEN-SIZES-MATCH))
 (15 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (13 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (13 13 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (13 13 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (11 11 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (11 11 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (11 11 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (8 5 (:REWRITE DEFAULT-<-1))
 (8 2 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (6 1 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (5 5 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(BVASHR-32-CASES
 (138 32 (:REWRITE BVSX-WHEN-UNSIGNED-BYTE-P))
 (54 54 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (33 33 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (32 32 (:REWRITE BVSX-WHEN-SIZES-MATCH))
 (32 5 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (21 21 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (21 21 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (15 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (13 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (13 13 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (13 13 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (11 11 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (11 11 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (11 11 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (8 5 (:REWRITE DEFAULT-<-1))
 (8 2 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (6 1 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (5 5 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(BVASHR-64-CASES
 (266 64 (:REWRITE BVSX-WHEN-UNSIGNED-BYTE-P))
 (86 86 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (65 65 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (64 64 (:REWRITE BVSX-WHEN-SIZES-MATCH))
 (32 5 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (21 21 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (21 21 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (15 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (13 13 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (13 13 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (13 13 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (11 11 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (11 11 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (11 11 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (8 5 (:REWRITE DEFAULT-<-1))
 (8 2 (:REWRITE UNSIGNED-BYTE-P-OF-BVCHOP-WHEN-ALREADY))
 (6 1 (:REWRITE UNSIGNED-BYTE-P-OF-0-ARG1))
 (5 5 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
