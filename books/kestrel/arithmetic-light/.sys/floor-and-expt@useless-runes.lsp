(FLOOR-OF-EXPT-AND-2
 (76 22 (:REWRITE DEFAULT-*-2))
 (70 2 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (60 2 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (34 22 (:REWRITE DEFAULT-*-1))
 (34 1 (:LINEAR EXPT-HALF-LINEAR))
 (27 27 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (27 27 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (27 27 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (27 27 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (26 17 (:REWRITE DEFAULT-+-2))
 (24 4 (:REWRITE COMMUTATIVITY-OF-*))
 (20 17 (:REWRITE DEFAULT-+-1))
 (20 1 (:LINEAR EXPT-OF-ONE-LESS-LINEAR))
 (6 6 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (6 6 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (5 1 (:REWRITE *-OF-*-OF-/-SAME))
 (4 1 (:DEFINITION FIX))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(FLOOR-OF-TIMES-2-EXPT
 (197 4 (:REWRITE FLOOR-WHEN-<))
 (162 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (150 2 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (148 148 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (148 148 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (133 2 (:REWRITE INTEGERP-OF-*))
 (87 16 (:REWRITE DEFAULT-*-2))
 (56 1 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (48 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (44 44 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (44 44 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (44 44 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (44 44 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (44 44 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (44 4 (:REWRITE DEFAULT-UNARY-/))
 (41 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (38 1 (:REWRITE <-OF-/-AND-CONSTANT))
 (35 14 (:REWRITE DEFAULT-<-2))
 (35 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (34 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (33 14 (:REWRITE DEFAULT-<-1))
 (31 10 (:REWRITE RATIONALP-*))
 (22 16 (:REWRITE DEFAULT-*-1))
 (21 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (16 16 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (16 16 (:LINEAR EXPT-BOUND-LINEAR))
 (15 8 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (15 4 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (14 4 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (11 1 (:REWRITE <-OF-*-OF-/-ARG1-ARG3))
 (10 1 (:REWRITE COMMUTATIVITY-OF-*))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:LINEAR EXPT-BOUND-LINEAR-2))
 (8 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (6 2 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (6 1 (:REWRITE RATIONALP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (6 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (6 1 (:REWRITE <-OF-*-OF-/-ARG2-ARG1))
 (6 1 (:REWRITE <-OF-*-OF-/-ARG2-ALT))
 (4 4 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (4 2 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (4 2 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (4 1 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (4 1 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NONNEGATIVE-LINEAR))
 (4 1 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (2 2 (:REWRITE <-OF-*-AND-0))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (2 2 (:LINEAR <=-OF-/-LINEAR))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (2 2 (:LINEAR <-OF-*-AND-*))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(FLOOR-SHIFTING-LEMMA
 (4516 24 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (1657 11 (:REWRITE FLOOR-WHEN-<))
 (1638 9 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (1388 28 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (1346 28 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (1344 24 (:LINEAR *-OF-FLOOR-UPPER-BOUND-LINEAR))
 (622 28 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (614 28 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (606 24 (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
 (565 145 (:REWRITE DEFAULT-<-2))
 (488 4 (:REWRITE <-OF-*-AND-0))
 (481 481 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (481 481 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (481 481 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (481 481 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (481 481 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (426 48 (:REWRITE DEFAULT-*-2))
 (407 48 (:REWRITE DEFAULT-*-1))
 (345 145 (:REWRITE DEFAULT-<-1))
 (182 11 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (168 24 (:REWRITE DEFAULT-UNARY-/))
 (132 4 (:REWRITE <-OF-FLOOR-AND-0))
 (129 11 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (128 11 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (128 11 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (92 92 (:LINEAR EXPT-BOUND-LINEAR))
 (84 28 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (62 4 (:REWRITE DEFAULT-+-2))
 (57 57 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (48 48 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (48 48 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (48 48 (:LINEAR <-OF-*-AND-*))
 (46 46 (:LINEAR EXPT-BOUND-LINEAR-2))
 (36 9 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (31 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (28 28 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (28 28 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (28 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (27 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (24 24 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (22 22 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (16 4 (:REWRITE <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE))
 (11 11 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (10 4 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (8 8 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (8 8 (:REWRITE <-OF-0-AND-EXPT))
 (8 2 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (6 6 (:TYPE-PRESCRIPTION MOD))
 (6 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (4 1 (:REWRITE RATIONALP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (4 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (1 1 (:REWRITE RATIONALP-*))
 (1 1 (:REWRITE INTEGERP-OF-*))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 )
(FLOOR-OF--1-AND-EXPT
 (7 1 (:REWRITE DEFAULT-UNARY-/))
 (4 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
(FLOOR-OF-FLOOR-SPECIAL
 (1443 40 (:REWRITE FLOOR-WHEN-<))
 (788 7 (:REWRITE <-OF-*-OF-/-ARG2-ARG1))
 (247 247 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (247 247 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (247 247 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (247 247 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (247 247 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (218 16 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (208 78 (:REWRITE DEFAULT-*-2))
 (208 2 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (192 48 (:LINEAR EXPT-BOUND-LINEAR))
 (145 5 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (144 79 (:REWRITE DEFAULT-<-2))
 (142 16 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (118 78 (:REWRITE DEFAULT-*-1))
 (114 79 (:REWRITE DEFAULT-<-1))
 (108 40 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (75 40 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (75 40 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (48 48 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (40 40 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (36 16 (:REWRITE DEFAULT-+-2))
 (35 35 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (35 5 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (30 30 (:TYPE-PRESCRIPTION MOD))
 (28 4 (:REWRITE DEFAULT-UNARY-/))
 (24 24 (:LINEAR EXPT-BOUND-LINEAR-2))
 (22 2 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 16 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (16 16 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (8 8 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (6 2 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (5 5 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (5 5 (:REWRITE INTEGERP-OF-*))
 (4 4 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (4 4 (:LINEAR <-OF-*-AND-*))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(FLOOR-OF-*-OF-EXPT-AND-EXPT
 (5448 16 (:REWRITE FLOOR-WHEN-<))
 (5159 44 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (1702 11 (:REWRITE <-OF-*-OF-/-ARG1-ARG3))
 (1547 234 (:LINEAR EXPT-BOUND-LINEAR))
 (1462 4 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (1171 10 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (1004 1004 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (954 18 (:REWRITE INTEGERP-OF-*))
 (946 11 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NONNEGATIVE-LINEAR))
 (945 117 (:LINEAR EXPT-BOUND-LINEAR-2))
 (783 151 (:REWRITE DEFAULT-*-2))
 (748 11 (:REWRITE <-OF-*-OF-/-ARG2-ARG2))
 (539 11 (:REWRITE <-OF-/-AND-CONSTANT))
 (441 151 (:REWRITE DEFAULT-*-1))
 (387 9 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (320 4 (:REWRITE <-OF-*-AND-0))
 (314 206 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (258 4 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (238 22 (:REWRITE DEFAULT-UNARY-/))
 (223 223 (:TYPE-PRESCRIPTION INTEGERP-OF-*-OF-EXPT2-AND-/-OF-EXPT2-TYPE))
 (201 101 (:REWRITE DEFAULT-<-1))
 (182 101 (:REWRITE DEFAULT-<-2))
 (155 16 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (130 1 (:REWRITE <-OF-*-OF-/-ARG2-ARG1))
 (121 16 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (121 16 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (121 16 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (108 9 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (99 11 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (88 88 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (88 88 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (88 88 (:LINEAR <-OF-*-AND-*))
 (81 9 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (78 42 (:REWRITE DEFAULT-+-2))
 (72 72 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (72 72 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (72 72 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (72 72 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (72 72 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (63 21 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (60 20 (:REWRITE <-OF-EXPT-AND-EXPT))
 (54 9 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (44 44 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (44 44 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (44 44 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (44 44 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (44 11 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (42 42 (:REWRITE DEFAULT-+-1))
 (36 9 (:REWRITE INTEGERP-OF-/-OF-EXPT-2))
 (27 9 (:REWRITE INTEGERP-OF-*-OF-EXPT2-AND-/-OF-EXPT2))
 (24 24 (:LINEAR <=-OF-/-LINEAR))
 (23 23 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (16 16 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (10 1 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (7 7 (:TYPE-PRESCRIPTION INTEGERP-OF-*-OF-/-OF-EXPT2-AND-EXPT2-TYPE))
 (4 4 (:REWRITE <-OF-0-AND-EXPT))
 (4 4 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (4 4 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (2 2 (:REWRITE *-OF-0))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(UNSIGNED-BYTE-P-OF-FLOOR-OF-EXPT
 (31 13 (:REWRITE DEFAULT-<-2))
 (30 1 (:REWRITE UNSIGNED-BYTE-P-OF-FLOOR))
 (26 1 (:REWRITE FLOOR-WHEN-<))
 (13 13 (:REWRITE DEFAULT-<-1))
 (12 3 (:REWRITE DEFAULT-*-2))
 (12 3 (:REWRITE DEFAULT-*-1))
 (10 4 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (3 1 (:REWRITE <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-2))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (1 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (1 1 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (1 1 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (1 1 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (1 1 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 )
