(FLOOR-OF-EXPT-2-AND-2
 (1544 132 (:REWRITE DEFAULT-*-2))
 (1533 1533 (:TYPE-PRESCRIPTION EVENP))
 (1022 511 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (1022 511 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (1022 511 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (660 3 (:LINEAR EXPT-HALF-LINEAR))
 (511 511 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (402 3 (:LINEAR EXPT-OF-ONE-LESS-LINEAR))
 (258 212 (:REWRITE DEFAULT-+-2))
 (250 20 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (250 20 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (238 19 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (236 132 (:REWRITE DEFAULT-*-1))
 (212 212 (:REWRITE DEFAULT-+-1))
 (208 1 (:REWRITE FLOOR-UNIQUE-EQUAL-VERSION))
 (204 3 (:REWRITE +-OF-EXPT2-OF-ONE-LESS-AND-EXPT2-OF-ONE-LESS))
 (174 58 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (173 14 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (164 164 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (155 143 (:REWRITE DEFAULT-<-1))
 (154 143 (:REWRITE DEFAULT-<-2))
 (140 54 (:REWRITE ZIP-OPEN))
 (129 43 (:REWRITE +-COMBINE-CONSTANTS))
 (120 1 (:REWRITE <-OF-*-OF-/-ARG1-ARG1))
 (86 43 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (70 70 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (70 70 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (70 70 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (70 70 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (52 22 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (43 43 (:DEFINITION FIX))
 (38 22 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (26 11 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (19 19 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (19 11 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (19 11 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (4 4 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (4 4 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (1 1 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 )
(FLOOR-OF-EXPT-AND-2
 (396 396 (:TYPE-PRESCRIPTION EVENP))
 (264 132 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (264 132 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (264 132 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (232 23 (:REWRITE DEFAULT-*-2))
 (186 2 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (160 2 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (132 132 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (95 1 (:LINEAR EXPT-HALF-LINEAR))
 (67 23 (:REWRITE DEFAULT-*-1))
 (56 4 (:REWRITE COMMUTATIVITY-OF-*))
 (55 1 (:LINEAR EXPT-OF-ONE-LESS-LINEAR))
 (50 17 (:REWRITE DEFAULT-+-2))
 (41 41 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (28 17 (:REWRITE DEFAULT-+-1))
 (27 27 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (27 27 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (27 27 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (27 27 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (15 5 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (13 1 (:REWRITE *-OF-*-OF-/-SAME))
 (12 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (12 1 (:DEFINITION FIX))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (6 6 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (6 6 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (6 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (6 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (3 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (3 3 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 )
(FLOOR-OF-TIMES-2-EXPT
 (834 4 (:REWRITE FLOOR-WHEN-<))
 (558 558 (:TYPE-PRESCRIPTION EVENP))
 (482 2 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (444 2 (:REWRITE INTEGERP-OF-*))
 (372 186 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (372 186 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (372 186 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (337 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (234 9 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (222 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (186 186 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (186 186 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (185 16 (:REWRITE DEFAULT-*-2))
 (176 1 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (153 1 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (141 92 (:REWRITE DEFAULT-<-2))
 (140 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (137 1 (:REWRITE <-OF-/-AND-CONSTANT))
 (132 92 (:REWRITE DEFAULT-<-1))
 (127 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (126 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (114 1 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (100 4 (:REWRITE DEFAULT-UNARY-/))
 (61 12 (:REWRITE RATIONALP-*))
 (54 18 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (54 18 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (54 4 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (54 4 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (49 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (44 44 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (44 44 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (44 44 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (44 44 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (44 44 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (42 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (39 3 (:REWRITE RATIONALP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (29 16 (:REWRITE DEFAULT-*-1))
 (29 4 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (28 4 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (28 2 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (27 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (27 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (27 9 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (25 1 (:REWRITE <-OF-*-OF-/-ARG1-ARG3))
 (23 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (22 8 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (18 18 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (18 18 (:LINEAR EXPT-BOUND-LINEAR))
 (18 18 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (18 18 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (17 1 (:REWRITE COMMUTATIVITY-OF-*))
 (15 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (13 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (13 1 (:REWRITE <-OF-*-OF-/-ARG2-ARG1-GEN))
 (13 1 (:REWRITE <-OF-*-OF-/-ARG2-ARG1))
 (13 1 (:REWRITE <-OF-*-OF-/-ARG2-ALT))
 (12 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (9 9 (:LINEAR EXPT-BOUND-LINEAR-2))
 (9 3 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (4 4 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (4 4 (:LINEAR <=-OF-/-LINEAR))
 (4 2 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (4 1 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (4 1 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NONNEGATIVE-LINEAR))
 (4 1 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (2 2 (:REWRITE <-OF-*-AND-0))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (2 2 (:LINEAR <-OF-*-AND-*-LINEAR))
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
 (16832 34 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (16808 34 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (9494 74 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (9308 74 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (9223 15 (:REWRITE FLOOR-WHEN-<))
 (9074 13 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (8502 74 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (7842 7842 (:TYPE-PRESCRIPTION EVENP))
 (5228 2614 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (5228 2614 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (5228 2614 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (4504 74 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (4428 34 (:LINEAR *-OF-FLOOR-UPPER-BOUND-LINEAR))
 (2838 6 (:REWRITE <-OF-*-AND-0))
 (2614 2614 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (2614 2614 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (2256 34 (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
 (1959 649 (:REWRITE DEFAULT-<-1))
 (1873 649 (:REWRITE DEFAULT-<-2))
 (1490 72 (:REWRITE DEFAULT-*-2))
 (1455 72 (:REWRITE DEFAULT-*-1))
 (1034 98 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (846 6 (:REWRITE <-OF-FLOOR-AND-0))
 (829 829 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (829 829 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (829 829 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (829 829 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (829 829 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (828 36 (:REWRITE DEFAULT-UNARY-/))
 (618 15 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (588 196 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (398 398 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (393 15 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (392 15 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (392 15 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (294 98 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (224 6 (:REWRITE DEFAULT-+-2))
 (222 74 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (196 196 (:LINEAR EXPT-BOUND-LINEAR))
 (196 196 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (196 196 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (156 13 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (147 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (146 98 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (136 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (135 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (113 113 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (98 98 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (98 98 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (98 98 (:LINEAR EXPT-BOUND-LINEAR-2))
 (74 74 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (74 74 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (68 68 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (68 68 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (68 68 (:LINEAR <-OF-*-AND-*-LINEAR))
 (40 40 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (34 34 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (34 34 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (34 34 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (34 34 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (34 34 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (28 6 (:REWRITE DEFAULT-+-1))
 (24 6 (:REWRITE <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE))
 (19 19 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (19 19 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (15 15 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (14 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 13 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (12 12 (:REWRITE <-OF-0-AND-EXPT))
 (12 1 (:REWRITE RATIONALP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (12 1 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (8 2 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (6 6 (:TYPE-PRESCRIPTION MOD))
 (1 1 (:REWRITE RATIONALP-*))
 (1 1 (:REWRITE INTEGERP-OF-*))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 )
(FLOOR-OF--1-AND-EXPT
 (123 123 (:TYPE-PRESCRIPTION EVENP))
 (82 41 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (82 41 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (82 41 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (41 41 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (41 41 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (23 1 (:REWRITE DEFAULT-UNARY-/))
 (12 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(FLOOR-OF-FLOOR-SPECIAL
 (3155 44 (:REWRITE FLOOR-WHEN-<))
 (1582 7 (:REWRITE <-OF-*-OF-/-ARG2-ARG1-GEN))
 (1140 1140 (:TYPE-PRESCRIPTION EVENP))
 (760 380 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (760 380 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (760 380 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (630 5 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE))
 (576 24 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (576 24 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (546 18 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (380 380 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (380 380 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (336 48 (:LINEAR EXPT-BOUND-LINEAR))
 (336 48 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (320 86 (:REWRITE DEFAULT-*-2))
 (261 261 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (261 261 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (261 261 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (261 261 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (261 261 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (224 18 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (213 89 (:REWRITE DEFAULT-<-2))
 (208 2 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (200 44 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (182 2 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (158 86 (:REWRITE DEFAULT-*-1))
 (124 89 (:REWRITE DEFAULT-<-1))
 (98 98 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (92 4 (:REWRITE DEFAULT-UNARY-/))
 (79 44 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (79 44 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (54 18 (:REWRITE DEFAULT-+-2))
 (48 48 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (48 48 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (48 48 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (48 48 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (44 44 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (39 39 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (38 2 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (35 5 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (30 30 (:TYPE-PRESCRIPTION MOD))
 (24 24 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (24 24 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (24 24 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (24 24 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (24 24 (:LINEAR EXPT-BOUND-LINEAR-2))
 (21 7 (:REWRITE <-OF-2-AND-EXPT2))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 18 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (18 18 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (12 4 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (8 8 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (5 5 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP-ALT))
 (5 5 (:REWRITE INTEGERP-OF-*))
 (5 5 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (5 5 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (4 4 (:LINEAR <-OF-*-AND-*-LINEAR))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(FLOOR-OF-*-OF-EXPT-AND-EXPT
 (34381 16 (:REWRITE FLOOR-WHEN-<))
 (26100 55 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (18282 55 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (11646 11646 (:TYPE-PRESCRIPTION EVENP))
 (9104 4 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (7764 3882 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (7764 3882 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (7764 3882 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (6841 11 (:REWRITE <-OF-*-OF-/-ARG1-ARG3))
 (6027 346 (:LINEAR EXPT-BOUND-LINEAR))
 (4774 22 (:REWRITE <-OF-/-AND-CONSTANT))
 (4671 346 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (4510 22 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NONNEGATIVE-LINEAR))
 (4400 173 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (4290 22 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (3943 10 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (3882 3882 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (3735 199 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (3303 18 (:REWRITE INTEGERP-OF-*))
 (2868 173 (:LINEAR EXPT-BOUND-LINEAR-2))
 (2849 11 (:REWRITE <-OF-*-OF-/-ARG2-ARG2))
 (2717 11 (:REWRITE <-OF-*-OF-/-ARG1-ARG2))
 (2264 198 (:REWRITE DEFAULT-*-2))
 (1845 9 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (1728 4 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (1548 4 (:REWRITE <-OF-*-AND-0))
 (1544 1115 (:REWRITE DEFAULT-<-1))
 (1295 1115 (:REWRITE DEFAULT-<-2))
 (1293 198 (:REWRITE DEFAULT-*-1))
 (1287 1287 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (934 346 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (934 346 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (842 346 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (823 33 (:REWRITE DEFAULT-UNARY-/))
 (770 2 (:REWRITE <-OF-0-AND-*))
 (729 173 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (542 346 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (528 22 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (528 1 (:REWRITE <-OF-*-OF-/-ARG2-ARG1-GEN))
 (477 173 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (421 173 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (421 173 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (395 16 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (315 9 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (311 16 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (311 16 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (311 16 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (278 278 (:TYPE-PRESCRIPTION INTEGERP-OF-*-OF-EXPT2-AND-/-OF-EXPT2-TYPE))
 (264 22 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (216 9 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (151 55 (:REWRITE DEFAULT-+-2))
 (129 43 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (117 9 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (110 110 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (110 110 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (110 110 (:LINEAR <-OF-*-AND-*-LINEAR))
 (93 31 (:REWRITE <-OF-EXPT-AND-EXPT-SAME-BASE))
 (90 90 (:LINEAR <=-OF-/-LINEAR))
 (72 72 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (72 72 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (72 72 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (72 72 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (72 72 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (55 55 (:REWRITE DEFAULT-+-1))
 (55 55 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (55 55 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (55 55 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (55 55 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (41 41 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT-GEN))
 (36 9 (:REWRITE INTEGERP-OF-/-OF-EXPT-2))
 (27 9 (:REWRITE INTEGERP-OF-*-OF-EXPT2-AND-/-OF-EXPT2))
 (25 1 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 (23 23 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (19 19 (:REWRITE <-OF-*-OF-CONSTANT-AND-CONSTANT))
 (16 16 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (9 9 (:TYPE-PRESCRIPTION INTEGERP-OF-*-OF-/-OF-EXPT2-AND-EXPT2-TYPE))
 (5 5 (:REWRITE <-OF-0-AND-EXPT))
 (4 4 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (4 4 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (2 2 (:REWRITE <-OF-EXPT-AND-0))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (2 2 (:REWRITE *-OF-0))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(UNSIGNED-BYTE-P-OF-FLOOR-OF-EXPT
 (134 1 (:REWRITE FLOOR-WHEN-<))
 (131 1 (:REWRITE UNSIGNED-BYTE-P-OF-FLOOR))
 (120 120 (:TYPE-PRESCRIPTION EVENP))
 (89 23 (:REWRITE DEFAULT-<-2))
 (80 40 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (80 40 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (80 40 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (48 2 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (40 40 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (40 40 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (36 3 (:REWRITE DEFAULT-*-2))
 (36 3 (:REWRITE DEFAULT-*-1))
 (28 4 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (28 4 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (23 23 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (12 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (12 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (6 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (6 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (6 2 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (3 1 (:REWRITE <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
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
