(ASH-OF-0
 (104 2 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (98 2 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (95 5 (:REWRITE FLOOR-WHEN-<))
 (82 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (52 2 (:REWRITE <-OF-*-AND-0))
 (32 4 (:REWRITE <-OF-*-CANCEL-2))
 (21 11 (:REWRITE DEFAULT-<-1))
 (20 20 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (20 20 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (20 20 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (20 20 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (20 20 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (14 10 (:REWRITE DEFAULT-*-2))
 (14 10 (:REWRITE DEFAULT-*-1))
 (12 12 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (12 12 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (12 12 (:LINEAR <-OF-*-AND-*-LINEAR))
 (11 11 (:REWRITE DEFAULT-<-2))
 (9 5 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (9 5 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (9 5 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (9 5 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (6 6 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (5 5 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (2 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 )
(INTEGERP-OF-ASH)
(EQUAL-OF-0-AND-ASH
 (1791 1791 (:TYPE-PRESCRIPTION EVENP))
 (1194 597 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (1194 597 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (1194 597 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (701 9 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (597 597 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (597 597 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (347 35 (:REWRITE DEFAULT-*-2))
 (287 35 (:REWRITE DEFAULT-*-1))
 (222 6 (:REWRITE <-OF-/-AND-CONSTANT))
 (218 90 (:REWRITE DEFAULT-<-2))
 (218 90 (:REWRITE DEFAULT-<-1))
 (218 2 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NONNEGATIVE-LINEAR))
 (76 1 (:REWRITE FLOOR-WHEN-<))
 (75 3 (:REWRITE DEFAULT-UNARY-/))
 (69 1 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (64 64 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (64 16 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (64 16 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (50 2 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (32 8 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (32 8 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (32 8 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (32 8 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (32 1 (:REWRITE INTEGERP-OF-*))
 (26 2 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (18 18 (:LINEAR <-OF-*-AND-*-LINEAR))
 (16 16 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (15 15 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (15 15 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (15 15 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (15 15 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (15 15 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (13 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (13 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (13 1 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (13 1 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (8 8 (:LINEAR <=-OF-/-LINEAR))
 (8 8 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (7 1 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
 (6 6 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (4 4 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (4 4 (:REWRITE <-OF-1-AND-EXPT))
 (4 4 (:REWRITE <-OF-/-AND-CONSTANT-1))
 (1 1 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE <-OF-EXPT-AND-0))
 )
(<=-OF-0-AND-ASH
 (430 3 (:REWRITE FLOOR-WHEN-<))
 (399 5 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (318 318 (:TYPE-PRESCRIPTION EVENP))
 (270 1 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (215 3 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (212 106 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (212 106 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (212 106 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (127 59 (:REWRITE DEFAULT-<-2))
 (121 59 (:REWRITE DEFAULT-<-1))
 (106 106 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (106 106 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (106 106 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (98 3 (:REWRITE INTEGERP-OF-*))
 (44 6 (:REWRITE DEFAULT-*-2))
 (44 6 (:REWRITE DEFAULT-*-1))
 (41 41 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (41 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (41 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (41 3 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (41 3 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (40 10 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (40 10 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (21 3 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
 (20 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (20 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (20 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (20 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (18 18 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (18 18 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (18 18 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (14 1 (:REWRITE DEFAULT-+-2))
 (10 10 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (10 10 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (10 10 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (10 10 (:LINEAR <-OF-*-AND-*-LINEAR))
 (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (4 4 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (4 4 (:REWRITE <-OF-1-AND-EXPT))
 (3 3 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (1 1 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE <-OF-EXPT-AND-0))
 (1 1 (:REWRITE <-OF-0-AND-EXPT))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (1 1 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 )
(<=-OF-0-AND-ASH-TYPE
 (430 3 (:REWRITE FLOOR-WHEN-<))
 (399 5 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (318 318 (:TYPE-PRESCRIPTION EVENP))
 (270 1 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (215 3 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (212 106 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (212 106 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (212 106 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (127 59 (:REWRITE DEFAULT-<-2))
 (121 59 (:REWRITE DEFAULT-<-1))
 (106 106 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (106 106 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (106 106 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (98 3 (:REWRITE INTEGERP-OF-*))
 (44 6 (:REWRITE DEFAULT-*-2))
 (44 6 (:REWRITE DEFAULT-*-1))
 (41 41 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (41 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (41 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (41 3 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (41 3 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (40 10 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (40 10 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (21 3 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
 (20 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (20 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (20 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (20 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (18 18 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (18 18 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (18 18 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (14 1 (:REWRITE DEFAULT-+-2))
 (10 10 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (10 10 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (10 10 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (10 10 (:LINEAR <-OF-*-AND-*-LINEAR))
 (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (5 5 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (4 4 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (4 4 (:REWRITE <-OF-1-AND-EXPT))
 (3 3 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (1 1 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE <-OF-EXPT-AND-0))
 (1 1 (:REWRITE <-OF-0-AND-EXPT))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (1 1 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 )
(UNSIGNED-BYTE-P-OF-ASH-ALT
 (2883 2883 (:TYPE-PRESCRIPTION EVENP))
 (1922 961 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (1922 961 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (1922 961 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (1068 12 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (961 961 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (539 51 (:REWRITE DEFAULT-*-2))
 (407 141 (:REWRITE DEFAULT-<-2))
 (386 51 (:REWRITE DEFAULT-*-1))
 (314 141 (:REWRITE DEFAULT-<-1))
 (207 3 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (200 3 (:REWRITE FLOOR-WHEN-<))
 (128 4 (:REWRITE INTEGERP-OF-*))
 (122 1 (:REWRITE UNSIGNED-BYTE-P-OF-FLOOR))
 (114 28 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (106 106 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (100 4 (:REWRITE DEFAULT-UNARY-/))
 (97 1 (:REWRITE <-OF-*-AND-*))
 (94 28 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (57 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (57 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (51 12 (:REWRITE DEFAULT-+-2))
 (51 12 (:REWRITE DEFAULT-+-1))
 (47 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (47 14 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (39 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (39 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (39 3 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (39 3 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (38 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (37 37 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (37 37 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (37 37 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (37 37 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (28 28 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (28 4 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
 (24 24 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (24 24 (:LINEAR <-OF-*-AND-*-LINEAR))
 (20 20 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (20 12 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (12 12 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (10 10 (:REWRITE <-OF-1-AND-EXPT))
 (10 10 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (10 10 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (3 3 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1-CHEAP))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (2 2 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (1 1 (:REWRITE INTEGERP-OF-+-WHEN-INTEGERP-1))
 (1 1 (:REWRITE <-OF-EXPT-AND-0))
 (1 1 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 )
(UNSIGNED-BYTE-P-ASH-ALT-STRONG
 (170 1 (:REWRITE FLOOR-WHEN-<))
 (126 126 (:TYPE-PRESCRIPTION EVENP))
 (84 42 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (84 42 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (84 42 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (55 1 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (49 16 (:REWRITE DEFAULT-<-1))
 (49 5 (:REWRITE DEFAULT-*-2))
 (49 2 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (42 42 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (42 42 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (38 16 (:REWRITE DEFAULT-<-2))
 (27 5 (:REWRITE DEFAULT-*-1))
 (23 1 (:REWRITE DEFAULT-UNARY-/))
 (12 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (12 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (12 1 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (12 1 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (6 6 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (6 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (3 1 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (3 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (3 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (2 2 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (2 2 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (2 2 (:LINEAR <-OF-*-AND-*-LINEAR))
 (1 1 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (1 1 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE *-OF-0))
 (1 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (1 1 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(<-OF-ASH-ARG1
 (339 339 (:TYPE-PRESCRIPTION EVENP))
 (226 113 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (226 113 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (226 113 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (140 18 (:REWRITE DEFAULT-*-2))
 (140 18 (:REWRITE DEFAULT-*-1))
 (113 113 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (113 113 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (113 113 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (82 3 (:REWRITE FLOOR-WHEN-<))
 (70 10 (:REWRITE DEFAULT-<-1))
 (70 3 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (50 50 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (50 50 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (50 50 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (50 50 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (50 50 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (50 2 (:REWRITE DEFAULT-UNARY-/))
 (44 4 (:REWRITE DEFAULT-+-2))
 (31 1 (:REWRITE INTEGERP-OF-*))
 (24 10 (:REWRITE DEFAULT-<-2))
 (16 4 (:REWRITE DEFAULT-+-1))
 (15 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (15 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (15 3 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (15 3 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (6 1 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
 (3 3 (:TYPE-PRESCRIPTION <=-OF-0-AND-ASH-TYPE))
 (3 3 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (3 3 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (3 3 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (3 1 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (2 2 (:LINEAR <-OF-*-AND-*-LINEAR))
 (1 1 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (1 1 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(<-OF-ASH-ARG2
 (213 213 (:TYPE-PRESCRIPTION EVENP))
 (142 71 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (142 71 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (142 71 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (80 3 (:REWRITE FLOOR-WHEN-<))
 (71 71 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (71 71 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (71 71 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (70 3 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (49 49 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (49 49 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (49 49 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (49 49 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (49 49 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (43 7 (:REWRITE DEFAULT-<-1))
 (42 6 (:REWRITE DEFAULT-*-2))
 (42 6 (:REWRITE DEFAULT-*-1))
 (31 1 (:REWRITE INTEGERP-OF-*))
 (21 7 (:REWRITE DEFAULT-<-2))
 (16 2 (:REWRITE DEFAULT-+-2))
 (15 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (15 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (15 3 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (15 3 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (6 1 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
 (3 3 (:TYPE-PRESCRIPTION <=-OF-0-AND-ASH-TYPE))
 (3 3 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (3 1 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (2 2 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (2 2 (:LINEAR <-OF-*-AND-*-LINEAR))
 (1 1 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(<=-OF-ASH-WHEN-<=-FREE-LINEAR
 (1146 1146 (:TYPE-PRESCRIPTION EVENP))
 (764 382 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (764 382 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (764 382 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (692 4 (:REWRITE FLOOR-WHEN-<))
 (462 7 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (382 382 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (382 382 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (382 382 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (360 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (280 4 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (207 2 (:REWRITE <-OF-*-AND-0))
 (174 16 (:REWRITE DEFAULT-*-2))
 (165 99 (:REWRITE DEFAULT-<-1))
 (126 4 (:REWRITE INTEGERP-OF-*))
 (118 99 (:REWRITE DEFAULT-<-2))
 (61 61 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (61 61 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (61 61 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (61 61 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (61 61 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (59 16 (:REWRITE DEFAULT-*-1))
 (54 18 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (54 18 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (54 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (54 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (54 4 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (54 4 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (27 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (27 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (27 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (27 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (24 4 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
 (21 7 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (18 18 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (14 14 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (14 14 (:LINEAR <-OF-*-AND-*-LINEAR))
 (14 1 (:REWRITE DEFAULT-+-2))
 (7 7 (:TYPE-PRESCRIPTION <=-OF-0-AND-ASH-TYPE))
 (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (2 2 (:REWRITE <-OF-0-AND-EXPT))
 (2 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 )
(<-OF-ASH-LINEAR-WHEN-<-FREE-LINEAR
 (1146 1146 (:TYPE-PRESCRIPTION EVENP))
 (764 382 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (764 382 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (764 382 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (692 4 (:REWRITE FLOOR-WHEN-<))
 (462 7 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (382 382 (:TYPE-PRESCRIPTION INTEGERP-OF-EXPT-TYPE))
 (382 382 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (382 382 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (360 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (280 4 (:REWRITE FLOOR-OF-1-WHEN-INTEGERP))
 (207 2 (:REWRITE <-OF-*-AND-0))
 (185 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (174 16 (:REWRITE DEFAULT-*-2))
 (171 99 (:REWRITE DEFAULT-<-1))
 (126 4 (:REWRITE INTEGERP-OF-*))
 (112 99 (:REWRITE DEFAULT-<-2))
 (61 61 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (61 61 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (61 61 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (61 61 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (61 61 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (59 16 (:REWRITE DEFAULT-*-1))
 (54 18 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (54 18 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (54 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (54 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (54 4 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (54 4 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (27 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (27 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (27 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (27 9 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (24 4 (:REWRITE INTEGERP-OF-EXPT-WHEN-NATP))
 (21 7 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (18 18 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (14 14 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (14 14 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (14 14 (:LINEAR <-OF-*-AND-*-LINEAR))
 (14 1 (:REWRITE DEFAULT-+-2))
 (7 7 (:TYPE-PRESCRIPTION <=-OF-0-AND-ASH-TYPE))
 (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (7 7 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (2 2 (:REWRITE <-OF-0-AND-EXPT))
 (2 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 )
(<-OF-ASH-AND-*-OF-EXPT
 (1110 1110 (:TYPE-PRESCRIPTION EVENP))
 (740 370 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (740 370 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (740 370 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (370 370 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (370 370 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (226 6 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (142 2 (:REWRITE FLOOR-WHEN-<))
 (98 10 (:REWRITE DEFAULT-*-2))
 (88 2 (:REWRITE <-OF-*-AND-*))
 (70 37 (:REWRITE DEFAULT-<-1))
 (56 56 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (56 56 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (56 56 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (56 56 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (56 56 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (37 37 (:REWRITE DEFAULT-<-2))
 (32 10 (:REWRITE DEFAULT-*-1))
 (30 10 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (24 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (24 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (24 2 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (24 2 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (15 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (15 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (12 12 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (12 12 (:LINEAR <-OF-*-AND-*-LINEAR))
 (12 4 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (10 10 (:TYPE-PRESCRIPTION <=-OF-0-AND-ASH-TYPE))
 (10 10 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (10 10 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (5 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (5 5 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (4 4 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (2 2 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 )
(<-OF-ASH-AND-*-OF-EXPT-ALT
 (213 213 (:TYPE-PRESCRIPTION EVENP))
 (142 71 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (142 71 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (142 71 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (71 71 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (71 71 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (66 66 (:TYPE-PRESCRIPTION <=-OF-0-AND-ASH-TYPE))
 (41 8 (:REWRITE DEFAULT-<-2))
 (38 5 (:REWRITE DEFAULT-*-2))
 (27 5 (:REWRITE DEFAULT-*-1))
 (14 8 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (3 3 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 )
(<-OF-*-OF-EXPT-AND-ASH
 (7236 7236 (:TYPE-PRESCRIPTION EVENP))
 (4824 2412 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (4824 2412 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (4824 2412 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (2412 2412 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (2412 2412 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (1517 39 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (1141 140 (:REWRITE DEFAULT-*-2))
 (1138 27 (:REWRITE FLOOR-WHEN-<))
 (635 140 (:REWRITE DEFAULT-*-1))
 (401 27 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (362 186 (:REWRITE DEFAULT-<-1))
 (294 186 (:REWRITE DEFAULT-<-2))
 (280 27 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (280 27 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (280 27 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (239 239 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (239 239 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (175 12 (:REWRITE DEFAULT-+-2))
 (162 54 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (81 27 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (81 27 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (81 27 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (78 78 (:LINEAR <-OF-*-AND-*-LINEAR))
 (64 64 (:TYPE-PRESCRIPTION <=-OF-0-AND-ASH-TYPE))
 (54 54 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (54 54 (:LINEAR <-OF-EXPT-AND-EXPT-LINEAR))
 (27 27 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (27 27 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (27 27 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (23 23 (:REWRITE INTEGERP-OF-*))
 (13 13 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (12 12 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (12 12 (:REWRITE DEFAULT-+-1))
 (8 8 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (6 6 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (6 6 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (4 4 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 )
(<-OF-*-OF-EXPT-AND-ASH-ALT
 (213 213 (:TYPE-PRESCRIPTION EVENP))
 (142 71 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (142 71 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (142 71 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (71 71 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (71 71 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (66 66 (:TYPE-PRESCRIPTION <=-OF-0-AND-ASH-TYPE))
 (41 8 (:REWRITE DEFAULT-<-1))
 (38 5 (:REWRITE DEFAULT-*-2))
 (27 5 (:REWRITE DEFAULT-*-1))
 (14 8 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 )
(DISTRIBUTIVITY-ALT
 (11 8 (:REWRITE DEFAULT-*-2))
 (11 8 (:REWRITE DEFAULT-*-1))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 2 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (4 4 (:LINEAR <-OF-*-AND-*-LINEAR))
 (4 3 (:REWRITE DEFAULT-+-2))
 (4 3 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(<-OF-ASH-LINEAR-WHEN-<-FREE-LINEAR-STRONG
 (477 477 (:TYPE-PRESCRIPTION EVENP))
 (318 159 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (318 159 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (318 159 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (159 159 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (159 159 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (114 114 (:TYPE-PRESCRIPTION <=-OF-0-AND-ASH-TYPE))
 (51 7 (:REWRITE DEFAULT-<-1))
 (39 6 (:REWRITE DEFAULT-*-2))
 (39 6 (:REWRITE DEFAULT-*-1))
 (28 6 (:REWRITE DEFAULT-+-2))
 (28 6 (:REWRITE DEFAULT-+-1))
 (24 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (11 7 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (4 1 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (2 2 (:LINEAR <-OF-*-AND-*-LINEAR))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (1 1 (:REWRITE *-OF---ARG1))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
