(REM-OF-0-ARG2
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 2 (:REWRITE DEFAULT-+-2))
 (3 2 (:REWRITE DEFAULT-+-1))
 )
(REM-OF-0-ARG1)
(REM-BECOMES-MOD
 (849 849 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (849 849 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (849 849 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (724 60 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (501 193 (:REWRITE DEFAULT-*-2))
 (394 6 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (376 193 (:REWRITE DEFAULT-*-1))
 (318 60 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (315 87 (:REWRITE DEFAULT-+-2))
 (296 12 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (272 12 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (261 94 (:REWRITE DEFAULT-UNARY-MINUS))
 (224 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (214 200 (:REWRITE DEFAULT-<-1))
 (212 200 (:REWRITE DEFAULT-<-2))
 (182 182 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (156 12 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (132 38 (:REWRITE MOD-WHEN-<-OF-0))
 (120 120 (:LINEAR <-OF-*-AND-*-LINEAR))
 (105 91 (:REWRITE FLOOR-WHEN-<))
 (91 91 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (91 91 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (91 91 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (91 91 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (91 91 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (87 87 (:REWRITE DEFAULT-+-1))
 (79 19 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-1))
 (66 19 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (64 64 (:LINEAR <=-OF-/-LINEAR))
 (60 60 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (60 60 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (51 27 (:REWRITE MOD-WHEN-MULTIPLE))
 (48 16 (:REWRITE <-OF-/-AND-CONSTANT))
 (48 16 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (44 44 (:REWRITE DEFAULT-UNARY-/))
 (41 19 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (40 24 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (40 24 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NONNEGATIVE-LINEAR))
 (38 38 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (33 27 (:REWRITE MOD-WHEN-<))
 (27 27 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (27 27 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (27 27 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (27 27 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (24 24 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (22 22 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (22 22 (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
 (20 12 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (19 19 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (19 19 (:REWRITE INTEGERP-OF-*))
 (18 18 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (18 6 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (18 6 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (17 17 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 (15 15 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (15 15 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (14 2 (:REWRITE <-OF-FLOOR-AND-0))
 (12 12 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (12 12 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (6 6 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (6 6 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (6 6 (:LINEAR MOD-BOUND-LINEAR-ARG2-STRONG))
 (4 4 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (4 4 (:REWRITE +-COMBINE-CONSTANTS))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE))
 (2 2 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 )
(REM-X-Y-=-X-BETTER
 (180 140 (:REWRITE DEFAULT-*-2))
 (180 140 (:REWRITE DEFAULT-*-1))
 (180 20 (:LINEAR <-OF-*-SAME-LINEAR-2))
 (168 80 (:LINEAR <=-OF-/-LINEAR))
 (152 20 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (129 129 (:REWRITE DEFAULT-<-2))
 (129 129 (:REWRITE DEFAULT-<-1))
 (97 97 (:REWRITE DEFAULT-UNARY-/))
 (80 16 (:REWRITE DEFAULT-+-2))
 (70 30 (:REWRITE DEFAULT-UNARY-MINUS))
 (45 15 (:REWRITE <-OF-/-AND-CONSTANT))
 (45 15 (:REWRITE /-EQUAL-CONSTANT-ALT))
 (40 40 (:LINEAR <-OF-*-AND-*-LINEAR))
 (35 15 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NONNEGATIVE-LINEAR))
 (30 12 (:REWRITE FLOOR-WHEN-<))
 (24 6 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-MIXED-2))
 (20 20 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (20 20 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (16 16 (:REWRITE DEFAULT-+-1))
 (15 15 (:LINEAR <=-OF-*-OF-/-WHEN-NEGATIVE-AND-POSITIVE-LINEAR))
 (15 15 (:LINEAR <=-OF-*-OF-/-WHEN-BOTH-NEGATIVE-LINEAR))
 (12 12 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (12 12 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (12 12 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (12 12 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (12 12 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (9 5 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-<-AND-NEGATIVE-ALT))
 (8 8 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 (8 8 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (5 5 (:REWRITE INTEGERP-OF-*-OF-/-WHEN-RATIONALP-AND-COMPLEX-RATIONALP))
 (5 5 (:REWRITE INTEGERP-OF-*))
 (4 4 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (4 4 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
 (2 2 (:REWRITE EQUAL-OF---AND-CONSTANT))
 (2 2 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (2 2 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (2 1 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 )
