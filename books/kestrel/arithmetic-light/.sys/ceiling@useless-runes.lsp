(INTEGERP-OF-*-OF---ARG2
 (3 2 (:REWRITE DEFAULT-*-2))
 (3 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE INTEGERP-OF-*))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(CEILING-OF-0)
(CEILING-IN-TERMS-OF-FLOOR
 (618 24 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (167 151 (:REWRITE DEFAULT-<-2))
 (151 151 (:REWRITE DEFAULT-<-1))
 (138 12 (:REWRITE <-OF-NUMERATOR-AND-DENOMINATOR-SAME))
 (136 8 (:REWRITE <-OF---OF-NUMERATOR-AND-DENOMINATOR-SAME))
 (133 61 (:REWRITE DEFAULT-UNARY-/))
 (132 92 (:REWRITE DEFAULT-+-2))
 (100 92 (:REWRITE DEFAULT-+-1))
 (97 73 (:REWRITE DEFAULT-*-1))
 (90 90 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (90 26 (:REWRITE <-OF-*-OF-/-ARG1-ARG2))
 (75 57 (:REWRITE DEFAULT-UNARY-MINUS))
 (73 73 (:REWRITE DEFAULT-*-2))
 (72 24 (:DEFINITION NFIX))
 (58 18 (:REWRITE <-OF-*-OF-/-ARG2-ARG2))
 (24 24 (:DEFINITION IFIX))
 (24 8 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (22 20 (:REWRITE DEFAULT-NUMERATOR))
 (20 18 (:REWRITE DEFAULT-DENOMINATOR))
 (19 19 (:REWRITE INTEGERP-OF-*))
 (18 18 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (16 16 (:REWRITE RATIONALP-*))
 (16 16 (:LINEAR <-OF-*-AND-*))
 (8 8 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (8 8 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (8 8 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (8 8 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (6 6 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (3 3 (:REWRITE MOVE-MINUS-TO-CONSTANT))
 (3 3 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
 (3 3 (:REWRITE EQUAL-OF---AND-CONSTANT))
 (3 2 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 )
(CEILING-WHEN-<=
 (100 100 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (100 100 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (18 18 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (18 18 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (18 18 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (18 18 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (15 15 (:REWRITE DEFAULT-UNARY-/))
 (14 14 (:REWRITE DEFAULT-*-2))
 (14 14 (:REWRITE DEFAULT-*-1))
 (12 4 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (8 8 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (8 8 (:LINEAR <-OF-*-AND-*))
 (6 6 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (4 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (2 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (1 1 (:REWRITE INTEGERP-OF-*))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(CEILING-OF-+-OF-MINUS-8
 (318 87 (:REWRITE DEFAULT-+-2))
 (212 30 (:REWRITE DEFAULT-UNARY-MINUS))
 (123 123 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (123 123 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (123 123 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (123 123 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (123 123 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (87 87 (:REWRITE DEFAULT-+-1))
 (71 24 (:REWRITE FLOOR-WHEN-<))
 (33 33 (:REWRITE DEFAULT-*-2))
 (33 33 (:REWRITE DEFAULT-*-1))
 (29 29 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (29 29 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (29 29 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (29 29 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (27 27 (:REWRITE DEFAULT-<-2))
 (27 27 (:REWRITE DEFAULT-<-1))
 (13 13 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (10 10 (:REWRITE FLOOR-PEEL-OFF-CONSTANT))
 (6 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (6 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (3 1 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (1 1 (:REWRITE MOVE-MINUS-TO-CONSTANT))
 (1 1 (:REWRITE INTEGERP-OF-*))
 (1 1 (:REWRITE EQUAL-OF---WHEN-VARIABLE))
 (1 1 (:REWRITE EQUAL-OF---AND-CONSTANT))
 )
(CEILING-IN-TERMS-OF-FLOOR-CASES
 (124 4 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (40 2 (:REWRITE <-OF---OF-NUMERATOR-AND-DENOMINATOR-SAME))
 (36 36 (:REWRITE DEFAULT-<-2))
 (36 36 (:REWRITE DEFAULT-<-1))
 (26 2 (:REWRITE <-OF-NUMERATOR-AND-DENOMINATOR-SAME))
 (25 17 (:REWRITE DEFAULT-+-2))
 (19 17 (:REWRITE DEFAULT-+-1))
 (18 6 (:REWRITE <-OF-*-OF-/-ARG1-ARG2))
 (12 4 (:REWRITE <-OF-*-OF-/-ARG2-ARG2))
 (12 4 (:DEFINITION NFIX))
 (10 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE INTEGERP-OF-*))
 (4 4 (:REWRITE DEFAULT-UNARY-/))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (4 4 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (4 4 (:DEFINITION IFIX))
 (3 3 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (3 2 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (3 2 (:REWRITE DENOMINATOR-WHEN-INTEGERP))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 )
(CEILING-UPPER-BOUND
 (580 15 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (574 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (410 410 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (410 410 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (410 410 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (410 410 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (410 410 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (200 60 (:REWRITE DEFAULT-*-2))
 (179 109 (:REWRITE DEFAULT-<-2))
 (149 49 (:REWRITE FLOOR-WHEN-<))
 (139 109 (:REWRITE DEFAULT-<-1))
 (112 16 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (106 15 (:REWRITE DEFAULT-UNARY-MINUS))
 (96 96 (:TYPE-PRESCRIPTION MOD))
 (85 36 (:REWRITE DEFAULT-+-2))
 (83 60 (:REWRITE DEFAULT-*-1))
 (59 49 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (51 49 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (49 49 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (49 49 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (46 46 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (37 37 (:REWRITE DEFAULT-UNARY-/))
 (36 36 (:REWRITE DEFAULT-+-1))
 (34 11 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (33 11 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (30 30 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (30 30 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (30 30 (:LINEAR <-OF-*-AND-*))
 (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (15 15 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (15 5 (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
 (11 11 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (11 11 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (8 8 (:REWRITE INTEGERP-OF-*))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 3 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (4 4 (:REWRITE <-OF-0-AND-FLOOR))
 (3 3 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (2 2 (:REWRITE RATIONALP-*))
 )
(CEILING-LOWER-BOUND
 (175 175 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (175 175 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (175 175 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (175 175 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (175 175 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (174 27 (:REWRITE DEFAULT-UNARY-MINUS))
 (168 54 (:REWRITE DEFAULT-*-2))
 (116 18 (:REWRITE DEFAULT-+-2))
 (76 54 (:REWRITE DEFAULT-*-1))
 (57 19 (:REWRITE FLOOR-WHEN-<))
 (49 35 (:REWRITE DEFAULT-<-1))
 (36 35 (:REWRITE DEFAULT-<-2))
 (21 3 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (19 19 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (19 19 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (19 19 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (19 19 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (18 18 (:TYPE-PRESCRIPTION MOD))
 (18 18 (:REWRITE DEFAULT-+-1))
 (17 17 (:REWRITE DEFAULT-UNARY-/))
 (16 16 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (13 4 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (12 12 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (12 12 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (12 12 (:LINEAR <-OF-*-AND-*))
 (12 4 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (6 6 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (5 3 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (4 4 (:REWRITE INTEGERP-OF-*))
 (3 3 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (3 3 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (3 3 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (2 1 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 )
(CEILING-LOWER-BOUND-LINEAR
 (3 1 (:REWRITE CEILING-WHEN-<=))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(<-OF-CEILING-ARG1
 (906 906 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (906 906 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (906 906 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (906 906 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (906 906 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (574 78 (:LINEAR <-OF-*-AND-*))
 (523 39 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (466 224 (:REWRITE DEFAULT-*-2))
 (393 57 (:REWRITE DEFAULT-UNARY-MINUS))
 (390 200 (:REWRITE DEFAULT-<-2))
 (378 12 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 (272 224 (:REWRITE DEFAULT-*-1))
 (252 84 (:REWRITE FLOOR-WHEN-<))
 (233 45 (:REWRITE DEFAULT-+-2))
 (214 200 (:REWRITE DEFAULT-<-1))
 (89 89 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (89 89 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (84 84 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (84 84 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (70 70 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (70 10 (:REWRITE *-OF-FLOOR-OF-SAME-WHEN-MULTIPLE))
 (60 60 (:TYPE-PRESCRIPTION MOD))
 (54 54 (:REWRITE DEFAULT-UNARY-/))
 (45 45 (:REWRITE DEFAULT-+-1))
 (43 43 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (39 3 (:REWRITE <-OF-FLOOR-AND-0))
 (31 9 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (27 9 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (27 9 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (16 16 (:REWRITE INTEGERP-OF-*))
 (11 3 (:LINEAR FLOOR-UPPER-BOUND-ALT-LINEAR))
 (8 8 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (7 3 (:REWRITE <-OF-0-AND-FLOOR))
 (5 5 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (4 4 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (4 2 (:REWRITE INTEGERP-OF--))
 (2 2 (:LINEAR FLOOR-UPPER-BOUND-STRONG-LINEAR-CHEAP))
 )
(<-OF-CEILING-ARG2
 (7 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE CEILING-WHEN-<=))
 (3 3 (:REWRITE DEFAULT-UNARY-/))
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 (3 1 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (2 2 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (2 2 (:LINEAR <-OF-*-AND-*))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (1 1 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
(CEILING-OF-*-SAME
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(CEILING-WHEN-MULTIPLE
 (16 2 (:REWRITE DEFAULT-+-2))
 (11 11 (:REWRITE DEFAULT-*-2))
 (11 11 (:REWRITE DEFAULT-*-1))
 (10 10 (:REWRITE DEFAULT-UNARY-/))
 (6 6 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (6 2 (:REWRITE FLOOR-WHEN-<))
 (3 3 (:REWRITE INTEGERP-OF-*))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (2 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (2 2 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (2 2 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (2 2 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(CEILING-OF-+-WHEN-MULTIPLE
 (79 23 (:REWRITE DEFAULT-+-2))
 (61 61 (:REWRITE DEFAULT-*-2))
 (61 61 (:REWRITE DEFAULT-*-1))
 (44 23 (:REWRITE DEFAULT-+-1))
 (38 4 (:REWRITE CEILING-WHEN-MULTIPLE))
 (26 26 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (26 26 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (26 26 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (26 26 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (26 26 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (26 26 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (24 3 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG2))
 (22 22 (:REWRITE DEFAULT-UNARY-/))
 (21 7 (:REWRITE FLOOR-WHEN-<))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (7 7 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (7 7 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (7 7 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (6 6 (:REWRITE INTEGERP-OF-*))
 (4 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:REWRITE FLOOR-PEEL-OFF-CONSTANT))
 (3 3 (:REWRITE FLOOR-OF-PLUS-NORMALIZE-NEGATIVE-CONSTANT))
 )
(EQUAL-OF-0-AND-CEILING
 (33 1 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (19 1 (:REWRITE <-OF-NUMERATOR-AND-DENOMINATOR-SAME))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 4 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (9 9 (:REWRITE DEFAULT-*-2))
 (9 9 (:REWRITE DEFAULT-*-1))
 (8 8 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (8 8 (:LINEAR <-OF-*-AND-*))
 (7 5 (:REWRITE DEFAULT-+-2))
 (7 1 (:REWRITE <-OF-*-OF-/-ARG2-ARG2))
 (6 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE INTEGERP-OF-*))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (4 4 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (3 3 (:REWRITE DEFAULT-UNARY-/))
 (3 1 (:DEFINITION NFIX))
 (2 1 (:REWRITE UNICITY-OF-1))
 (2 1 (:REWRITE DENOMINATOR-WHEN-INTEGERP))
 (1 1 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 (1 1 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:DEFINITION IFIX))
 )
(<-OF-0-AND-CEILING)
(CEILING-MONOTONE
 (221 221 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (221 221 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (221 221 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (221 221 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (221 221 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (221 221 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (84 28 (:REWRITE FLOOR-WHEN-<))
 (63 49 (:REWRITE DEFAULT-<-2))
 (63 49 (:REWRITE DEFAULT-<-1))
 (45 45 (:REWRITE DEFAULT-*-2))
 (45 45 (:REWRITE DEFAULT-*-1))
 (35 35 (:REWRITE DEFAULT-UNARY-/))
 (28 28 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (28 28 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (28 28 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (28 28 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (26 26 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (20 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (20 6 (:REWRITE DEFAULT-+-2))
 (12 4 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (12 4 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (9 3 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (8 8 (:REWRITE INTEGERP-OF-*))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (6 6 (:LINEAR <-OF-*-AND-*))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (2 2 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (1 1 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 )
(CEILING-UPPER-BOUND-WHEN-<-CONSTANT-LINEAR
 (52 4 (:REWRITE CEILING-WHEN-MULTIPLE))
 (27 27 (:REWRITE DEFAULT-*-2))
 (27 27 (:REWRITE DEFAULT-*-1))
 (26 2 (:REWRITE CEILING-OF-+-WHEN-MULTIPLE))
 (12 4 (:REWRITE CEILING-WHEN-<=))
 (9 9 (:REWRITE DEFAULT-UNARY-/))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 2 (:REWRITE INTEGERP-OF--))
 (2 2 (:REWRITE INTEGERP-OF-*))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(CEILING-OF-*-AND-*-CANCEL-ARG2-ARG2
 (149 6 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (66 21 (:REWRITE DEFAULT-UNARY-/))
 (56 56 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (44 30 (:REWRITE DEFAULT-*-1))
 (41 35 (:REWRITE DEFAULT-<-2))
 (36 3 (:REWRITE <-OF---OF-NUMERATOR-AND-DENOMINATOR-SAME))
 (35 35 (:REWRITE DEFAULT-<-1))
 (32 23 (:REWRITE DEFAULT-+-2))
 (30 30 (:REWRITE DEFAULT-*-2))
 (28 10 (:REWRITE <-OF-*-OF-/-ARG1-ARG2))
 (25 23 (:REWRITE DEFAULT-+-1))
 (24 3 (:REWRITE <-OF-NUMERATOR-AND-DENOMINATOR-SAME))
 (18 6 (:DEFINITION NFIX))
 (15 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (15 5 (:REWRITE <-OF-*-OF-/-ARG2-ARG2))
 (8 8 (:REWRITE RATIONALP-*))
 (8 8 (:REWRITE <-OF-*-AND-0))
 (6 6 (:DEFINITION IFIX))
 (6 2 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (5 5 (:REWRITE INTEGERP-OF-*))
 (5 5 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (4 4 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (4 4 (:LINEAR <-OF-*-AND-*))
 (3 3 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (2 2 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (2 2 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 )
