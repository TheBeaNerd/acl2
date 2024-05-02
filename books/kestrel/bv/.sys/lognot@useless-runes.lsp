(INTEGERP-ALL-ONES
 (24 24 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (22 1 (:REWRITE MOD-WHEN-MULTIPLE))
 (22 1 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (19 19 (:REWRITE DEFAULT-*-2))
 (19 19 (:REWRITE DEFAULT-*-1))
 (6 6 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (5 5 (:REWRITE DEFAULT-UNARY-/))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE MOD-WHEN-<-OF-0))
 (3 1 (:REWRITE MOD-WHEN-<))
 (1 1 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (1 1 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (1 1 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (1 1 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 (1 1 (:REWRITE EQUAL-OF-MOD-OF-+-WHEN-CONSTANTS))
 )
(LOGNOT-WHEN-NOT-INTEGERP)
(LOGNOT-OF-LOGNOT
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(<-OF-LOGNOT-ARG1-WHEN-CONSTANT
 (16 12 (:REWRITE DEFAULT-<-2))
 (14 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 )
(<-OF-LOGNOT-ARG2-WHEN-CONSTANT
 (16 12 (:REWRITE DEFAULT-<-1))
 (14 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 )
(LOGNOT-OF-ALL-ONES
 (93 93 (:TYPE-PRESCRIPTION EVENP))
 (62 31 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (62 31 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (62 31 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (49 5 (:REWRITE DEFAULT-+-2))
 (36 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (31 31 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (31 31 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (16 5 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(LOGNOT-OF---OF-EXPT
 (81 81 (:TYPE-PRESCRIPTION EVENP))
 (54 27 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (54 27 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (54 27 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (27 27 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (27 27 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (25 3 (:REWRITE DEFAULT-+-2))
 (14 3 (:REWRITE DEFAULT-+-1))
 (12 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(EQUAL-OF-LOGNOT-AND-CONSTANT
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(LOGNOT-OF-FLOOR-OF-2
 (384 16 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG1))
 (176 16 (:REWRITE INTEGERP-OF--))
 (166 118 (:REWRITE DEFAULT-*-2))
 (160 16 (:REWRITE *-OF---ARG1))
 (154 73 (:REWRITE DEFAULT-+-2))
 (150 118 (:REWRITE DEFAULT-*-1))
 (150 24 (:REWRITE FLOOR-WHEN-<))
 (115 115 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (115 115 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (115 115 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (115 115 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (115 115 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (114 40 (:REWRITE DEFAULT-UNARY-MINUS))
 (103 73 (:REWRITE DEFAULT-+-1))
 (86 62 (:REWRITE DEFAULT-<-1))
 (70 62 (:REWRITE DEFAULT-<-2))
 (66 3 (:LINEAR MOD-BOUND-LINEAR-ARG2))
 (64 8 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (64 8 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (60 7 (:REWRITE MOD-WHEN-MULTIPLE))
 (42 26 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (42 26 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (42 26 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (37 21 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (33 11 (:REWRITE MOD-WHEN-<-OF-0))
 (32 16 (:DEFINITION FIX))
 (29 29 (:REWRITE INTEGERP-OF-*))
 (26 26 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (21 7 (:REWRITE MOD-WHEN-<))
 (17 17 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (16 16 (:REWRITE FLOOR-OF-PLUS-NORMALIZE-NEGATIVE-CONSTANT))
 (16 16 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG2))
 (12 2 (:REWRITE FLOOR-OF-ONE-LESS-GEN))
 (9 3 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (8 8 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (8 8 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (8 2 (:DEFINITION NATP))
 (7 7 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (7 7 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (7 7 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (7 7 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (7 7 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
 (6 2 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(FLOOR-OF-LOGNOT-AND-2)
(LOGNOT-OF-*-OF-2
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 )
(LOGNOT-OF-+-1-OF-*-2
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 )
(INTEGERP-OF-*-1/2-OF-LOGNOT
 (8 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (2 2 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (2 2 (:REWRITE INTEGERP-OF-*))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(MOD-OF-LOGNOT-OF-2
 (1071 66 (:REWRITE MOD-WHEN-MULTIPLE))
 (1071 66 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (745 5 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 (556 114 (:REWRITE COMMUTATIVITY-OF-*))
 (440 124 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (439 66 (:REWRITE MOD-WHEN-<-OF-0))
 (352 248 (:REWRITE DEFAULT-*-2))
 (336 248 (:REWRITE DEFAULT-*-1))
 (306 30 (:REWRITE INTEGERP-OF--))
 (282 30 (:REWRITE *-OF---ARG1))
 (256 42 (:REWRITE MOD-WHEN-<))
 (242 10 (:REWRITE INTEGERP-OF-+-OF---AND--))
 (196 10 (:REWRITE INTEGERP-OF-+-OF-1/2-AND-*-OF-1/2))
 (183 102 (:REWRITE DEFAULT-<-1))
 (162 80 (:REWRITE DEFAULT-+-2))
 (139 80 (:REWRITE DEFAULT-+-1))
 (126 10 (:REWRITE DISTRIBUTIVITY))
 (124 124 (:REWRITE INTEGERP-OF-*))
 (114 102 (:REWRITE DEFAULT-<-2))
 (96 61 (:REWRITE DEFAULT-UNARY-MINUS))
 (93 15 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (74 42 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (74 42 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (74 42 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (74 42 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
 (66 66 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (56 10 (:REWRITE *-OF---ARG2))
 (54 30 (:DEFINITION FIX))
 (42 42 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (21 3 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (5 5 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG2))
 (5 5 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG1))
 (2 2 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 )
(<-OF-LOGNOT-AND-EXPT
 (618 618 (:TYPE-PRESCRIPTION EVENP))
 (412 206 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (412 206 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (412 206 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (206 206 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (206 206 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (63 19 (:REWRITE DEFAULT-<-2))
 (52 19 (:REWRITE DEFAULT-<-1))
 (32 10 (:REWRITE DEFAULT-+-2))
 (28 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (12 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (10 10 (:REWRITE DEFAULT-+-1))
 (6 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (6 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (6 2 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
(MOD-OF-LOGNOT-AND-EXPT
 (45723 10 (:REWRITE INTEGERP-OF-+-OF---AND--))
 (45401 235 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (45237 18 (:REWRITE INTEGERP-ALL-ONES))
 (33953 235 (:REWRITE MOD-WHEN-MULTIPLE))
 (19416 19416 (:TYPE-PRESCRIPTION EVENP))
 (17914 178 (:REWRITE MOD-WHEN-<))
 (12944 6472 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (12944 6472 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (12944 6472 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (8142 354 (:REWRITE DEFAULT-UNARY-/))
 (6472 6472 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (6472 6472 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (4631 235 (:REWRITE MOD-WHEN-<-OF-0))
 (4406 414 (:REWRITE DEFAULT-*-2))
 (4119 23 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 (4068 167 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (3310 271 (:REWRITE DEFAULT-+-2))
 (2724 225 (:DEFINITION FIX))
 (2520 271 (:REWRITE DEFAULT-+-1))
 (2456 60 (:REWRITE INTEGERP-OF--))
 (2448 54 (:REWRITE COMMUTATIVITY-OF-*))
 (2423 1377 (:REWRITE DEFAULT-<-2))
 (2338 334 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (2338 334 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (2220 174 (:REWRITE INTEGERP-OF-*))
 (2216 178 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (2180 18 (:REWRITE DISTRIBUTIVITY))
 (2136 178 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (1959 1377 (:REWRITE DEFAULT-<-1))
 (1950 150 (:REWRITE UNICITY-OF-1))
 (1830 15 (:REWRITE <-OF---AND--))
 (1498 154 (:REWRITE DEFAULT-UNARY-MINUS))
 (1459 167 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (1396 233 (:REWRITE INTEGERP-OF-/-OF-EXPT-2))
 (1184 414 (:REWRITE DEFAULT-*-1))
 (998 334 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (954 20 (:REWRITE *-OF---ARG2))
 (881 83 (:REWRITE *-OF---ARG1))
 (601 601 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (522 167 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (334 334 (:LINEAR EXPT-BOUND-LINEAR))
 (334 334 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (334 334 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (307 167 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (258 178 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (258 178 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (243 81 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (235 235 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (167 167 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (167 167 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (167 167 (:LINEAR EXPT-BOUND-LINEAR-2))
 (93 15 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (48 48 (:REWRITE FOLD-CONSTS-IN-+))
 (18 2 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (5 5 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG2))
 (5 5 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG1))
 )
(MOD-OF-LOGNOT-OF-MOD-OF-EXPT-AND-EXPT
 (36252 244 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (29020 243 (:REWRITE MOD-WHEN-MULTIPLE))
 (25901 15 (:REWRITE INTEGERP-OF-+-OF---AND--))
 (24924 10 (:REWRITE INTEGERP-ALL-ONES))
 (19869 19869 (:TYPE-PRESCRIPTION EVENP))
 (15994 171 (:REWRITE MOD-WHEN-<))
 (13246 6623 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (13246 6623 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (13246 6623 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (9131 397 (:REWRITE DEFAULT-UNARY-/))
 (7653 244 (:REWRITE MOD-WHEN-<-OF-0))
 (6623 6623 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (6623 6623 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (6075 19 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 (4837 517 (:REWRITE DEFAULT-*-2))
 (4150 92 (:REWRITE INTEGERP-OF--))
 (3914 128 (:REWRITE COMMUTATIVITY-OF-*))
 (3870 160 (:LINEAR <-OF-EXPT2-SAME-LINEAR))
 (3252 268 (:DEFINITION FIX))
 (3075 263 (:REWRITE DEFAULT-+-2))
 (2959 263 (:REWRITE DEFAULT-+-1))
 (2806 23 (:REWRITE <-OF---AND--))
 (2436 1381 (:REWRITE DEFAULT-<-2))
 (2418 19 (:REWRITE DISTRIBUTIVITY))
 (2328 198 (:REWRITE INTEGERP-OF-*))
 (2240 320 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (2240 320 (:LINEAR <=-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (2214 517 (:REWRITE DEFAULT-*-1))
 (2124 171 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (2101 221 (:REWRITE DEFAULT-UNARY-MINUS))
 (2052 171 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (1989 153 (:REWRITE UNICITY-OF-1))
 (1961 1381 (:REWRITE DEFAULT-<-1))
 (1692 110 (:REWRITE *-OF---ARG1))
 (1610 160 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (1530 255 (:REWRITE INTEGERP-OF-/-OF-EXPT-2))
 (1325 30 (:REWRITE *-OF---ARG2))
 (960 320 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (800 80 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (596 596 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (480 160 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (320 320 (:LINEAR EXPT-BOUND-LINEAR))
 (320 320 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (320 320 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (270 90 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (254 160 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (244 244 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (243 171 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (243 171 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (160 160 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (160 160 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (160 160 (:LINEAR EXPT-BOUND-LINEAR-2))
 (141 23 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (36 36 (:REWRITE FOLD-CONSTS-IN-+))
 (30 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (9 9 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG2))
 (9 9 (:REWRITE MOD-OF-+-OF---WHEN-EQUAL-OF-MOD-ARG1))
 )
(FLOOR-OF-LOGNOT-AND-EXPT
 (8613 8613 (:TYPE-PRESCRIPTION EVENP))
 (6537 52 (:REWRITE FLOOR-WHEN-<))
 (5742 2871 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (5742 2871 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (5742 2871 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (4074 39 (:REWRITE MOD-WHEN-<))
 (3585 48 (:REWRITE MOD-WHEN-MULTIPLE))
 (2871 2871 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (2871 2871 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (2835 129 (:REWRITE DEFAULT-UNARY-/))
 (1895 101 (:REWRITE DEFAULT-+-2))
 (1481 142 (:REWRITE DEFAULT-*-2))
 (1478 649 (:REWRITE DEFAULT-<-2))
 (1198 52 (:REWRITE MOD-WHEN-<-OF-0))
 (1124 74 (:REWRITE DEFAULT-UNARY-MINUS))
 (1038 101 (:REWRITE DEFAULT-+-1))
 (944 24 (:REWRITE INTEGERP-OF--))
 (940 76 (:REWRITE INTEGERP-OF-*))
 (907 649 (:REWRITE DEFAULT-<-1))
 (732 6 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG1))
 (558 6 (:REWRITE FLOOR-OF-+-WHEN-MULT-ARG2))
 (550 90 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (542 60 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (520 180 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (488 4 (:REWRITE <-OF---AND--))
 (443 39 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (435 39 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (406 71 (:REWRITE INTEGERP-OF-/-OF-EXPT-2))
 (359 142 (:REWRITE DEFAULT-*-1))
 (349 25 (:REWRITE *-OF---ARG1))
 (338 338 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (338 338 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (338 338 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (338 338 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (338 338 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (319 319 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (269 7 (:REWRITE FLOOR-PEEL-OFF-CONSTANT))
 (242 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (202 90 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (180 180 (:LINEAR EXPT-BOUND-LINEAR))
 (180 180 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (180 180 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (90 90 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (90 90 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (90 90 (:LINEAR EXPT-BOUND-LINEAR-2))
 (88 52 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (75 25 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (57 33 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (52 52 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (52 52 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (47 39 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (47 39 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (31 5 (:REWRITE <-OF-MINUS-AND-CONSTANT))
 (16 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (14 14 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE))
 (14 9 (:REWRITE FLOOR-OF-ONE-LESS-GEN))
 (12 4 (:LINEAR MOD-BOUND-LINEAR-ARG1))
 (8 8 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (7 7 (:REWRITE FLOOR-OF-PLUS-NORMALIZE-NEGATIVE-CONSTANT))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE MOD-OF-+-SUBST-CONSTANT))
 )
(<-OF---AND-LOGNOT
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(<-OF-LOGNOT-AND---OF-EXPT
 (405 405 (:TYPE-PRESCRIPTION EVENP))
 (270 135 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (270 135 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (270 135 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (135 135 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (135 135 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (60 16 (:REWRITE DEFAULT-<-2))
 (26 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:REWRITE DEFAULT-<-1))
 (12 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR))
 (10 10 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (6 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-4))
 (6 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-2))
 (6 2 (:LINEAR <=-OF-2-AND-EXPT2-LINEAR))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-EXPONENTS-LINEAR-NEGATIVE-EXPONENT))
 (4 4 (:LINEAR <-OF-EXPT-AND-EXPT-SAME-BASE-LINEAR))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-3))
 (2 2 (:LINEAR EXPT-WHEN-NEGATIVE-EXPONENT-LINEAR-1))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
(LOGNOT-OF-+-OF-EXPT
 (108 108 (:TYPE-PRESCRIPTION EVENP))
 (72 36 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (72 36 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (72 36 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (66 11 (:REWRITE DEFAULT-+-2))
 (55 11 (:REWRITE DEFAULT-+-1))
 (38 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (36 36 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NON-POSITIVE-EXPONENT))
 (36 36 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(SIGNED-BYTE-P-OF-LOGNOT
 (147 147 (:TYPE-PRESCRIPTION EVENP))
 (98 49 (:TYPE-PRESCRIPTION EXPT-TYPE-ODD-EXPONENT-NEGATIVE-BASE))
 (98 49 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-2))
 (98 49 (:TYPE-PRESCRIPTION EXPT-TYPE-EVEN-EXPONENT-1))
 (49 49 (:TYPE-PRESCRIPTION EXPT-TYPE-SMALL-BASE-NEGATIVE-EXPONENT))
 (39 6 (:REWRITE DEFAULT-<-2))
 (36 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (17 6 (:REWRITE DEFAULT-<-1))
 (14 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE EXPT-WHEN-NOT-ACL2-NUMBERP-CHEAP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE LOGNOT-WHEN-NOT-INTEGERP))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-MINUS))
 )
(EQUAL-OF-LOGNOT-AND-LOGNOT
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
