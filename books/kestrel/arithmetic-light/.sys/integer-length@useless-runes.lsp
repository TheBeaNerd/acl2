(INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP)
(INTEGER-LENGTH-BOUND
 (254 21 (:REWRITE FLOOR-WHEN-<))
 (145 145 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (145 145 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (145 145 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (145 145 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (145 145 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (64 6 (:REWRITE ZIP-OPEN))
 (53 29 (:REWRITE DEFAULT-<-2))
 (51 9 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (43 29 (:REWRITE DEFAULT-<-1))
 (35 21 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (35 21 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (35 21 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (27 6 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (21 21 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (19 19 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (19 15 (:REWRITE DEFAULT-*-2))
 (18 2 (:REWRITE FLOOR-OF-FLOOR))
 (15 15 (:REWRITE DEFAULT-*-1))
 (15 9 (:REWRITE DEFAULT-+-2))
 (15 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (14 2 (:REWRITE EQUAL-OF-0-AND-FLOOR-GEN))
 (12 12 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (12 12 (:LINEAR EXPT-BOUND-LINEAR))
 (9 9 (:REWRITE DEFAULT-+-1))
 (8 4 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (8 1 (:REWRITE FLOOR-UNIQUE-EQUAL-VERSION))
 (6 6 (:LINEAR EXPT-BOUND-LINEAR-2))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 )
(INTEGER-LENGTH-OF-EXPT2
 (128 4 (:REWRITE FLOOR-OF-EXPT-2-AND-2))
 (52 10 (:REWRITE DEFAULT-*-2))
 (49 8 (:REWRITE ZIP-OPEN))
 (38 34 (:REWRITE DEFAULT-+-2))
 (34 34 (:REWRITE DEFAULT-+-1))
 (25 25 (:REWRITE DEFAULT-<-2))
 (25 25 (:REWRITE DEFAULT-<-1))
 (22 8 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (20 16 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (15 6 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (14 4 (:DEFINITION POSP))
 (12 12 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (10 10 (:REWRITE DEFAULT-*-1))
 (8 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (8 2 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (4 4 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (4 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (4 1 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (4 1 (:REWRITE FLOOR-WHEN-<))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (1 1 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 )
(INTEGER-LENGTH-OF-MASK
 (88 3 (:REWRITE FLOOR-OF-EXPT-2-AND-2))
 (57 28 (:REWRITE DEFAULT-+-2))
 (50 14 (:REWRITE DEFAULT-*-2))
 (44 27 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (32 8 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (28 28 (:REWRITE DEFAULT-+-1))
 (26 14 (:REWRITE DEFAULT-*-1))
 (24 6 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (16 4 (:REWRITE MOD-WHEN-<-OF-0))
 (12 5 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (12 5 (:REWRITE +-COMBINE-CONSTANTS))
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (11 3 (:REWRITE EQUAL-OF-1-AND-EXPT))
 (8 2 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (7 3 (:REWRITE INTEGERP-OF-*-OF-1/2-AND-EXPT-2))
 (6 6 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (4 4 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (4 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (4 1 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (4 1 (:REWRITE FLOOR-WHEN-<))
 (3 3 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (3 3 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (3 3 (:REWRITE INTEGERP-OF-*))
 (3 3 (:DEFINITION IFIX))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (1 1 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 )
(DOUBLE-FLOOR-BY-2-INDUCT
 (37 37 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (37 37 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (37 37 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (19 5 (:REWRITE DEFAULT-<-1))
 (9 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 4 (:REWRITE FLOOR-WHEN-<))
 (5 5 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (4 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (4 4 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (4 4 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (4 4 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE ZIP-OPEN))
 (2 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (1 1 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 )
(INTEGER-LENGTH-MONOTONIC
 (1260 70 (:REWRITE FLOOR-WHEN-<))
 (236 8 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (234 8 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (221 221 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (221 221 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (221 221 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (221 221 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (221 221 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (208 8 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (194 8 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (138 8 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (120 6 (:REWRITE ZIP-OPEN))
 (116 8 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (98 70 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (98 70 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (98 70 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (82 12 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (70 70 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (66 66 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (64 62 (:REWRITE DEFAULT-<-2))
 (64 62 (:REWRITE DEFAULT-<-1))
 (48 16 (:REWRITE COMMUTATIVITY-OF-*))
 (36 4 (:REWRITE FLOOR-OF-FLOOR))
 (33 5 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (32 32 (:REWRITE DEFAULT-*-2))
 (32 32 (:REWRITE DEFAULT-*-1))
 (26 17 (:REWRITE DEFAULT-+-2))
 (26 4 (:REWRITE EQUAL-OF-0-AND-FLOOR-GEN))
 (17 17 (:REWRITE DEFAULT-+-1))
 (13 5 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (1 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 )
(INTEGER-LENGTH-OF-TIMES-2
 (20 6 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (10 5 (:REWRITE DEFAULT-+-2))
 (7 3 (:REWRITE FLOOR-WHEN-<))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (4 4 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (3 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (3 3 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (3 3 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION FLOOR))
 (2 2 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(INTEGER-LENGTH-OF-FLOOR-BY-2
 (269 17 (:REWRITE FLOOR-WHEN-<))
 (62 2 (:REWRITE ZIP-OPEN))
 (56 2 (:LINEAR MY-FLOOR-LOWER-BOUND-LINEAR))
 (52 2 (:LINEAR FLOOR-UPPER-BOUND-LINEAR))
 (43 43 (:TYPE-PRESCRIPTION FLOOR))
 (43 43 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (43 43 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (43 43 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (43 43 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (43 43 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (43 43 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (42 2 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (41 6 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (31 17 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (31 17 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (31 17 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (28 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (28 2 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (18 2 (:REWRITE FLOOR-OF-FLOOR))
 (17 17 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (16 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (16 2 (:REWRITE EQUAL-OF-0-AND-FLOOR-GEN))
 (15 15 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 7 (:REWRITE DEFAULT-+-2))
 (12 4 (:REWRITE COMMUTATIVITY-OF-*))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (2 2 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 )
(FLOOR-BY-2-BOUND-EVEN-LINEAR
 (373 373 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (373 373 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (373 373 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (373 373 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (373 373 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (52 24 (:REWRITE DEFAULT-<-1))
 (40 14 (:REWRITE FLOOR-WHEN-<))
 (38 24 (:REWRITE DEFAULT-<-2))
 (30 30 (:REWRITE DEFAULT-*-2))
 (30 30 (:REWRITE DEFAULT-*-1))
 (14 14 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (14 14 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (14 14 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (14 14 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (14 14 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (8 2 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (6 6 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (6 6 (:LINEAR <-OF-*-AND-*))
 (4 4 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (3 3 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (2 2 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (2 2 (:REWRITE INTEGERP-OF-*))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (1 1 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 )
(<-OF-1-AND-FLOOR-OF-2
 (48 48 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (48 48 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (48 48 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (48 48 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (48 48 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (14 7 (:REWRITE DEFAULT-<-2))
 (10 6 (:REWRITE FLOOR-WHEN-<))
 (7 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (6 6 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (6 6 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (6 6 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (6 6 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (6 6 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-*-1))
 (4 2 (:LINEAR FLOOR-BY-2-BOUND-EVEN-LINEAR))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:DEFINITION NATP))
 )
(EQUAL-OF-0-AND-INTEGER-LENGTH
 (9 2 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (3 1 (:REWRITE FLOOR-WHEN-<))
 (2 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:TYPE-PRESCRIPTION FLOOR))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (1 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (1 1 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (1 1 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (1 1 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(EQUAL-OF-1-AND-INTEGER-LENGTH
 (17 3 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (11 3 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (6 2 (:REWRITE FLOOR-WHEN-<))
 (5 5 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (5 5 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (5 5 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (5 5 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (5 5 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (2 2 (:REWRITE ZIP-OPEN))
 (2 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (2 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (2 2 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (2 2 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (2 2 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(<-OF-1-AND-INTEGER-LENGTH
 (42 42 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (42 42 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (42 42 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (42 42 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (42 42 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (30 9 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (26 10 (:REWRITE FLOOR-WHEN-<))
 (22 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-<-1))
 (16 9 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (10 10 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (10 10 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (10 10 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (10 10 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (9 9 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (1 1 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (1 1 (:LINEAR FLOOR-BY-2-BOUND-EVEN-LINEAR))
 )
(UNSIGNED-BYTE-P-OF-INTEGER-LENGTH
 (21 1 (:DEFINITION INTEGER-LENGTH))
 (9 2 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (5 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-<-2))
 (3 1 (:REWRITE FLOOR-WHEN-<))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:TYPE-PRESCRIPTION FLOOR))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (1 1 (:REWRITE ZIP-OPEN))
 (1 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (1 1 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (1 1 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (1 1 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (1 1 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(UNSIGNED-BYTE-P-OF-INTEGER-LENGTH-GEN
 (11 7 (:REWRITE DEFAULT-<-2))
 (8 7 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (2 2 (:LINEAR EXPT-BOUND-LINEAR))
 (1 1 (:LINEAR EXPT-BOUND-LINEAR-2))
 )
(UNSIGNED-BYTE-P-INTEGER-LENGTH-ONE-LESS
 (258 2 (:DEFINITION INTEGER-LENGTH))
 (105 1 (:REWRITE FLOOR-OF-PLUS-NORMALIZE-NEGATIVE-CONSTANT))
 (74 2 (:REWRITE FLOOR-OF-ONE-LESS-GEN))
 (72 2 (:REWRITE FLOOR-PEEL-OFF-CONSTANT))
 (43 7 (:REWRITE DEFAULT-+-2))
 (41 4 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (22 18 (:REWRITE DEFAULT-<-2))
 (22 18 (:REWRITE DEFAULT-<-1))
 (22 2 (:REWRITE MOD-WHEN-MULTIPLE))
 (22 2 (:REWRITE MOD-WHEN-INTEGERP-OF-QUOTIENT))
 (21 6 (:REWRITE FLOOR-WHEN-<))
 (16 4 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (16 4 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (14 14 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (14 14 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (14 14 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (12 4 (:REWRITE COMMUTATIVITY-OF-*))
 (12 2 (:REWRITE ZIP-OPEN))
 (8 8 (:TYPE-PRESCRIPTION FLOOR))
 (8 8 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (8 8 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (8 8 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (8 8 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (8 8 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (8 8 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (7 7 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (6 6 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (6 6 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (6 2 (:REWRITE MOD-WHEN-<-OF-0))
 (6 2 (:REWRITE MOD-WHEN-<))
 (4 4 (:REWRITE INTEGERP-OF-*))
 (4 4 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (4 4 (:DEFINITION FIX))
 (4 2 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (4 2 (:DEFINITION NATP))
 (3 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE MOD-WHEN-RATIONALP-ARG1-AND-NOT-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-RATIONALP-ARG1-AND-RATIONALP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG2))
 (2 2 (:REWRITE MOD-WHEN-NOT-ACL2-NUMBERP-ARG1))
 (2 2 (:REWRITE MOD-WHEN-EQUAL-OF-MOD-AND-0-FREE-CHEAP))
 (2 2 (:REWRITE MOD-OF-2-WHEN-EVEN-CHEAP))
 )
(<-OF-INTEGER-LENGTH-AND-1
 (123 3 (:REWRITE EQUAL-OF-0-AND-INTEGER-LENGTH))
 (101 4 (:DEFINITION NATP))
 (47 47 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (47 47 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (47 47 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (47 47 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (47 47 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (47 47 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (38 10 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (33 11 (:REWRITE FLOOR-WHEN-<))
 (27 25 (:REWRITE DEFAULT-<-1))
 (25 25 (:REWRITE DEFAULT-<-2))
 (14 9 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE DEFAULT-*-1))
 (11 11 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (11 11 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (11 11 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (11 11 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (11 11 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (9 9 (:REWRITE DEFAULT-+-1))
 (9 3 (:LINEAR FLOOR-BOUND-STRICT-LINEAR))
 (9 3 (:LINEAR FLOOR-BOUND-ARG1-LINEAR))
 (5 1 (:REWRITE NATP-OF-FLOOR))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (3 3 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (3 3 (:LINEAR FLOOR-BY-2-BOUND-EVEN-LINEAR))
 (3 1 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 (1 1 (:REWRITE ZIP-OPEN))
 )
(SUB1-INDUCT)
(INTEGER-LENGTH-OF-*-OF-EXPT2
 (633 3 (:LINEAR <-OF-*-SAME-LINEAR-SPECIAL))
 (493 7 (:REWRITE FLOOR-WHEN-<))
 (333 3 (:LINEAR EXPT-HALF-LINEAR))
 (248 1 (:REWRITE INTEGER-LENGTH-OF-TIMES-2))
 (240 3 (:LINEAR EXPT-OF-ONE-LESS-LINEAR))
 (240 1 (:DEFINITION POSP))
 (198 42 (:REWRITE DEFAULT-*-2))
 (132 20 (:REWRITE ZIP-OPEN))
 (105 85 (:REWRITE DEFAULT-+-2))
 (94 85 (:REWRITE DEFAULT-+-1))
 (79 68 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (72 18 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (68 14 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (63 21 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (45 39 (:REWRITE DEFAULT-<-1))
 (42 42 (:REWRITE DEFAULT-*-1))
 (42 39 (:REWRITE DEFAULT-<-2))
 (18 18 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (18 18 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (17 8 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (17 8 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (13 7 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (13 7 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (12 3 (:REWRITE <-OF-1-AND-EXPT-GEN))
 (11 1 (:REWRITE EQUAL-OF-0-AND-*))
 (9 6 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (7 7 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (6 6 (:TYPE-PRESCRIPTION FLOOR))
 (6 6 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (6 6 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (6 6 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (6 6 (:LINEAR EXPT-BOUND-LINEAR-2))
 (6 6 (:LINEAR EXPT-BOUND-LINEAR))
 (6 6 (:LINEAR <=-OF-*-AND-*-SAME-LINEAR))
 (6 6 (:LINEAR <=-OF-*-AND-*-SAME-ALT-LINEAR))
 (6 6 (:LINEAR <-OF-*-AND-*))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-4))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-3))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-2))
 (3 3 (:LINEAR <-OF-*-AND-*-SAME-LINEAR-1))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 )
(INTEGER-LENGTH-OF-*-OF-1/2
 (88 4 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (32 21 (:REWRITE DEFAULT-+-2))
 (23 21 (:REWRITE DEFAULT-+-1))
 (20 6 (:REWRITE COMMUTATIVITY-OF-+))
 (19 19 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE DEFAULT-<-1))
 (16 4 (:REWRITE <-OF-CONSTANT-AND-*-OF-CONSTANT))
 (16 4 (:REWRITE <-OF-*-AND-0))
 (16 2 (:REWRITE <-OF-NUMERATOR-AND-DENOMINATOR-SAME))
 (16 2 (:REWRITE <-OF---OF-NUMERATOR-AND-DENOMINATOR-SAME))
 (14 14 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (14 13 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (12 4 (:DEFINITION NFIX))
 (12 3 (:REWRITE MULTIPLE-WHEN-MOD-0-CHEAP))
 (12 2 (:REWRITE <-OF-NUMERATOR-AND-0))
 (11 4 (:REWRITE EQUAL-OF-*-AND-CONSTANT))
 (10 10 (:REWRITE DEFAULT-*-2))
 (10 10 (:REWRITE DEFAULT-*-1))
 (10 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 6 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (9 3 (:REWRITE FLOOR-WHEN-<))
 (9 2 (:REWRITE ZIP-OPEN))
 (8 8 (:DEFINITION FIX))
 (6 2 (:REWRITE *-OF-*-COMBINE-CONSTANTS))
 (4 4 (:DEFINITION IFIX))
 (3 3 (:TYPE-PRESCRIPTION RATIONALP-OF-MOD))
 (3 3 (:TYPE-PRESCRIPTION NONNEG-OF-MOD-TYPE-2))
 (3 3 (:TYPE-PRESCRIPTION INTEGERP-OF-MOD-TYPE))
 (3 3 (:REWRITE INTEGERP-OF-*))
 (3 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (3 3 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (3 3 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (3 3 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (3 3 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (3 3 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 )
(<-OF-INTEGER-LENGTH-ARG2
 (491 491 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (288 135 (:REWRITE DEFAULT-+-2))
 (185 59 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (180 135 (:REWRITE DEFAULT-+-1))
 (169 169 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (169 169 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (169 169 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (169 169 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (169 169 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (153 89 (:REWRITE DEFAULT-<-2))
 (101 50 (:REWRITE DEFAULT-*-2))
 (96 89 (:REWRITE DEFAULT-<-1))
 (74 74 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (74 74 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (74 74 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (74 74 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (64 64 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (50 50 (:REWRITE DEFAULT-*-1))
 (10 10 (:LINEAR FLOOR-BY-2-BOUND-EVEN-LINEAR))
 (9 9 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (9 9 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (1 1 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 )
(<-OF-EXPT-OF-ONE-LESS-OF-INTEGER-LENGTH
 (233 233 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (91 48 (:REWRITE DEFAULT-+-2))
 (88 88 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (88 88 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (88 88 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (88 88 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (88 88 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (62 36 (:REWRITE DEFAULT-<-2))
 (54 48 (:REWRITE DEFAULT-+-1))
 (45 17 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (43 36 (:REWRITE DEFAULT-<-1))
 (39 27 (:REWRITE DEFAULT-*-2))
 (34 34 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (34 34 (:LINEAR EXPT-BOUND-LINEAR))
 (29 29 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (29 29 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (29 29 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (29 29 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (27 27 (:REWRITE DEFAULT-*-1))
 (25 25 (:LINEAR EXPT-BOUND-LINEAR-2))
 (24 24 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (8 1 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (5 5 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (5 5 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (5 5 (:LINEAR FLOOR-BY-2-BOUND-EVEN-LINEAR))
 (1 1 (:REWRITE <-OF-FLOOR-OF-CONSTANT-AND-CONSTANT-GEN))
 )
(<-OF-EXPT-OF-ONE-LESS-OF-INTEGER-LENGTH-LINEAR
 (40 2 (:DEFINITION INTEGER-LENGTH))
 (35 35 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (18 4 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (13 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE FLOOR-WHEN-<))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR-WEAK))
 (4 4 (:LINEAR EXPT-BOUND-LINEAR))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:LINEAR EXPT-BOUND-LINEAR-2))
 (2 2 (:TYPE-PRESCRIPTION FLOOR))
 (2 2 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONNEGATIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (2 2 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (2 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (2 2 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (2 2 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (2 2 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (2 2 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(<-OF-INTEGER-LENGTH-ARG1
 (265 265 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (143 100 (:REWRITE DEFAULT-+-2))
 (128 37 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 (109 100 (:REWRITE DEFAULT-+-1))
 (108 40 (:REWRITE FLOOR-WHEN-<))
 (94 63 (:REWRITE DEFAULT-<-2))
 (83 83 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONPOSITIVE-AND-NONNEGATIVE-TYPE))
 (83 83 (:TYPE-PRESCRIPTION <=-OF-FLOOR-AND-0-WHEN-NONNEGATIVE-AND-NONPOSITIVE-TYPE))
 (83 83 (:TYPE-PRESCRIPTION <=-OF-0-AND-FLOOR-WHEN-BOTH-NONPOSITIVE-TYPE))
 (83 83 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-POSITIVE-AND-NEGATIVE-TYPE))
 (83 83 (:TYPE-PRESCRIPTION <-OF-FLOOR-AND-0-WHEN-NEGATIVE-AND-POSITIVE-TYPE))
 (69 63 (:REWRITE DEFAULT-<-1))
 (40 40 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-OF-QUOTIENT))
 (40 40 (:REWRITE FLOOR-WHEN-NOT-RATIONALP-ARG1))
 (40 40 (:REWRITE FLOOR-WHEN-NEGATIVE-AND-SMALL-CHEAP))
 (40 40 (:REWRITE FLOOR-WHEN-I-IS-NOT-AN-ACL2-NUMBERP))
 (40 40 (:REWRITE FLOOR-MINUS-NEGATIVE-CONSTANT))
 (36 27 (:REWRITE DEFAULT-*-2))
 (27 27 (:REWRITE DEFAULT-*-1))
 (5 5 (:LINEAR FLOOR-BY-2-BOUND-EVEN-LINEAR))
 (4 4 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR=-2))
 (4 4 (:LINEAR FLOOR-WEAK-MONOTONE-LINEAR-1))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (1 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 )
(<-OF-EXPT-2-AND-CONSTANT
 (7 4 (:REWRITE DEFAULT-<-2))
 (7 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION NATP-OF-EXPT))
 (1 1 (:REWRITE INTEGER-LENGTH-WHEN-NOT-INTEGERP-CHEAP))
 )
