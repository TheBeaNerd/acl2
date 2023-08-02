(INT-C-MOD::CEILING-AS-FLOOR
 (68 6 (:REWRITE NIQ-TYPE . 3))
 (54 38 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (32 4 (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
 (28 28 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (25 25 (:REWRITE DEFAULT-*-2))
 (25 25 (:REWRITE DEFAULT-*-1))
 (24 6 (:REWRITE COMMUTATIVITY-OF-*))
 (19 19 (:REWRITE DEFAULT-UNARY-/))
 (16 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 6 (:REWRITE NIQ-TYPE . 2))
 (11 5 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (7 5 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (6 6 (:REWRITE RATIONAL-IMPLIES2))
 (6 2 (:LINEAR X*Y>1-POSITIVE))
 (5 5 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 )
(INT-C-MOD::CLOSURE-LAWS)
(INT-C-MOD::EQUIVALENCE-LAW)
(INT-C-MOD::CONGRUENCE-LAWS)
(INT-C-MOD::CLOSURE-OF-IDENTITY)
(INT-C-MOD::EQUIVALENCE-CLASS-LAWS)
(INT-C-MOD::COMMUTATIVITY-LAWS
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 )
(INT-C-MOD::ASSOCIATIVITY-LAWS)
(INT-C-MOD::LEFT-DISTRIBUTIVITY-LAW
 (6 2 (:LINEAR X*Y>1-POSITIVE))
 (5 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(INT-C-MOD::LEFT-UNICITY-LAWS)
(INT-C-MOD::RIGHT-INVERSE-LAW
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(INT-C-MOD::ZERO-DIVISOR-LAW
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(INT-C-MOD::NATP-ABS
 (14 14 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:TYPE-PRESCRIPTION INT-C-MOD::NATP-ABS))
 )
(INT-C-MOD::CONGRUENCE-FOR-ABS)
(INT-C-MOD::C-MOD)
(INT-C-MOD::CLOSURE-OF-CEILING-&-C-MOD
 (22 12 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (18 3 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (16 2 (:REWRITE FLOOR-=-X/Y . 2))
 (12 7 (:REWRITE DEFAULT-*-2))
 (12 4 (:REWRITE FLOOR-TYPE-4 . 3))
 (12 4 (:REWRITE FLOOR-TYPE-4 . 2))
 (12 4 (:REWRITE FLOOR-TYPE-3 . 3))
 (12 4 (:REWRITE FLOOR-TYPE-3 . 2))
 (10 10 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (7 7 (:REWRITE DEFAULT-*-1))
 (6 6 (:REWRITE DEFAULT-UNARY-/))
 (6 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-+-1))
 )
(INT-C-MOD::CONGRUENCE-FOR-CEILING-&-C-MOD)
(INT-C-MOD::DIVISION-PROPERTY
 (1418 1418 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (1418 1418 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (1418 1418 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (1418 1418 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (859 594 (:REWRITE DEFAULT-*-2))
 (652 289 (:REWRITE DEFAULT-+-2))
 (599 594 (:REWRITE DEFAULT-*-1))
 (483 370 (:REWRITE DEFAULT-<-1))
 (435 370 (:REWRITE DEFAULT-<-2))
 (292 192 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (289 289 (:REWRITE DEFAULT-+-1))
 (284 40 (:REWRITE FLOOR-=-X/Y . 2))
 (132 44 (:REWRITE FLOOR-TYPE-4 . 3))
 (132 44 (:REWRITE FLOOR-TYPE-4 . 2))
 (132 44 (:REWRITE FLOOR-TYPE-3 . 3))
 (132 44 (:REWRITE FLOOR-TYPE-3 . 2))
 (125 64 (:REWRITE DEFAULT-UNARY-MINUS))
 (100 100 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (96 96 (:REWRITE DEFAULT-UNARY-/))
 (40 20 (:LINEAR X*Y>1-POSITIVE))
 (21 21 (:REWRITE FOLD-CONSTS-IN-*))
 (16 16 (:REWRITE EQUAL-CONSTANT-+))
 (3 3 (:REWRITE <-*-/-LEFT))
 (1 1 (:REWRITE <-UNARY-/-POSITIVE-RIGHT))
 )
(INT-C-MOD::ABS-*
 (84 76 (:REWRITE DEFAULT-<-2))
 (80 76 (:REWRITE DEFAULT-<-1))
 (43 8 (:LINEAR X*Y>1-POSITIVE))
 (37 36 (:REWRITE DEFAULT-*-2))
 (37 36 (:REWRITE DEFAULT-*-1))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 1 (:REWRITE ZERO-IS-ONLY-ZERO-DIVISOR))
 )
(INT-C-MOD::DIVIDES-P$-WITNESS)
(INT-C-MOD::DIVIDES-P)
(INT-C-MOD::DIVIDES-P-SUFF
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (4 2 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (2 2 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-*))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 )
(INT-C-MOD::UNIT-P)
(INT-C-MOD::ABS-UNIT-P=1
 (33 23 (:REWRITE DEFAULT-*-2))
 (24 23 (:REWRITE DEFAULT-*-1))
 (24 9 (:REWRITE DEFAULT-+-2))
 (22 21 (:REWRITE DEFAULT-<-1))
 (22 12 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (21 21 (:REWRITE DEFAULT-<-2))
 (16 2 (:REWRITE FLOOR-=-X/Y . 2))
 (12 4 (:REWRITE FLOOR-TYPE-4 . 3))
 (12 4 (:REWRITE FLOOR-TYPE-4 . 2))
 (12 4 (:REWRITE FLOOR-TYPE-3 . 3))
 (12 4 (:REWRITE FLOOR-TYPE-3 . 2))
 (10 10 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (10 3 (:LINEAR X*Y>1-POSITIVE))
 (9 9 (:REWRITE DEFAULT-+-1))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (7 7 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (6 6 (:REWRITE DEFAULT-UNARY-/))
 (6 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE INT-C-MOD::DIVIDES-P-SUFF))
 )
(INT-C-MOD::ABS=1-IMPLIES-UNIT-P)
(INT-C-MOD::UNIT-P=_+1_OR_-1
 (12 6 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE INT-C-MOD::DIVIDES-P-SUFF))
 (6 6 (:REWRITE DEFAULT-*-1))
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:LINEAR X*Y>1-POSITIVE))
 )
(INT-C-MOD::ABS-<-ABS-*
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 (3 1 (:LINEAR X*Y>1-POSITIVE))
 )
(INT-C-MOD::GREATEST-FACTOR
 (10 10 (:TYPE-PRESCRIPTION INT-C-MOD::NATP-ABS))
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE INT-C-MOD::DIVIDES-P-SUFF))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(INT-C-MOD::NATP-GREATEST-FACTOR
 (14 7 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE DEFAULT-*-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(INT-C-MOD::DIVIDES-P-GREATEST-FACTOR
 (66 38 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (40 34 (:REWRITE DEFAULT-*-2))
 (38 34 (:REWRITE DEFAULT-*-1))
 (26 17 (:REWRITE DEFAULT-UNARY-/))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (13 9 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (10 10 (:REWRITE ZP-OPEN))
 (6 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 2 (:REWRITE NUMERATOR-MINUS))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 1 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE FOLD-CONSTS-IN-*))
 )
(INT-C-MOD::X>1-FORWARD)
(INT-C-MOD::NOT-INTEGERP-/-A
 (4 2 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 )
(INT-C-MOD::NOT-INTEGERP-/-B-LEMMA
 (6 4 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 )
(INT-C-MOD::NOT-INTEGERP-/-B)
(INT-C-MOD::GREATEST-FACTOR=1
 (32 25 (:REWRITE DEFAULT-*-1))
 (28 28 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (25 25 (:REWRITE DEFAULT-*-2))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (16 8 (:REWRITE DEFAULT-<-1))
 (14 14 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:REWRITE DEFAULT-UNARY-/))
 (11 11 (:REWRITE DEFAULT-+-2))
 (11 11 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE FOLD-CONSTS-IN-*))
 )
(INT-C-MOD::GREATEST-FACTOR->-1
 (69 19 (:REWRITE DEFAULT-<-2))
 (29 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (19 19 (:REWRITE DEFAULT-<-1))
 (10 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(INT-C-MOD::GREATEST-FACTOR->-1-A
 (64 19 (:REWRITE DEFAULT-<-2))
 (29 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24 19 (:REWRITE DEFAULT-<-1))
 (10 5 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(INT-C-MOD::GREATEST-FACTOR->=-DIVISOR
 (96 60 (:REWRITE DEFAULT-<-1))
 (75 60 (:REWRITE DEFAULT-<-2))
 (72 9 (:LINEAR X*Y>1-POSITIVE))
 (56 10 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1))
 (48 10 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1-A))
 (47 23 (:REWRITE DEFAULT-*-2))
 (24 23 (:REWRITE DEFAULT-*-1))
 (18 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 1 (:REWRITE X*Y>1-POSITIVE))
 (7 1 (:REWRITE INT-C-MOD::ABS-*))
 (3 3 (:REWRITE ZP-OPEN))
 (3 2 (:TYPE-PRESCRIPTION INT-C-MOD::NATP-ABS))
 )
(INT-C-MOD::GREATEST-FACTOR-<=-Y
 (105 60 (:REWRITE DEFAULT-<-2))
 (72 9 (:LINEAR X*Y>1-POSITIVE))
 (67 60 (:REWRITE DEFAULT-<-1))
 (59 29 (:REWRITE DEFAULT-*-2))
 (56 10 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1))
 (48 10 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1-A))
 (30 29 (:REWRITE DEFAULT-*-1))
 (18 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 1 (:REWRITE X*Y>1-POSITIVE))
 (7 6 (:TYPE-PRESCRIPTION INT-C-MOD::NATP-ABS))
 (7 1 (:REWRITE INT-C-MOD::ABS-*))
 (6 6 (:REWRITE ZP-OPEN))
 )
(INT-C-MOD::REDUCIBLE-P$-WITNESS)
(INT-C-MOD::REDUCIBLE-P)
(INT-C-MOD::SUBGOAL-7.4
 (513 366 (:REWRITE DEFAULT-*-2))
 (438 122 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (433 366 (:REWRITE DEFAULT-*-1))
 (134 131 (:REWRITE DEFAULT-<-2))
 (133 131 (:REWRITE DEFAULT-<-1))
 (129 102 (:REWRITE DEFAULT-+-2))
 (107 53 (:REWRITE DEFAULT-UNARY-/))
 (102 102 (:REWRITE DEFAULT-+-1))
 (89 62 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (79 67 (:REWRITE DEFAULT-UNARY-MINUS))
 (54 54 (:TYPE-PRESCRIPTION INT-C-MOD::NATP-ABS))
 (52 52 (:REWRITE FOLD-CONSTS-IN-*))
 (52 13 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1))
 (46 46 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (40 40 (:REWRITE X*Y>1-POSITIVE))
 (28 28 (:REWRITE INT-C-MOD::DIVIDES-P-SUFF))
 (20 10 (:REWRITE INT-C-MOD::GREATEST-FACTOR=1))
 (13 13 (:LINEAR INT-C-MOD::GREATEST-FACTOR->=-DIVISOR))
 (13 13 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1-A))
 (13 13 (:LINEAR INT-C-MOD::GREATEST-FACTOR-<=-Y))
 (8 5 (:LINEAR X*Y>1-POSITIVE))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 1 (:REWRITE NUMERATOR-MINUS))
 )
(INT-C-MOD::SUBGOAL-7.3-LEMMA
 (40 39 (:REWRITE DEFAULT-<-1))
 (39 39 (:REWRITE DEFAULT-<-2))
 (15 5 (:REWRITE X*Y>1-POSITIVE-LEMMA))
 (15 5 (:REWRITE *-PRESERVES->=-FOR-NONNEGATIVES))
 (15 5 (:REWRITE *-PRESERVES->-FOR-NONNEGATIVES-1))
 (10 10 (:REWRITE DEFAULT-*-2))
 (10 10 (:REWRITE DEFAULT-*-1))
 (7 3 (:LINEAR X*Y>1-POSITIVE))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(INT-C-MOD::SUBGOAL-7.3-LEMMA-A)
(INT-C-MOD::SUBGOAL-7.3
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (3 3 (:LINEAR X*Y>1-POSITIVE))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(INT-C-MOD::SUBGOAL-7.1
 (114 76 (:REWRITE DEFAULT-*-2))
 (104 12 (:LINEAR X*Y>1-POSITIVE))
 (97 22 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (95 76 (:REWRITE DEFAULT-*-1))
 (41 33 (:REWRITE DEFAULT-<-2))
 (33 33 (:REWRITE DEFAULT-<-1))
 (29 22 (:REWRITE DEFAULT-+-2))
 (29 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1))
 (25 11 (:REWRITE DEFAULT-UNARY-/))
 (22 22 (:REWRITE DEFAULT-+-1))
 (21 7 (:REWRITE FOLD-CONSTS-IN-+))
 (18 11 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (16 16 (:REWRITE X*Y>1-POSITIVE))
 (14 14 (:REWRITE EQUAL-CONSTANT-+))
 (13 13 (:REWRITE FOLD-CONSTS-IN-*))
 (8 8 (:REWRITE INT-C-MOD::DIVIDES-P-SUFF))
 (8 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR->=-DIVISOR))
 (8 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1-A))
 (8 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR-<=-Y))
 (8 4 (:REWRITE INT-C-MOD::GREATEST-FACTOR=1))
 )
(INT-C-MOD::SUBGOAL-5.3-LEMMA
 (41 40 (:REWRITE DEFAULT-<-1))
 (40 40 (:REWRITE DEFAULT-<-2))
 (15 5 (:REWRITE X*Y>1-POSITIVE-LEMMA))
 (15 5 (:REWRITE *-PRESERVES->=-FOR-NONNEGATIVES))
 (15 5 (:REWRITE *-PRESERVES->-FOR-NONNEGATIVES-1))
 (10 10 (:REWRITE DEFAULT-*-2))
 (10 10 (:REWRITE DEFAULT-*-1))
 (9 3 (:LINEAR X*Y>1-POSITIVE))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(INT-C-MOD::SUBGOAL-5.3-LEMMA-A)
(INT-C-MOD::SUBGOAL-5.3
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 3 (:LINEAR X*Y>1-POSITIVE))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(INT-C-MOD::SUBGOAL-5.2
 (561 393 (:REWRITE DEFAULT-*-2))
 (481 393 (:REWRITE DEFAULT-*-1))
 (466 136 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (145 135 (:REWRITE DEFAULT-<-1))
 (139 135 (:REWRITE DEFAULT-<-2))
 (129 102 (:REWRITE DEFAULT-+-2))
 (126 120 (:REWRITE DEFAULT-UNARY-MINUS))
 (108 108 (:TYPE-PRESCRIPTION INT-C-MOD::NATP-ABS))
 (107 53 (:REWRITE DEFAULT-UNARY-/))
 (102 102 (:REWRITE DEFAULT-+-1))
 (89 62 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (52 52 (:REWRITE FOLD-CONSTS-IN-*))
 (39 13 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1-A))
 (30 10 (:REWRITE INT-C-MOD::GREATEST-FACTOR=1))
 (28 28 (:REWRITE INT-C-MOD::DIVIDES-P-SUFF))
 (24 8 (:REWRITE NUMERATOR-MINUS))
 (16 5 (:LINEAR X*Y>1-POSITIVE))
 (13 13 (:LINEAR INT-C-MOD::GREATEST-FACTOR->=-DIVISOR))
 (13 13 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1))
 (13 13 (:LINEAR INT-C-MOD::GREATEST-FACTOR-<=-Y))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(INT-C-MOD::SUBGOAL-5.1
 (170 170 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (132 12 (:LINEAR X*Y>1-POSITIVE))
 (129 83 (:REWRITE DEFAULT-*-2))
 (111 83 (:REWRITE DEFAULT-*-1))
 (99 22 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (49 37 (:REWRITE DEFAULT-<-2))
 (37 37 (:REWRITE DEFAULT-<-1))
 (29 22 (:REWRITE DEFAULT-+-2))
 (25 11 (:REWRITE DEFAULT-UNARY-/))
 (22 22 (:REWRITE DEFAULT-+-1))
 (22 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1-A))
 (21 7 (:REWRITE FOLD-CONSTS-IN-+))
 (18 11 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (14 14 (:REWRITE EQUAL-CONSTANT-+))
 (13 13 (:REWRITE FOLD-CONSTS-IN-*))
 (12 4 (:REWRITE INT-C-MOD::GREATEST-FACTOR=1))
 (11 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:REWRITE INT-C-MOD::DIVIDES-P-SUFF))
 (8 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR->=-DIVISOR))
 (8 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1))
 (8 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR-<=-Y))
 )
(INT-C-MOD::SUBGOAL-1.4
 (753 144 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (571 414 (:REWRITE DEFAULT-*-2))
 (467 414 (:REWRITE DEFAULT-*-1))
 (179 136 (:REWRITE DEFAULT-+-2))
 (136 136 (:REWRITE DEFAULT-+-1))
 (134 64 (:REWRITE DEFAULT-UNARY-/))
 (127 116 (:REWRITE DEFAULT-<-1))
 (119 116 (:REWRITE DEFAULT-<-2))
 (87 87 (:REWRITE FOLD-CONSTS-IN-*))
 (83 48 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (44 44 (:REWRITE INT-C-MOD::DIVIDES-P-SUFF))
 (43 14 (:LINEAR X*Y>1-POSITIVE))
 (22 11 (:REWRITE INT-C-MOD::GREATEST-FACTOR=1))
 (14 14 (:LINEAR INT-C-MOD::GREATEST-FACTOR->=-DIVISOR))
 (14 14 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1-A))
 (14 14 (:LINEAR INT-C-MOD::GREATEST-FACTOR-<=-Y))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:REWRITE /-CANCELLATION-ON-LEFT))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(INT-C-MOD::SUBGOAL-1.3-LEMMA
 (29 28 (:REWRITE DEFAULT-<-2))
 (28 28 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE DEFAULT-*-2))
 (10 10 (:REWRITE DEFAULT-*-1))
 (9 5 (:REWRITE X*Y>1-POSITIVE-LEMMA))
 (9 5 (:REWRITE *-PRESERVES->-FOR-NONNEGATIVES-1))
 (9 3 (:LINEAR X*Y>1-POSITIVE))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(INT-C-MOD::SUBGOAL-1.3-LEMMA-A)
(INT-C-MOD::SUBGOAL-1.3)
(INT-C-MOD::SUBGOAL-1.1
 (513 12 (:DEFINITION INT-C-MOD::GREATEST-FACTOR))
 (192 14 (:LINEAR X*Y>1-POSITIVE))
 (151 28 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (118 75 (:REWRITE DEFAULT-*-2))
 (90 75 (:REWRITE DEFAULT-*-1))
 (43 31 (:REWRITE DEFAULT-+-2))
 (36 12 (:REWRITE FOLD-CONSTS-IN-+))
 (34 14 (:REWRITE DEFAULT-UNARY-/))
 (31 31 (:REWRITE DEFAULT-+-1))
 (26 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 (24 14 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (22 22 (:REWRITE EQUAL-CONSTANT-+))
 (16 16 (:REWRITE FOLD-CONSTS-IN-*))
 (13 13 (:REWRITE INT-C-MOD::DIVIDES-P-SUFF))
 (12 4 (:REWRITE X*Y>1-POSITIVE))
 (8 4 (:REWRITE INT-C-MOD::GREATEST-FACTOR=1))
 (6 6 (:LINEAR INT-C-MOD::GREATEST-FACTOR->=-DIVISOR))
 (6 6 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1-A))
 (6 6 (:LINEAR INT-C-MOD::GREATEST-FACTOR-<=-Y))
 )
(INT-C-MOD::REDUCIBLE-P-SUFF
 (673 13 (:DEFINITION INT-C-MOD::GREATEST-FACTOR))
 (209 13 (:DEFINITION INT-C-MOD::DIVIDES-P))
 (167 127 (:REWRITE DEFAULT-*-2))
 (156 127 (:REWRITE DEFAULT-*-1))
 (121 17 (:LINEAR X*Y>1-POSITIVE))
 (114 101 (:REWRITE DEFAULT-<-2))
 (102 16 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (101 101 (:REWRITE DEFAULT-<-1))
 (71 10 (:REWRITE ZP-OPEN))
 (53 53 (:REWRITE DEFAULT-UNARY-MINUS))
 (49 37 (:REWRITE DEFAULT-+-2))
 (37 37 (:REWRITE DEFAULT-+-1))
 (36 12 (:REWRITE FOLD-CONSTS-IN-+))
 (32 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1))
 (21 7 (:REWRITE <-0-+-NEGATIVE-2))
 (20 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR->-1-A))
 (16 16 (:REWRITE EQUAL-CONSTANT-+))
 (16 8 (:REWRITE DEFAULT-UNARY-/))
 (13 13 (:REWRITE INT-C-MOD::DIVIDES-P-SUFF))
 (12 8 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (8 8 (:REWRITE FOLD-CONSTS-IN-*))
 (8 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR->=-DIVISOR))
 (8 8 (:LINEAR INT-C-MOD::GREATEST-FACTOR-<=-Y))
 (8 2 (:REWRITE <-0-+-NEGATIVE-1))
 (3 3 (:REWRITE X*Y>1-POSITIVE))
 )
(INT-C-MOD::IRREDUCIBLE-P)
(INT-C-MOD::IRREDUCIBLE-P-IMPLIES-PRIME-PROPERTY
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE INT-C-MOD::REDUCIBLE-P-SUFF))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(INT-C-MOD::IRREDUCIBLE-FACTORS
 (38 8 (:REWRITE DEFAULT-<-2))
 (38 8 (:REWRITE DEFAULT-<-1))
 (34 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 14 (:REWRITE INT-C-MOD::REDUCIBLE-P-SUFF))
 (12 9 (:REWRITE DEFAULT-*-2))
 (12 9 (:REWRITE DEFAULT-*-1))
 (6 2 (:LINEAR X*Y>1-POSITIVE))
 (6 2 (:LINEAR INT-C-MOD::ABS-<-ABS-*))
 (3 1 (:REWRITE INT-C-MOD::ABS-<-ABS-*))
 (2 2 (:REWRITE INT-C-MOD::ABS-*))
 (2 2 (:LINEAR INT-C-MOD::ABS-*))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(INT-C-MOD::INTEGERP-LISTP)
(INT-C-MOD::IRREDUCIBLE-LISTP)
(INT-C-MOD::*-LST)
(INT-C-MOD::IRREDUCIBLE-FACTORIZATION-EXISTENCE
 (55 11 (:DEFINITION BINARY-APPEND))
 (31 31 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE INT-C-MOD::REDUCIBLE-P-SUFF))
 (10 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 )
(INT-C-MOD::UNIT-ASSOCIATES-P$-WITNESS)
(INT-C-MOD::UNIT-ASSOCIATES-P)
(INT-C-MOD::UNIT-ASSOCIATES-P-SUFF
 (28 12 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (20 17 (:REWRITE DEFAULT-*-1))
 (17 17 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (12 6 (:REWRITE DEFAULT-UNARY-/))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 )
(INT-C-MOD::IRREDUCIBLE-P-UNIT-ASSOCIATES
 (6 4 (:REWRITE DEFAULT-*-2))
 (6 4 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE INT-C-MOD::UNIT-ASSOCIATES-P-SUFF))
 )
(INT-C-MOD::ACL2-NUMBER-LISTP)
(INT-C-MOD::MEMBER-UNIT-ASSOCIATE
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(INT-C-MOD::DELETE-ONE-UNIT-ASSOCIATE
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(INT-C-MOD::BAG-EQUAL-UNIT-ASSOCIATES
 (198 198 (:REWRITE DEFAULT-CAR))
 (127 127 (:REWRITE DEFAULT-CDR))
 (113 85 (:REWRITE DEFAULT-*-2))
 (113 85 (:REWRITE DEFAULT-*-1))
 (83 83 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (56 56 (:REWRITE INT-C-MOD::UNIT-ASSOCIATES-P-SUFF))
 (30 10 (:LINEAR X*Y>1-POSITIVE))
 (14 14 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 )
(INT-C-MOD::BAG-EQUAL-UNIT-ASSOCIATES->EQUAL-LEN
 (58 38 (:REWRITE DEFAULT-*-2))
 (56 38 (:REWRITE DEFAULT-*-1))
 (50 50 (:REWRITE DEFAULT-CAR))
 (35 35 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE INT-C-MOD::UNIT-ASSOCIATES-P-SUFF))
 )
(INT-C-MOD::BAG-EQUAL-UNIT-ASSOCIATES->IFF-MEMBER-UNIT-ASSOCIATE)
(INT-C-MOD::MULTIPLICITY-UNIT-ASSOCIATE
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(INT-C-MOD::BAG-EQUAL-UNIT-ASSOCIATES->EQUAL-MULTIPLICITY-UNIT-ASSOCIATE
 (20 13 (:REWRITE DEFAULT-*-2))
 (19 13 (:REWRITE DEFAULT-*-1))
 (14 14 (:REWRITE DEFAULT-CDR))
 (14 7 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE INT-C-MOD::UNIT-ASSOCIATES-P-SUFF))
 )
(INT-C-MOD::IRREDUCIBLE-FACTORIZATION-UNIQUENESS-GENERAL)
(INT-C-MOD::IRREDUCIBLE-FACTORIZATION-UNIQUENESS)
