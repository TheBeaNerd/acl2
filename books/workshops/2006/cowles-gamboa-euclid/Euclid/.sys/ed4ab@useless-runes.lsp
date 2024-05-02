(INT-MOD::CLOSURE-LAWS)
(INT-MOD::EQUIVALENCE-LAW)
(INT-MOD::CONGRUENCE-LAWS)
(INT-MOD::CLOSURE-OF-IDENTITY)
(INT-MOD::EQUIVALENCE-CLASS-LAWS)
(INT-MOD::COMMUTATIVITY-LAWS
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 )
(INT-MOD::ASSOCIATIVITY-LAWS)
(INT-MOD::LEFT-DISTRIBUTIVITY-LAW
 (6 2 (:LINEAR X*Y>1-POSITIVE))
 (5 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(INT-MOD::LEFT-UNICITY-LAWS)
(INT-MOD::RIGHT-INVERSE-LAW
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 )
(INT-MOD::ZERO-DIVISOR-LAW
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(INT-MOD::NATP-ABS
 (14 14 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:TYPE-PRESCRIPTION INT-MOD::NATP-ABS))
 )
(INT-MOD::CONGRUENCE-FOR-ABS)
(INT-MOD::CLOSURE-OF-FLOOR-&-MOD
 (1 1 (:TYPE-PRESCRIPTION MOD-TYPE . 4))
 (1 1 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (1 1 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (1 1 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (1 1 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (1 1 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (1 1 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (1 1 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 )
(INT-MOD::CONGRUENCE-FOR-FLOOR-&-MOD
 (16 16 (:TYPE-PRESCRIPTION MOD-TYPE . 4))
 (16 16 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (16 16 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (16 16 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (16 16 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (16 16 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (16 16 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (16 16 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 )
(INT-MOD::DIVISION-PROPERTY
 (52 40 (:REWRITE DEFAULT-<-1))
 (40 40 (:REWRITE DEFAULT-<-2))
 (25 9 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (25 9 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (25 9 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (25 9 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (19 19 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (19 19 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (19 19 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (19 19 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (14 9 (:REWRITE MOD-=-0 . 2))
 (13 10 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (11 6 (:REWRITE DEFAULT-*-2))
 (8 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 1 (:REWRITE FLOOR-=-X/Y . 3))
 (7 1 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-*-1))
 (6 1 (:REWRITE FLOOR-=-X/Y . 2))
 (6 1 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-UNARY-/))
 (3 3 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (3 1 (:REWRITE FLOOR-TYPE-4 . 3))
 (3 1 (:REWRITE FLOOR-TYPE-4 . 2))
 (3 1 (:REWRITE FLOOR-TYPE-3 . 3))
 (3 1 (:REWRITE FLOOR-TYPE-3 . 2))
 )
(INT-MOD::ABS-*
 (84 76 (:REWRITE DEFAULT-<-2))
 (80 76 (:REWRITE DEFAULT-<-1))
 (43 8 (:LINEAR X*Y>1-POSITIVE))
 (37 36 (:REWRITE DEFAULT-*-2))
 (37 36 (:REWRITE DEFAULT-*-1))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 1 (:REWRITE ZERO-IS-ONLY-ZERO-DIVISOR))
 )
(INT-MOD::DIVIDES-P$-WITNESS)
(INT-MOD::DIVIDES-P)
(INT-MOD::DIVIDES-P-SUFF
 (4 4 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE DEFAULT-*-1))
 (4 2 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (2 2 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-*))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 )
(INT-MOD::UNIT-P)
(INT-MOD::ABS-UNIT-P=1
 (42 42 (:TYPE-PRESCRIPTION MOD-TYPE . 4))
 (42 42 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (42 42 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (42 42 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (35 35 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (35 35 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (35 35 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (35 35 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (32 22 (:REWRITE DEFAULT-*-2))
 (24 23 (:REWRITE DEFAULT-<-1))
 (23 23 (:REWRITE DEFAULT-<-2))
 (23 22 (:REWRITE DEFAULT-*-1))
 (14 10 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (13 7 (:REWRITE DEFAULT-+-2))
 (12 7 (:REWRITE DEFAULT-+-1))
 (10 3 (:LINEAR X*Y>1-POSITIVE))
 (9 4 (:REWRITE MOD-=-0 . 2))
 (8 4 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (8 4 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (8 4 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (8 4 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (8 1 (:REWRITE FLOOR-=-X/Y . 3))
 (6 2 (:LINEAR MOD-BOUNDED-BY-MODULUS))
 (6 1 (:REWRITE FLOOR-=-X/Y . 2))
 (5 5 (:REWRITE DEFAULT-UNARY-/))
 (4 4 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (3 1 (:REWRITE FLOOR-TYPE-4 . 3))
 (3 1 (:REWRITE FLOOR-TYPE-4 . 2))
 (3 1 (:REWRITE FLOOR-TYPE-3 . 3))
 (3 1 (:REWRITE FLOOR-TYPE-3 . 2))
 (3 1 (:LINEAR MOD-TYPE . 4))
 (3 1 (:LINEAR MOD-TYPE . 3))
 (3 1 (:LINEAR MOD-TYPE . 2))
 (3 1 (:LINEAR MOD-TYPE . 1))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (1 1 (:REWRITE INT-MOD::DIVIDES-P-SUFF))
 )
(INT-MOD::ABS=1-IMPLIES-UNIT-P)
(INT-MOD::UNIT-P=_+1_OR_-1
 (12 6 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE INT-MOD::DIVIDES-P-SUFF))
 (6 6 (:REWRITE DEFAULT-*-1))
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:LINEAR X*Y>1-POSITIVE))
 )
(INT-MOD::ABS-<-ABS-*
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 (3 1 (:LINEAR X*Y>1-POSITIVE))
 )
(INT-MOD::GREATEST-FACTOR
 (10 10 (:TYPE-PRESCRIPTION INT-MOD::NATP-ABS))
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE INT-MOD::DIVIDES-P-SUFF))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(INT-MOD::NATP-GREATEST-FACTOR
 (14 7 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE DEFAULT-*-1))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(INT-MOD::DIVIDES-P-GREATEST-FACTOR
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
(INT-MOD::X>1-FORWARD)
(INT-MOD::NOT-INTEGERP-/-A
 (4 2 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 )
(INT-MOD::NOT-INTEGERP-/-B-LEMMA
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
(INT-MOD::NOT-INTEGERP-/-B)
(INT-MOD::GREATEST-FACTOR=1
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
(INT-MOD::GREATEST-FACTOR->-1
 (69 19 (:REWRITE DEFAULT-<-2))
 (29 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (19 19 (:REWRITE DEFAULT-<-1))
 (10 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(INT-MOD::GREATEST-FACTOR->-1-A
 (64 19 (:REWRITE DEFAULT-<-2))
 (29 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (24 19 (:REWRITE DEFAULT-<-1))
 (10 5 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:LINEAR INT-MOD::GREATEST-FACTOR->-1))
 (5 5 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(INT-MOD::GREATEST-FACTOR->=-DIVISOR
 (93 58 (:REWRITE DEFAULT-<-1))
 (72 58 (:REWRITE DEFAULT-<-2))
 (72 9 (:LINEAR X*Y>1-POSITIVE))
 (52 9 (:LINEAR INT-MOD::GREATEST-FACTOR->-1))
 (47 23 (:REWRITE DEFAULT-*-2))
 (44 9 (:LINEAR INT-MOD::GREATEST-FACTOR->-1-A))
 (24 23 (:REWRITE DEFAULT-*-1))
 (16 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 1 (:REWRITE X*Y>1-POSITIVE))
 (7 1 (:REWRITE INT-MOD::ABS-*))
 (3 2 (:TYPE-PRESCRIPTION INT-MOD::NATP-ABS))
 (2 2 (:REWRITE ZP-OPEN))
 )
(INT-MOD::GREATEST-FACTOR-<=-Y
 (102 58 (:REWRITE DEFAULT-<-2))
 (72 9 (:LINEAR X*Y>1-POSITIVE))
 (64 58 (:REWRITE DEFAULT-<-1))
 (55 27 (:REWRITE DEFAULT-*-2))
 (52 9 (:LINEAR INT-MOD::GREATEST-FACTOR->-1))
 (44 9 (:LINEAR INT-MOD::GREATEST-FACTOR->-1-A))
 (28 27 (:REWRITE DEFAULT-*-1))
 (16 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (8 1 (:REWRITE X*Y>1-POSITIVE))
 (7 1 (:REWRITE INT-MOD::ABS-*))
 (3 3 (:REWRITE ZP-OPEN))
 (3 2 (:TYPE-PRESCRIPTION INT-MOD::NATP-ABS))
 )
(INT-MOD::REDUCIBLE-P$-WITNESS)
(INT-MOD::REDUCIBLE-P)
(INT-MOD::SUBGOAL-7.4
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
 (54 54 (:TYPE-PRESCRIPTION INT-MOD::NATP-ABS))
 (52 52 (:REWRITE FOLD-CONSTS-IN-*))
 (52 13 (:LINEAR INT-MOD::GREATEST-FACTOR->-1))
 (46 46 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (40 40 (:REWRITE X*Y>1-POSITIVE))
 (28 28 (:REWRITE INT-MOD::DIVIDES-P-SUFF))
 (20 10 (:REWRITE INT-MOD::GREATEST-FACTOR=1))
 (13 13 (:LINEAR INT-MOD::GREATEST-FACTOR->=-DIVISOR))
 (13 13 (:LINEAR INT-MOD::GREATEST-FACTOR->-1-A))
 (13 13 (:LINEAR INT-MOD::GREATEST-FACTOR-<=-Y))
 (8 5 (:LINEAR X*Y>1-POSITIVE))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 1 (:REWRITE NUMERATOR-MINUS))
 )
(INT-MOD::SUBGOAL-7.3-LEMMA
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
(INT-MOD::SUBGOAL-7.3-LEMMA-A)
(INT-MOD::SUBGOAL-7.3
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (3 3 (:LINEAR X*Y>1-POSITIVE))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(INT-MOD::SUBGOAL-7.1
 (114 76 (:REWRITE DEFAULT-*-2))
 (104 12 (:LINEAR X*Y>1-POSITIVE))
 (97 22 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (95 76 (:REWRITE DEFAULT-*-1))
 (41 33 (:REWRITE DEFAULT-<-2))
 (33 33 (:REWRITE DEFAULT-<-1))
 (29 22 (:REWRITE DEFAULT-+-2))
 (29 8 (:LINEAR INT-MOD::GREATEST-FACTOR->-1))
 (25 11 (:REWRITE DEFAULT-UNARY-/))
 (22 22 (:REWRITE DEFAULT-+-1))
 (21 7 (:REWRITE FOLD-CONSTS-IN-+))
 (18 11 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (16 16 (:REWRITE X*Y>1-POSITIVE))
 (14 14 (:REWRITE EQUAL-CONSTANT-+))
 (13 13 (:REWRITE FOLD-CONSTS-IN-*))
 (8 8 (:REWRITE INT-MOD::DIVIDES-P-SUFF))
 (8 8 (:LINEAR INT-MOD::GREATEST-FACTOR->=-DIVISOR))
 (8 8 (:LINEAR INT-MOD::GREATEST-FACTOR->-1-A))
 (8 8 (:LINEAR INT-MOD::GREATEST-FACTOR-<=-Y))
 (8 4 (:REWRITE INT-MOD::GREATEST-FACTOR=1))
 )
(INT-MOD::SUBGOAL-5.3-LEMMA
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
(INT-MOD::SUBGOAL-5.3-LEMMA-A)
(INT-MOD::SUBGOAL-5.3
 (9 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 3 (:LINEAR X*Y>1-POSITIVE))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(INT-MOD::SUBGOAL-5.2
 (561 393 (:REWRITE DEFAULT-*-2))
 (481 393 (:REWRITE DEFAULT-*-1))
 (466 136 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (145 135 (:REWRITE DEFAULT-<-1))
 (139 135 (:REWRITE DEFAULT-<-2))
 (129 102 (:REWRITE DEFAULT-+-2))
 (126 120 (:REWRITE DEFAULT-UNARY-MINUS))
 (108 108 (:TYPE-PRESCRIPTION INT-MOD::NATP-ABS))
 (107 53 (:REWRITE DEFAULT-UNARY-/))
 (102 102 (:REWRITE DEFAULT-+-1))
 (89 62 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (52 52 (:REWRITE FOLD-CONSTS-IN-*))
 (39 13 (:LINEAR INT-MOD::GREATEST-FACTOR->-1-A))
 (30 10 (:REWRITE INT-MOD::GREATEST-FACTOR=1))
 (28 28 (:REWRITE INT-MOD::DIVIDES-P-SUFF))
 (24 8 (:REWRITE NUMERATOR-MINUS))
 (16 5 (:LINEAR X*Y>1-POSITIVE))
 (13 13 (:LINEAR INT-MOD::GREATEST-FACTOR->=-DIVISOR))
 (13 13 (:LINEAR INT-MOD::GREATEST-FACTOR->-1))
 (13 13 (:LINEAR INT-MOD::GREATEST-FACTOR-<=-Y))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(INT-MOD::SUBGOAL-5.1
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
 (22 8 (:LINEAR INT-MOD::GREATEST-FACTOR->-1-A))
 (21 7 (:REWRITE FOLD-CONSTS-IN-+))
 (18 11 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (14 14 (:REWRITE EQUAL-CONSTANT-+))
 (13 13 (:REWRITE FOLD-CONSTS-IN-*))
 (12 4 (:REWRITE INT-MOD::GREATEST-FACTOR=1))
 (11 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:REWRITE INT-MOD::DIVIDES-P-SUFF))
 (8 8 (:LINEAR INT-MOD::GREATEST-FACTOR->=-DIVISOR))
 (8 8 (:LINEAR INT-MOD::GREATEST-FACTOR->-1))
 (8 8 (:LINEAR INT-MOD::GREATEST-FACTOR-<=-Y))
 )
(INT-MOD::SUBGOAL-1.4
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
 (44 44 (:REWRITE INT-MOD::DIVIDES-P-SUFF))
 (43 14 (:LINEAR X*Y>1-POSITIVE))
 (22 11 (:REWRITE INT-MOD::GREATEST-FACTOR=1))
 (14 14 (:LINEAR INT-MOD::GREATEST-FACTOR->=-DIVISOR))
 (14 14 (:LINEAR INT-MOD::GREATEST-FACTOR->-1-A))
 (14 14 (:LINEAR INT-MOD::GREATEST-FACTOR-<=-Y))
 (9 9 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:REWRITE /-CANCELLATION-ON-LEFT))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(INT-MOD::SUBGOAL-1.3-LEMMA
 (29 28 (:REWRITE DEFAULT-<-2))
 (28 28 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE DEFAULT-*-2))
 (10 10 (:REWRITE DEFAULT-*-1))
 (9 5 (:REWRITE X*Y>1-POSITIVE-LEMMA))
 (9 5 (:REWRITE *-PRESERVES->-FOR-NONNEGATIVES-1))
 (9 3 (:LINEAR X*Y>1-POSITIVE))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(INT-MOD::SUBGOAL-1.3-LEMMA-A)
(INT-MOD::SUBGOAL-1.3)
(INT-MOD::SUBGOAL-1.1
 (513 12 (:DEFINITION INT-MOD::GREATEST-FACTOR))
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
 (13 13 (:REWRITE INT-MOD::DIVIDES-P-SUFF))
 (12 4 (:REWRITE X*Y>1-POSITIVE))
 (8 4 (:REWRITE INT-MOD::GREATEST-FACTOR=1))
 (6 6 (:LINEAR INT-MOD::GREATEST-FACTOR->=-DIVISOR))
 (6 6 (:LINEAR INT-MOD::GREATEST-FACTOR->-1-A))
 (6 6 (:LINEAR INT-MOD::GREATEST-FACTOR-<=-Y))
 )
(INT-MOD::REDUCIBLE-P-SUFF
 (673 13 (:DEFINITION INT-MOD::GREATEST-FACTOR))
 (209 13 (:DEFINITION INT-MOD::DIVIDES-P))
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
 (32 8 (:LINEAR INT-MOD::GREATEST-FACTOR->-1))
 (21 7 (:REWRITE <-0-+-NEGATIVE-2))
 (20 8 (:LINEAR INT-MOD::GREATEST-FACTOR->-1-A))
 (16 16 (:REWRITE EQUAL-CONSTANT-+))
 (16 8 (:REWRITE DEFAULT-UNARY-/))
 (13 13 (:REWRITE INT-MOD::DIVIDES-P-SUFF))
 (12 8 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (8 8 (:REWRITE FOLD-CONSTS-IN-*))
 (8 8 (:LINEAR INT-MOD::GREATEST-FACTOR->=-DIVISOR))
 (8 8 (:LINEAR INT-MOD::GREATEST-FACTOR-<=-Y))
 (8 2 (:REWRITE <-0-+-NEGATIVE-1))
 (3 3 (:REWRITE X*Y>1-POSITIVE))
 )
(INT-MOD::IRREDUCIBLE-P)
(INT-MOD::IRREDUCIBLE-P-IMPLIES-PRIME-PROPERTY
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE INT-MOD::REDUCIBLE-P-SUFF))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(INT-MOD::IRREDUCIBLE-FACTORS
 (38 8 (:REWRITE DEFAULT-<-2))
 (38 8 (:REWRITE DEFAULT-<-1))
 (34 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 14 (:REWRITE INT-MOD::REDUCIBLE-P-SUFF))
 (12 9 (:REWRITE DEFAULT-*-2))
 (12 9 (:REWRITE DEFAULT-*-1))
 (6 2 (:LINEAR X*Y>1-POSITIVE))
 (6 2 (:LINEAR INT-MOD::ABS-<-ABS-*))
 (3 1 (:REWRITE INT-MOD::ABS-<-ABS-*))
 (2 2 (:REWRITE INT-MOD::ABS-*))
 (2 2 (:LINEAR INT-MOD::ABS-*))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(INT-MOD::INTEGERP-LISTP)
(INT-MOD::IRREDUCIBLE-LISTP)
(INT-MOD::*-LST)
(INT-MOD::IRREDUCIBLE-FACTORIZATION-EXISTENCE
 (55 11 (:DEFINITION BINARY-APPEND))
 (31 31 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE INT-MOD::REDUCIBLE-P-SUFF))
 (10 5 (:REWRITE DEFAULT-*-2))
 (5 5 (:REWRITE DEFAULT-*-1))
 )
(INT-MOD::UNIT-ASSOCIATES-P$-WITNESS)
(INT-MOD::UNIT-ASSOCIATES-P)
(INT-MOD::UNIT-ASSOCIATES-P-SUFF
 (28 12 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (20 17 (:REWRITE DEFAULT-*-1))
 (17 17 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (12 6 (:REWRITE DEFAULT-UNARY-/))
 (9 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 )
(INT-MOD::IRREDUCIBLE-P-UNIT-ASSOCIATES
 (6 4 (:REWRITE DEFAULT-*-2))
 (6 4 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE INT-MOD::UNIT-ASSOCIATES-P-SUFF))
 )
(INT-MOD::ACL2-NUMBER-LISTP)
(INT-MOD::MEMBER-UNIT-ASSOCIATE
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(INT-MOD::DELETE-ONE-UNIT-ASSOCIATE
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(INT-MOD::BAG-EQUAL-UNIT-ASSOCIATES
 (198 198 (:REWRITE DEFAULT-CAR))
 (127 127 (:REWRITE DEFAULT-CDR))
 (113 85 (:REWRITE DEFAULT-*-2))
 (113 85 (:REWRITE DEFAULT-*-1))
 (83 83 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (56 56 (:REWRITE INT-MOD::UNIT-ASSOCIATES-P-SUFF))
 (30 10 (:LINEAR X*Y>1-POSITIVE))
 (14 14 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 )
(INT-MOD::BAG-EQUAL-UNIT-ASSOCIATES->EQUAL-LEN
 (58 38 (:REWRITE DEFAULT-*-2))
 (56 38 (:REWRITE DEFAULT-*-1))
 (50 50 (:REWRITE DEFAULT-CAR))
 (35 35 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE INT-MOD::UNIT-ASSOCIATES-P-SUFF))
 )
(INT-MOD::BAG-EQUAL-UNIT-ASSOCIATES->IFF-MEMBER-UNIT-ASSOCIATE)
(INT-MOD::MULTIPLICITY-UNIT-ASSOCIATE
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(INT-MOD::BAG-EQUAL-UNIT-ASSOCIATES->EQUAL-MULTIPLICITY-UNIT-ASSOCIATE
 (20 13 (:REWRITE DEFAULT-*-2))
 (19 13 (:REWRITE DEFAULT-*-1))
 (14 14 (:REWRITE DEFAULT-CDR))
 (14 7 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE INT-MOD::UNIT-ASSOCIATES-P-SUFF))
 )
(INT-MOD::IRREDUCIBLE-FACTORIZATION-UNIQUENESS-GENERAL)
(INT-MOD::IRREDUCIBLE-FACTORIZATION-UNIQUENESS)
