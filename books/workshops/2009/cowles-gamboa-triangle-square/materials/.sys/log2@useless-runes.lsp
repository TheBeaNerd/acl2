(FLOG2
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:REWRITE SIMPLIFY-SUMS-<))
 (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE |(< (- x) 0)|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(integerp (* c x))|))
 (1 1 (:REWRITE |(< 0 (- x))|))
 (1 1 (:REWRITE |(* c (* d x))|))
 (1 1 (:META META-INTEGERP-CORRECT))
 )
(FLOG2-IS-CORRECT
 (312 16 (:LINEAR EXPT-X->=-X))
 (312 16 (:LINEAR EXPT-X->-X))
 (196 76 (:REWRITE DEFAULT-<-2))
 (166 18 (:REWRITE |(* (+ x y) z)|))
 (157 92 (:REWRITE DEFAULT-+-2))
 (157 12 (:REWRITE ZP-OPEN))
 (140 13 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (125 125 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (125 125 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (100 52 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (92 92 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (92 92 (:REWRITE DEFAULT-+-1))
 (83 83 (:REWRITE |(< (- x) (- y))|))
 (80 40 (:REWRITE DEFAULT-EXPT-2))
 (76 76 (:REWRITE DEFAULT-<-1))
 (71 40 (:REWRITE |(expt 2^i n)|))
 (55 9 (:REWRITE EVEN-AND-ODD-ALTERNATE))
 (47 47 (:REWRITE DEFAULT-*-2))
 (47 47 (:REWRITE DEFAULT-*-1))
 (47 47 (:META META-INTEGERP-CORRECT))
 (40 40 (:REWRITE DEFAULT-EXPT-1))
 (40 40 (:REWRITE |(expt x (- n))|))
 (40 40 (:REWRITE |(expt 1/c n)|))
 (40 40 (:REWRITE |(expt (- x) n)|))
 (34 17 (:LINEAR EXPT-<-1-TWO))
 (32 32 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (32 32 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (32 32 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (32 32 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (31 31 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (31 31 (:REWRITE |(< 0 (- x))|))
 (30 30 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (28 26 (:REWRITE REDUCE-INTEGERP-+))
 (26 26 (:REWRITE INTEGERP-MINUS-X))
 (17 17 (:LINEAR EXPT->-1-TWO))
 (17 17 (:LINEAR EXPT-<-1-ONE))
 (15 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (15 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (15 3 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (13 13 (:REWRITE |(integerp (* c x))|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE |(< (+ c x) d)|))
 )
(CLOG2
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (7 7 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (7 7 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE DEFAULT-*-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (4 4 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (3 3 (:REWRITE |(< (- x) 0)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE |(integerp (* c x))|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (1 1 (:REWRITE |(< 0 (- x))|))
 (1 1 (:REWRITE |(+ c (+ d x))|))
 )
(NATP-CLOG2
 (79 79 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (79 79 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (79 79 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (16 12 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (16 12 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (16 12 (:REWRITE DEFAULT-+-2))
 (14 10 (:REWRITE SIMPLIFY-SUMS-<))
 (14 10 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (14 10 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (14 10 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (12 12 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (12 12 (:REWRITE NORMALIZE-ADDENDS))
 (12 12 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-*-2))
 (12 12 (:REWRITE DEFAULT-*-1))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE |(< (- x) (- y))|))
 (10 10 (:META META-INTEGERP-CORRECT))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE |(integerp (* c x))|))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (4 4 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (4 4 (:REWRITE |(< 0 (- x))|))
 (4 4 (:REWRITE |(< (- x) 0)|))
 )
(POSP-1/2+1/2*N
 (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (27 27 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (3 3 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (3 3 (:REWRITE DEFAULT-*-2))
 (3 3 (:REWRITE DEFAULT-*-1))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (1 1 (:REWRITE |(integerp (* c x))|))
 )
(POSP-CLOG2
 (278 278 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (278 278 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (278 278 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (103 103 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (103 103 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (103 103 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (103 103 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (86 28 (:REWRITE DEFAULT-+-2))
 (64 12 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (64 12 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (64 12 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (54 6 (:REWRITE |(* (* x y) z)|))
 (36 36 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (36 36 (:REWRITE DEFAULT-*-2))
 (36 36 (:REWRITE DEFAULT-*-1))
 (31 17 (:REWRITE REDUCE-INTEGERP-+))
 (28 28 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (28 28 (:REWRITE NORMALIZE-ADDENDS))
 (28 28 (:REWRITE DEFAULT-+-1))
 (24 6 (:REWRITE |(* c (* d x))|))
 (17 17 (:REWRITE INTEGERP-MINUS-X))
 (17 17 (:META META-INTEGERP-CORRECT))
 (12 12 (:REWRITE |(equal (- x) (- y))|))
 (10 10 (:REWRITE |(integerp (* c x))|))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (7 7 (:REWRITE SIMPLIFY-SUMS-<))
 (7 7 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (5 1 (:REWRITE |(+ c (+ d x))|))
 (4 4 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (4 4 (:REWRITE |(equal (- x) 0)|))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 )
(CLOG2-LEMMA-A
 (238 2 (:DEFINITION CLOG2))
 (108 6 (:REWRITE |(* (+ x y) z)|))
 (93 3 (:REWRITE |(< d (+ c x))|))
 (89 20 (:REWRITE DEFAULT-+-2))
 (84 2 (:DEFINITION EVENP))
 (73 2 (:LINEAR EXPT-X->=-X))
 (73 2 (:LINEAR EXPT-X->-X))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (68 68 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (54 6 (:REWRITE |(* (* x y) z)|))
 (46 2 (:LINEAR EXPT-<-1-TWO))
 (32 4 (:REWRITE REDUCE-INTEGERP-+))
 (31 1 (:REWRITE |(< (+ c x) d)|))
 (28 7 (:REWRITE SIMPLIFY-SUMS-<))
 (28 7 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (28 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (25 7 (:REWRITE DEFAULT-<-2))
 (24 6 (:REWRITE |(* y x)|))
 (20 20 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:REWRITE NORMALIZE-ADDENDS))
 (20 20 (:REWRITE DEFAULT-+-1))
 (18 18 (:REWRITE DEFAULT-*-2))
 (18 18 (:REWRITE DEFAULT-*-1))
 (16 4 (:REWRITE DEFAULT-EXPT-2))
 (10 7 (:REWRITE DEFAULT-<-1))
 (10 4 (:REWRITE |(expt 2^i n)|))
 (10 2 (:REWRITE |(equal (+ c x) d)|))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE DEFAULT-EXPT-1))
 (4 4 (:REWRITE |(expt x (- n))|))
 (4 4 (:REWRITE |(expt 1/c n)|))
 (4 4 (:REWRITE |(expt (- x) n)|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (4 4 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (2 2 (:REWRITE |(integerp (* c x))|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (1 1 (:REWRITE |(< 0 (- x))|))
 )
(CLOG2-LEMMA-B
 (444 4 (:DEFINITION CLOG2))
 (216 12 (:REWRITE |(* (+ x y) z)|))
 (121 30 (:REWRITE DEFAULT-+-2))
 (108 12 (:REWRITE |(* (* x y) z)|))
 (93 3 (:REWRITE |(< d (+ c x))|))
 (73 2 (:LINEAR EXPT-X->=-X))
 (73 2 (:LINEAR EXPT-X->-X))
 (64 8 (:REWRITE REDUCE-INTEGERP-+))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (55 55 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (48 12 (:REWRITE |(* c (* d x))|))
 (46 2 (:LINEAR EXPT-<-1-TWO))
 (33 33 (:REWRITE DEFAULT-*-2))
 (33 33 (:REWRITE DEFAULT-*-1))
 (31 1 (:REWRITE |(< (+ c x) d)|))
 (30 30 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (30 30 (:REWRITE NORMALIZE-ADDENDS))
 (30 30 (:REWRITE DEFAULT-+-1))
 (28 7 (:REWRITE SIMPLIFY-SUMS-<))
 (28 7 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (28 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (25 25 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (25 7 (:REWRITE DEFAULT-<-2))
 (24 6 (:REWRITE DEFAULT-EXPT-2))
 (20 4 (:REWRITE |(equal (+ c x) d)|))
 (20 4 (:REWRITE |(+ c (+ d x))|))
 (12 12 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (12 6 (:REWRITE |(expt 2^i n)|))
 (10 7 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:META META-INTEGERP-CORRECT))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE DEFAULT-EXPT-1))
 (6 6 (:REWRITE |(expt x (- n))|))
 (6 6 (:REWRITE |(expt 1/c n)|))
 (6 6 (:REWRITE |(expt (- x) n)|))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (4 4 (:REWRITE |(integerp (* c x))|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (4 4 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (4 4 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (4 4 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (2 2 (:LINEAR EXPT->-1-TWO))
 (2 2 (:LINEAR EXPT-<-1-ONE))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (1 1 (:REWRITE |(< 0 (- x))|))
 )
(CLOG2-IS-CORRECT-LOWER
 (1226 26 (:REWRITE |(< d (+ c x))|))
 (995 995 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (995 995 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (995 995 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (681 9 (:LINEAR EXPT->-1-ONE))
 (679 9 (:LINEAR EXPT-X->=-X))
 (679 9 (:LINEAR EXPT-X->-X))
 (594 9 (:LINEAR EXPT-<-1-TWO))
 (473 51 (:REWRITE SIMPLIFY-SUMS-<))
 (473 51 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (336 5 (:REWRITE |(< (+ c x) d)|))
 (334 51 (:REWRITE DEFAULT-<-2))
 (277 9 (:REWRITE DEFAULT-UNARY-/))
 (244 43 (:REWRITE DEFAULT-+-2))
 (190 51 (:REWRITE DEFAULT-<-1))
 (145 15 (:REWRITE DEFAULT-EXPT-2))
 (131 42 (:REWRITE DEFAULT-*-2))
 (108 108 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (108 108 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (108 108 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (108 108 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (106 15 (:REWRITE |(expt 2^i n)|))
 (83 83 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (54 54 (:REWRITE |(< (- x) (- y))|))
 (54 6 (:REWRITE |(* (* x y) z)|))
 (49 21 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (44 16 (:REWRITE REDUCE-INTEGERP-+))
 (43 43 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (43 43 (:REWRITE NORMALIZE-ADDENDS))
 (43 43 (:REWRITE DEFAULT-+-1))
 (42 42 (:REWRITE DEFAULT-*-1))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (18 18 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (18 18 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (18 18 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (18 18 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (16 16 (:REWRITE INTEGERP-MINUS-X))
 (16 16 (:META META-INTEGERP-CORRECT))
 (15 15 (:REWRITE DEFAULT-EXPT-1))
 (15 15 (:REWRITE |(expt x (- n))|))
 (15 15 (:REWRITE |(expt 1/c n)|))
 (15 15 (:REWRITE |(expt (- x) n)|))
 (10 2 (:REWRITE |(equal (+ c x) d)|))
 (9 9 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (9 9 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 9 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 9 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (9 9 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (9 9 (:REWRITE |(integerp (* c x))|))
 (9 9 (:REWRITE |(equal (- x) (- y))|))
 (9 9 (:REWRITE |(< 0 (- x))|))
 (9 9 (:LINEAR EXPT->-1-TWO))
 (9 9 (:LINEAR EXPT-<-1-ONE))
 (3 3 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (1 1 (:REWRITE |(< (- x) 0)|))
 )
(CLOG2-IS-CORRECT-UPPER
 (1778 1778 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1778 1778 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1778 1778 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1068 16 (:LINEAR EXPT-<-1-TWO))
 (980 85 (:REWRITE SIMPLIFY-SUMS-<))
 (980 85 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (938 938 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (938 938 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (938 938 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (938 938 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (620 85 (:REWRITE DEFAULT-<-2))
 (572 117 (:REWRITE DEFAULT-+-2))
 (480 4 (:REWRITE |(< (+ c x) d)|))
 (445 85 (:REWRITE DEFAULT-<-1))
 (409 39 (:REWRITE DEFAULT-EXPT-2))
 (390 12 (:REWRITE DEFAULT-UNARY-/))
 (378 42 (:REWRITE |(* (* x y) z)|))
 (277 145 (:REWRITE DEFAULT-*-2))
 (274 39 (:REWRITE |(expt 2^i n)|))
 (172 12 (:REWRITE ZP-OPEN))
 (145 145 (:REWRITE DEFAULT-*-1))
 (142 44 (:REWRITE REDUCE-INTEGERP-+))
 (117 117 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (117 117 (:REWRITE NORMALIZE-ADDENDS))
 (117 117 (:REWRITE DEFAULT-+-1))
 (88 88 (:REWRITE |(< (- x) (- y))|))
 (46 46 (:META META-INTEGERP-CORRECT))
 (44 44 (:REWRITE INTEGERP-MINUS-X))
 (40 2 (:REWRITE EVEN-AND-ODD-ALTERNATE))
 (39 39 (:REWRITE DEFAULT-EXPT-1))
 (39 39 (:REWRITE |(expt x (- n))|))
 (39 39 (:REWRITE |(expt 1/c n)|))
 (39 39 (:REWRITE |(expt (- x) n)|))
 (35 7 (:REWRITE |(equal (+ c x) d)|))
 (35 7 (:REWRITE |(+ c (+ d x))|))
 (32 32 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (32 32 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (32 32 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (32 32 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (31 31 (:REWRITE |(integerp (* c x))|))
 (25 25 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (25 25 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (25 25 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (25 25 (:REWRITE |(equal (- x) (- y))|))
 (24 24 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (24 24 (:REWRITE |(< 0 (- x))|))
 (22 2 (:REWRITE |(< 0 (* x y))|))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (16 16 (:LINEAR EXPT->-1-TWO))
 (16 16 (:LINEAR EXPT-<-1-ONE))
 (12 12 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (9 9 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (9 9 (:REWRITE |(< (- x) 0)|))
 (7 7 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (3 3 (:REWRITE BUBBLE-DOWN-*-MATCH-3))
 )
(CLOG2-IS-CORRECT
 (108 2 (:DEFINITION CLOG2))
 (58 56 (:TYPE-PRESCRIPTION POSP-CLOG2))
 (26 9 (:REWRITE DEFAULT-+-2))
 (26 2 (:DEFINITION EVENP))
 (24 6 (:REWRITE |(* y x)|))
 (18 2 (:REWRITE |(* (+ x y) z)|))
 (9 9 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE NORMALIZE-ADDENDS))
 (9 9 (:REWRITE DEFAULT-+-1))
 (8 2 (:REWRITE DEFAULT-EXPT-2))
 (6 6 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (6 6 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-*-1))
 (5 2 (:REWRITE |(expt 2^i n)|))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (4 4 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION POSP-1/2+1/2*N))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2 (:REWRITE DEFAULT-EXPT-1))
 (2 2 (:REWRITE |(integerp (* c x))|))
 (2 2 (:REWRITE |(expt x (- n))|))
 (2 2 (:REWRITE |(expt 1/c n)|))
 (2 2 (:REWRITE |(expt (- x) n)|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (1 1 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE |(< 0 (- x))|))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 )
(NBR-CALLS-CLOG2
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (32 32 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (10 10 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (8 8 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (8 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (7 7 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (7 7 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE DEFAULT-*-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (3 3 (:REWRITE |(< (- x) 0)|))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE |(integerp (* c x))|))
 (2 2 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE |(* (- x) y)|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (1 1 (:REWRITE |(< 0 (- x))|))
 (1 1 (:REWRITE |(+ c (+ d x))|))
 (1 1 (:REWRITE |(* c (* d x))|))
 )
(NBR-CALLS-CLOG2=1+CLOG2
 (175 175 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (175 175 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (175 175 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (116 28 (:REWRITE DEFAULT-+-2))
 (51 11 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (51 11 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (51 11 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (40 4 (:REWRITE |(equal (+ c x) d)|))
 (37 37 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (37 37 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (37 37 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (37 37 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (28 28 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (28 28 (:REWRITE NORMALIZE-ADDENDS))
 (28 28 (:REWRITE DEFAULT-+-1))
 (20 20 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (20 20 (:REWRITE DEFAULT-*-2))
 (20 20 (:REWRITE DEFAULT-*-1))
 (11 11 (:REWRITE REDUCE-INTEGERP-+))
 (11 11 (:REWRITE INTEGERP-MINUS-X))
 (11 11 (:REWRITE |(equal (- x) (- y))|))
 (11 11 (:META META-INTEGERP-CORRECT))
 (7 7 (:REWRITE |(integerp (* c x))|))
 (4 4 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (4 4 (:REWRITE SIMPLIFY-SUMS-<))
 (4 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE |(< 0 (- x))|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 )
(NBR-CALLS-FLOG2
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (14 14 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (5 5 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (3 3 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (3 3 (:REWRITE SIMPLIFY-SUMS-<))
 (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (2 2 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE |(< (- x) 0)|))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(integerp (* c x))|))
 (1 1 (:REWRITE |(< 0 (- x))|))
 (1 1 (:REWRITE |(* c (* d x))|))
 (1 1 (:META META-INTEGERP-CORRECT))
 )
(NBR-CALLS-FLOG2-LOWER-BOUND
 (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (42 42 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (38 21 (:REWRITE DEFAULT-+-2))
 (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (35 35 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (21 21 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (21 21 (:REWRITE NORMALIZE-ADDENDS))
 (21 21 (:REWRITE DEFAULT-+-1))
 (19 9 (:REWRITE SIMPLIFY-SUMS-<))
 (19 9 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (19 9 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (18 12 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (14 14 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (14 14 (:REWRITE DEFAULT-*-2))
 (14 14 (:REWRITE DEFAULT-*-1))
 (14 9 (:REWRITE DEFAULT-<-2))
 (14 9 (:REWRITE DEFAULT-<-1))
 (14 7 (:REWRITE |(< d (+ c x))|))
 (10 10 (:REWRITE REDUCE-INTEGERP-+))
 (10 10 (:REWRITE INTEGERP-MINUS-X))
 (10 10 (:META META-INTEGERP-CORRECT))
 (9 9 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:REWRITE |(integerp (* c x))|))
 (6 2 (:REWRITE |(< (+ d x) (+ c y))|))
 (4 4 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (4 4 (:REWRITE |(< 0 (- x))|))
 )
(NBR-CALLS-FLOG2-UPPER-BOUND
 (131 79 (:REWRITE DEFAULT-+-2))
 (130 130 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (130 130 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (130 130 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (130 130 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (119 103 (:REWRITE DEFAULT-*-2))
 (103 103 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (103 103 (:REWRITE DEFAULT-*-1))
 (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (91 91 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (79 79 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (79 79 (:REWRITE NORMALIZE-ADDENDS))
 (79 79 (:REWRITE DEFAULT-+-1))
 (65 33 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (63 39 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (62 30 (:REWRITE SIMPLIFY-SUMS-<))
 (46 30 (:REWRITE DEFAULT-<-2))
 (46 30 (:REWRITE DEFAULT-<-1))
 (41 41 (:META META-INTEGERP-CORRECT))
 (40 34 (:REWRITE REDUCE-INTEGERP-+))
 (39 39 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (34 34 (:REWRITE INTEGERP-MINUS-X))
 (33 33 (:REWRITE |(< (- x) (- y))|))
 (32 16 (:REWRITE |(< (+ c x) d)|))
 (18 12 (:REWRITE |(< d (+ c x))|))
 (17 17 (:REWRITE |(integerp (* c x))|))
 (14 14 (:REWRITE |(< 0 (- x))|))
 (11 11 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (6 6 (:REWRITE |(+ 0 x)|))
 (2 2 (:TYPE-PRESCRIPTION POSP-1/2+1/2*N))
 (2 2 (:REWRITE |(* 1 x)|))
 (1 1 (:REWRITE ZP-OPEN))
 )
(NBR-CALLS-FLOG2-IS-LOGARITHMIC
 (219 9 (:DEFINITION NBR-CALLS-FLOG2))
 (184 9 (:DEFINITION FLOG2))
 (70 42 (:REWRITE DEFAULT-+-2))
 (51 45 (:REWRITE DEFAULT-*-2))
 (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (50 50 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (45 45 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (45 45 (:REWRITE DEFAULT-*-1))
 (42 42 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (42 42 (:REWRITE NORMALIZE-ADDENDS))
 (42 42 (:REWRITE DEFAULT-+-1))
 (16 16 (:REWRITE REDUCE-INTEGERP-+))
 (16 16 (:REWRITE INTEGERP-MINUS-X))
 (16 16 (:META META-INTEGERP-CORRECT))
 (15 7 (:REWRITE SIMPLIFY-SUMS-<))
 (15 7 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (15 7 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (13 13 (:REWRITE |(integerp (* c x))|))
 (11 7 (:REWRITE DEFAULT-<-2))
 (11 7 (:REWRITE DEFAULT-<-1))
 (8 4 (:REWRITE |(< (+ c x) d)|))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (7 7 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (5 5 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (3 3 (:REWRITE |(< 0 (- x))|))
 )
