(NARY::MAG
 (13 13 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (7 7 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (1 1 (:REWRITE REDUCE-INTEGERP-+))
 (1 1 (:REWRITE INTEGERP-MINUS-X))
 (1 1 (:REWRITE |(< d (+ c x))|))
 (1 1 (:REWRITE |(< 0 (- x))|))
 (1 1 (:META META-INTEGERP-CORRECT))
 )
(NARY::PUSH-MOD-+-1
 (895 583 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (719 583 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (687 583 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (583 583 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (583 583 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (440 17 (:REWRITE MOD-X-Y-=-X . 4))
 (440 17 (:REWRITE MOD-X-Y-=-X . 3))
 (376 376 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (373 17 (:REWRITE MOD-ZERO . 3))
 (304 40 (:LINEAR MOD-BOUNDS-2))
 (304 40 (:LINEAR MOD-BOUNDS-1))
 (173 53 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (143 53 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (143 53 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (131 17 (:REWRITE MOD-ZERO . 2))
 (128 20 (:LINEAR MOD-BOUNDS-3))
 (118 72 (:REWRITE DEFAULT-+-2))
 (116 86 (:REWRITE DEFAULT-<-2))
 (116 86 (:REWRITE DEFAULT-<-1))
 (105 105 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (101 101 (:REWRITE |(< (- x) (- y))|))
 (74 74 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (74 74 (:REWRITE DEFAULT-*-2))
 (74 74 (:REWRITE DEFAULT-*-1))
 (73 73 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (72 72 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (72 72 (:REWRITE DEFAULT-+-1))
 (64 46 (:REWRITE DEFAULT-UNARY-/))
 (64 34 (:REWRITE MOD-COMPLETION))
 (63 3 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (53 53 (:REWRITE |(equal (- x) (- y))|))
 (50 50 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (50 50 (:REWRITE |(equal (- x) 0)|))
 (47 17 (:REWRITE MOD-NEG))
 (47 17 (:REWRITE MOD-CANCEL-*))
 (46 46 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (44 20 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (44 20 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (42 42 (:REWRITE |(< 0 (- x))|))
 (42 42 (:REWRITE |(< (- x) 0)|))
 (40 40 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (40 40 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (34 34 (:REWRITE INTEGERP-MINUS-X))
 (34 34 (:META META-INTEGERP-CORRECT))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
 (17 17 (:REWRITE MOD-X-Y-=-X . 2))
 (17 17 (:REWRITE MOD-MINUS-2))
 (15 15 (:REWRITE |(< (+ c x) d)|))
 (13 13 (:REWRITE |(< d (+ c x))|))
 (11 11 (:REWRITE |(integerp (* c x))|))
 (8 8 (:REWRITE |(equal (+ c x) d)|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
 (2 2 (:REWRITE |(< (+ c x) (+ d y))|))
 (2 2 (:REWRITE |(< (+ c x y) d)|))
 )
(NARY::PUSH-MOD-+-2
 (895 583 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (719 583 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (687 583 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (583 583 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (583 583 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (440 17 (:REWRITE MOD-X-Y-=-X . 4))
 (440 17 (:REWRITE MOD-X-Y-=-X . 3))
 (376 376 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (373 17 (:REWRITE MOD-ZERO . 3))
 (304 40 (:LINEAR MOD-BOUNDS-2))
 (304 40 (:LINEAR MOD-BOUNDS-1))
 (173 53 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (143 53 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (143 53 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (131 17 (:REWRITE MOD-ZERO . 2))
 (128 20 (:LINEAR MOD-BOUNDS-3))
 (118 72 (:REWRITE DEFAULT-+-2))
 (116 86 (:REWRITE DEFAULT-<-2))
 (116 86 (:REWRITE DEFAULT-<-1))
 (105 105 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (101 101 (:REWRITE |(< (- x) (- y))|))
 (74 74 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (74 74 (:REWRITE DEFAULT-*-2))
 (74 74 (:REWRITE DEFAULT-*-1))
 (73 73 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (72 72 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (72 72 (:REWRITE DEFAULT-+-1))
 (64 46 (:REWRITE DEFAULT-UNARY-/))
 (64 34 (:REWRITE MOD-COMPLETION))
 (63 3 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (53 53 (:REWRITE |(equal (- x) (- y))|))
 (50 50 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (50 50 (:REWRITE |(equal (- x) 0)|))
 (47 17 (:REWRITE MOD-NEG))
 (47 17 (:REWRITE MOD-CANCEL-*))
 (46 46 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (44 20 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (44 20 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (42 42 (:REWRITE |(< 0 (- x))|))
 (42 42 (:REWRITE |(< (- x) 0)|))
 (40 40 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (40 40 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (34 34 (:REWRITE INTEGERP-MINUS-X))
 (34 34 (:META META-INTEGERP-CORRECT))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (26 26 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
 (17 17 (:REWRITE MOD-X-Y-=-X . 2))
 (17 17 (:REWRITE MOD-MINUS-2))
 (15 15 (:REWRITE |(< (+ c x) d)|))
 (13 13 (:REWRITE |(< d (+ c x))|))
 (11 11 (:REWRITE |(integerp (* c x))|))
 (8 8 (:REWRITE |(equal (+ c x) d)|))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (3 3 (:REWRITE |(- (* c x))|))
 (2 2 (:REWRITE |(< (+ d x) (+ c y))|))
 (2 2 (:REWRITE |(< (+ c x) (+ d y))|))
 (2 2 (:REWRITE |(< (+ c x y) d)|))
 )
(NARY::PUSH-MOD-*-1
 (4340 87 (:REWRITE MOD-ZERO . 3))
 (3632 87 (:REWRITE MOD-X-Y-=-X . 3))
 (3558 87 (:REWRITE MOD-X-Y-=-X . 4))
 (2877 2877 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (2877 2877 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (2371 2371 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1752 24 (:REWRITE |(equal (* x y) 0)|))
 (1627 87 (:REWRITE MOD-ZERO . 2))
 (1459 429 (:REWRITE DEFAULT-*-2))
 (1313 113 (:LINEAR MOD-BOUNDS-2))
 (1307 107 (:LINEAR MOD-BOUNDS-1))
 (1160 2 (:REWRITE |(< x (if a b c))|))
 (1160 2 (:REWRITE |(< (if a b c) x)|))
 (837 195 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (613 189 (:REWRITE DEFAULT-+-2))
 (504 36 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (451 273 (:REWRITE DEFAULT-<-2))
 (451 273 (:REWRITE DEFAULT-<-1))
 (444 120 (:REWRITE DEFAULT-UNARY-MINUS))
 (429 429 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (429 429 (:REWRITE DEFAULT-*-1))
 (426 58 (:LINEAR MOD-BOUNDS-3))
 (367 367 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (352 174 (:REWRITE MOD-COMPLETION))
 (345 345 (:REWRITE |(< (- x) (- y))|))
 (326 302 (:REWRITE DEFAULT-UNARY-/))
 (302 302 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (269 91 (:REWRITE MOD-CANCEL-*))
 (233 189 (:REWRITE DEFAULT-+-1))
 (217 217 (:REWRITE |(equal (- x) (- y))|))
 (198 198 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (198 198 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (198 198 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (189 189 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (175 109 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (175 109 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (174 174 (:REWRITE |(equal (- x) 0)|))
 (170 170 (:REWRITE |(* c (* d x))|))
 (164 164 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (129 129 (:REWRITE |(< 0 (- x))|))
 (117 117 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (112 112 (:REWRITE |(< (- x) 0)|))
 (100 100 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (95 39 (:REWRITE |(< d (+ c x))|))
 (91 91 (:REWRITE MOD-MINUS-2))
 (87 87 (:REWRITE MOD-X-Y-=-X . 2))
 (49 21 (:REWRITE |(equal (+ c x) d)|))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
 (40 40 (:REWRITE |(- (* c x))|))
 (36 36 (:REWRITE |(integerp (* c x))|))
 (32 32 (:REWRITE |(< (+ c x) d)|))
 (12 12 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4 4 (:REWRITE |(< (+ d x) (+ c y))|))
 (4 4 (:REWRITE |(< (+ c x) (+ d y))|))
 (4 4 (:REWRITE |(< (+ c x y) d)|))
 )
(NARY::PUSH-MOD-*-2
 (4340 87 (:REWRITE MOD-ZERO . 3))
 (3632 87 (:REWRITE MOD-X-Y-=-X . 3))
 (3558 87 (:REWRITE MOD-X-Y-=-X . 4))
 (2877 2877 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (2877 2877 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (2371 2371 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1752 24 (:REWRITE |(equal (* x y) 0)|))
 (1627 87 (:REWRITE MOD-ZERO . 2))
 (1459 429 (:REWRITE DEFAULT-*-2))
 (1313 113 (:LINEAR MOD-BOUNDS-2))
 (1307 107 (:LINEAR MOD-BOUNDS-1))
 (1160 2 (:REWRITE |(< x (if a b c))|))
 (1160 2 (:REWRITE |(< (if a b c) x)|))
 (837 195 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (613 189 (:REWRITE DEFAULT-+-2))
 (504 36 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (451 273 (:REWRITE DEFAULT-<-2))
 (451 273 (:REWRITE DEFAULT-<-1))
 (444 120 (:REWRITE DEFAULT-UNARY-MINUS))
 (429 429 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (429 429 (:REWRITE DEFAULT-*-1))
 (426 58 (:LINEAR MOD-BOUNDS-3))
 (367 367 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (352 174 (:REWRITE MOD-COMPLETION))
 (345 345 (:REWRITE |(< (- x) (- y))|))
 (326 302 (:REWRITE DEFAULT-UNARY-/))
 (302 302 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (269 91 (:REWRITE MOD-CANCEL-*))
 (233 189 (:REWRITE DEFAULT-+-1))
 (217 217 (:REWRITE |(equal (- x) (- y))|))
 (198 198 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (198 198 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (198 198 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (189 189 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (175 109 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (175 109 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (174 174 (:REWRITE |(equal (- x) 0)|))
 (170 170 (:REWRITE |(* c (* d x))|))
 (164 164 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (129 129 (:REWRITE |(< 0 (- x))|))
 (117 117 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (112 112 (:REWRITE |(< (- x) 0)|))
 (100 100 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (95 39 (:REWRITE |(< d (+ c x))|))
 (91 91 (:REWRITE MOD-MINUS-2))
 (87 87 (:REWRITE MOD-X-Y-=-X . 2))
 (49 21 (:REWRITE |(equal (+ c x) d)|))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-4D))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-3D))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-2D))
 (46 46 (:TYPE-PRESCRIPTION NOT-INTEGERP-1D))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-3C))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-2C))
 (44 44 (:TYPE-PRESCRIPTION NOT-INTEGERP-1C))
 (40 40 (:REWRITE |(- (* c x))|))
 (36 36 (:REWRITE |(integerp (* c x))|))
 (32 32 (:REWRITE |(< (+ c x) d)|))
 (12 12 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4 4 (:REWRITE |(< (+ d x) (+ c y))|))
 (4 4 (:REWRITE |(< (+ c x) (+ d y))|))
 (4 4 (:REWRITE |(< (+ c x y) d)|))
 )
(NARY::PUSH-MOD-*)
(NARY::PUSH-MOD-+)
(NARY::MOD-MOD
 (747 291 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (327 291 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (323 291 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (291 291 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (291 291 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (207 207 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (207 207 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (207 207 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (207 207 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (199 10 (:REWRITE MOD-X-Y-=-X . 4))
 (199 10 (:REWRITE MOD-X-Y-=-X . 3))
 (156 10 (:REWRITE MOD-ZERO . 3))
 (152 12 (:LINEAR MOD-BOUNDS-3))
 (146 10 (:REWRITE MOD-ZERO . 2))
 (118 10 (:REWRITE CANCEL-MOD-+))
 (96 48 (:REWRITE SIMPLIFY-SUMS-<))
 (96 48 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (75 23 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (72 48 (:REWRITE DEFAULT-<-2))
 (72 48 (:REWRITE DEFAULT-<-1))
 (65 23 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (65 23 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (50 50 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (50 50 (:REWRITE |(< (- x) (- y))|))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (48 48 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (31 31 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (31 31 (:REWRITE DEFAULT-UNARY-/))
 (30 20 (:REWRITE MOD-COMPLETION))
 (26 26 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (25 25 (:REWRITE REDUCE-INTEGERP-+))
 (25 25 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (25 25 (:REWRITE INTEGERP-MINUS-X))
 (25 25 (:REWRITE DEFAULT-*-2))
 (25 25 (:REWRITE DEFAULT-*-1))
 (25 25 (:META META-INTEGERP-CORRECT))
 (25 5 (:REWRITE MOD-+-CANCEL-0-WEAK))
 (24 24 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (24 24 (:REWRITE |(< 0 (- x))|))
 (23 23 (:REWRITE |(equal (- x) (- y))|))
 (22 22 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (22 22 (:REWRITE |(< (- x) 0)|))
 (20 20 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (20 20 (:REWRITE |(equal (- x) 0)|))
 (20 10 (:REWRITE MOD-NEG))
 (20 10 (:REWRITE MOD-CANCEL-*))
 (16 16 (:REWRITE |(integerp (* c x))|))
 (16 10 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (16 10 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (10 10 (:REWRITE MOD-X-Y-=-X . 2))
 (10 10 (:REWRITE MOD-MINUS-2))
 (7 1 (:REWRITE REWRITE-MOD-MOD-WEAK))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (3 3 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE MOD-POSITIVE . 3))
 (2 2 (:REWRITE MOD-POSITIVE . 2))
 (2 2 (:REWRITE MOD-NEGATIVE . 3))
 (2 2 (:REWRITE MOD-NEGATIVE . 2))
 (1 1 (:REWRITE MOD-ZERO . 1))
 (1 1 (:REWRITE MOD-NONPOSITIVE))
 (1 1 (:REWRITE MOD-NONNEGATIVE))
 (1 1 (:REWRITE |(* c (* d x))|))
 )
(NARY::INTEGERP-MOD+
 (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (3 3 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 )
(NARY::INTEGERP-PLUS
 (17 17 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (17 17 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (17 17 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (17 17 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (14 14 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (14 14 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (14 14 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE INTEGERP-+-REDUCE-LEADING-RATIONAL-CONSTANT))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE |(+ 0 x)|))
 )
(NARY::INTEGERP-MOD-REWRITE
 (38 38 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (38 38 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (38 38 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (38 38 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (38 38 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (38 38 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (38 38 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (38 38 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (25 1 (:REWRITE CANCEL-FLOOR-+))
 (14 2 (:REWRITE DEFAULT-*-2))
 (13 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 1 (:REWRITE DEFAULT-+-2))
 (7 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (7 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (7 1 (:REWRITE DEFAULT-UNARY-/))
 (7 1 (:REWRITE CANCEL-MOD-+))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-2))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE-1))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-2))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE-1))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (5 5 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (4 4 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE INTEGERP-MINUS-X))
 (4 4 (:REWRITE |(equal (- x) 0)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:META META-INTEGERP-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (2 2 (:REWRITE MOD-COMPLETION))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 1 (:REWRITE FLOOR-COMPLETION))
 (1 1 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (1 1 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (1 1 (:REWRITE NORMALIZE-ADDENDS))
 (1 1 (:REWRITE MOD-ZERO . 3))
 (1 1 (:REWRITE MOD-ZERO . 2))
 (1 1 (:REWRITE MOD-X-Y-=-X . 4))
 (1 1 (:REWRITE MOD-X-Y-=-X . 3))
 (1 1 (:REWRITE MOD-X-Y-=-X . 2))
 (1 1 (:REWRITE MOD-NEG))
 (1 1 (:REWRITE MOD-MINUS-2))
 (1 1 (:REWRITE MOD-CANCEL-*))
 (1 1 (:REWRITE FLOOR-ZERO . 4))
 (1 1 (:REWRITE FLOOR-ZERO . 3))
 (1 1 (:REWRITE FLOOR-ZERO . 2))
 (1 1 (:REWRITE FLOOR-MINUS-WEAK))
 (1 1 (:REWRITE FLOOR-MINUS-2))
 (1 1 (:REWRITE FLOOR-CANCEL-*-WEAK))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE |(integerp (* c x))|))
 (1 1 (:REWRITE |(- (* c x))|))
 )
(NARY::MOD-NOT-ACL2-NUMBERP
 (5 5 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (5 5 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (5 5 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (5 5 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (5 5 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (5 5 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 )
(NARY::MOD-ARG-TYPE
 (55 55 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (55 55 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (55 55 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (55 55 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (55 55 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (55 55 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (55 55 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (55 55 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (7 1 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (7 1 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (7 1 (:REWRITE CANCEL-MOD-+))
 (3 3 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE |(equal (- x) 0)|))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (2 2 (:REWRITE MOD-COMPLETION))
 (1 1 (:REWRITE MOD-ZERO . 3))
 (1 1 (:REWRITE MOD-ZERO . 2))
 (1 1 (:REWRITE MOD-X-Y-=-X . 4))
 (1 1 (:REWRITE MOD-X-Y-=-X . 3))
 (1 1 (:REWRITE MOD-X-Y-=-X . 2))
 (1 1 (:REWRITE NARY::MOD-NOT-ACL2-NUMBERP))
 (1 1 (:REWRITE MOD-NEG))
 (1 1 (:REWRITE MOD-MINUS-2))
 (1 1 (:REWRITE MOD-CANCEL-*))
 )
(NARY::EQUAL-MOD-TRANSFERS-TYPE
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-MOD))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (2 2 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (2 2 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (2 2 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2 2 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (2 2 (:TYPE-PRESCRIPTION INTEGERP-MOD))
 )
(NARY::TIMES-ZERO)
(NARY::MOD-N-OF-N-REDUCTION
 (176 11 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (109 49 (:REWRITE DEFAULT-UNARY-/))
 (102 102 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (95 73 (:REWRITE DEFAULT-*-1))
 (89 73 (:REWRITE DEFAULT-*-2))
 (87 57 (:REWRITE DEFAULT-+-2))
 (66 57 (:REWRITE DEFAULT-+-1))
 (62 44 (:REWRITE DEFAULT-UNARY-MINUS))
 (46 46 (:REWRITE RATIONALP-*))
 (46 23 (:REWRITE DEFAULT-NUMERATOR))
 (46 23 (:REWRITE DEFAULT-DENOMINATOR))
 (33 11 (:DEFINITION NFIX))
 (32 32 (:REWRITE DEFAULT-<-2))
 (32 32 (:REWRITE DEFAULT-<-1))
 (11 11 (:DEFINITION IFIX))
 (5 5 (:REWRITE FOLD-CONSTS-IN-+))
 (2 1 (:REWRITE NARY::MOD-NOT-ACL2-NUMBERP))
 )
(NARY::MOD-N-OF-MOD-N-REDUCTION
 (4 4 (:REWRITE NARY::MOD-NOT-ACL2-NUMBERP))
 )
(NARY::UN-MOD)
(NARY::MOD-EQUIV)
(NARY::OPEN-MOD-EQUIV-IN-CONCLUSION
 (128 8 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (56 36 (:REWRITE DEFAULT-+-2))
 (44 36 (:REWRITE DEFAULT-+-1))
 (32 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (30 30 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (30 14 (:REWRITE DEFAULT-*-1))
 (28 14 (:REWRITE DEFAULT-*-2))
 (24 8 (:DEFINITION NFIX))
 (20 20 (:REWRITE DEFAULT-<-2))
 (20 20 (:REWRITE DEFAULT-<-1))
 (16 4 (:REWRITE DEFAULT-UNARY-/))
 (10 8 (:REWRITE RATIONALP-*))
 (10 4 (:REWRITE DEFAULT-NUMERATOR))
 (8 8 (:DEFINITION IFIX))
 (8 4 (:REWRITE NARY::MOD-NOT-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE RATIONALP-UNARY-/))
 )
(NARY::MOD-EQUIV-OF-MOD
 (3 3 (:REWRITE NARY::MOD-NOT-ACL2-NUMBERP))
 )
(NARY::MOD-EQUIV-NO-MOD
 (64 4 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (28 18 (:REWRITE DEFAULT-+-2))
 (26 26 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (22 18 (:REWRITE DEFAULT-+-1))
 (16 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 8 (:REWRITE DEFAULT-*-2))
 (16 8 (:REWRITE DEFAULT-*-1))
 (15 15 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 4 (:DEFINITION NFIX))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (8 2 (:REWRITE DEFAULT-UNARY-/))
 (6 4 (:REWRITE RATIONALP-*))
 (6 2 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:DEFINITION IFIX))
 (4 2 (:REWRITE DEFAULT-DENOMINATOR))
 (4 2 (:DEFINITION NOT))
 (3 2 (:REWRITE NARY::MOD-NOT-ACL2-NUMBERP))
 (2 2 (:REWRITE RATIONALP-UNARY-/))
 )
(NARY::MOD-+-CONGRUENCE
 (86 86 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE NARY::MOD-MOD))
 )
(NARY::MOD-*-CONGRUENCE
 (76 76 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NARY::PUSH-MOD-EXPT
 (2517 553 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (2517 553 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1848 1848 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (1848 1848 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (1848 1848 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (1816 408 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (553 553 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (553 553 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (553 553 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (492 4 (:LINEAR MOD-BOUNDS-3))
 (408 408 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (408 408 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (400 8 (:LINEAR MOD-BOUNDS-2))
 (400 8 (:LINEAR MOD-BOUNDS-1))
 (323 3 (:REWRITE CANCEL-MOD-+))
 (314 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (246 246 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (194 26 (:REWRITE DEFAULT-TIMES-1))
 (188 10 (:REWRITE |(* y x)|))
 (183 3 (:REWRITE MOD-X-Y-=-X . 4))
 (183 3 (:REWRITE MOD-X-Y-=-X . 3))
 (177 3 (:REWRITE MOD-ZERO . 4))
 (174 26 (:REWRITE DEFAULT-TIMES-2))
 (157 6 (:REWRITE DEFAULT-MOD-RATIO))
 (108 3 (:REWRITE |(integerp (- x))|))
 (96 3 (:REWRITE MOD-ZERO . 3))
 (96 3 (:REWRITE |(* (- x) y)|))
 (55 3 (:REWRITE MOD-X-Y-=-X . 2))
 (55 3 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (55 3 (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (46 6 (:REWRITE DEFAULT-MOD-1))
 (46 3 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (46 3 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (46 3 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (46 3 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (41 1 (:REWRITE |(equal (expt x n) 0)|))
 (38 18 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (38 18 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (35 3 (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (35 3 (:REWRITE DEFAULT-MINUS))
 (35 3 (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (35 3 (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (34 5 (:REWRITE DEFAULT-EXPT-1))
 (28 18 (:REWRITE DEFAULT-LESS-THAN-2))
 (28 18 (:REWRITE DEFAULT-LESS-THAN-1))
 (23 3 (:REWRITE NARY::MOD-NOT-ACL2-NUMBERP))
 (21 3 (:REWRITE MOD-CANCEL-*-CONST))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (18 18 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (18 18 (:REWRITE THE-FLOOR-BELOW))
 (18 18 (:REWRITE THE-FLOOR-ABOVE))
 (18 18 (:REWRITE SIMPLIFY-SUMS-<))
 (18 18 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (18 18 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (18 18 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (18 18 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (18 18 (:REWRITE INTEGERP-<-CONSTANT))
 (18 18 (:REWRITE CONSTANT-<-INTEGERP))
 (18 18 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (18 18 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (18 18 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (18 18 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< c (- x))|))
 (18 18 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (18 18 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (18 18 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (18 18 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (18 18 (:REWRITE |(< (/ x) (/ y))|))
 (18 18 (:REWRITE |(< (- x) c)|))
 (18 18 (:REWRITE |(< (- x) (- y))|))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:META META-INTEGERP-CORRECT))
 (10 10 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (10 10 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (10 10 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (10 10 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (10 10 (:REWRITE DEFAULT-DIVIDE))
 (10 10 (:REWRITE |(< (/ x) 0)|))
 (10 10 (:REWRITE |(< (* x y) 0)|))
 (8 8 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (8 8 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (8 8 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< 0 (/ x))|))
 (8 8 (:REWRITE |(< 0 (* x y))|))
 (8 8 (:LINEAR EXPT-IS-WEAKLY-INCREASING-FOR-BASE->-1))
 (8 8 (:LINEAR EXPT-IS-WEAKLY-DECREASING-FOR-POS-BASE-<-1))
 (8 8 (:LINEAR EXPT-IS-INCREASING-FOR-BASE->-1))
 (8 8 (:LINEAR EXPT-IS-DECREASING-FOR-POS-BASE-<-1))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (6 6 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (6 6 (:REWRITE DEFAULT-MOD-2))
 (6 6 (:REWRITE |(equal c (/ x))|))
 (6 6 (:REWRITE |(equal c (- x))|))
 (6 6 (:REWRITE |(equal (/ x) c)|))
 (6 6 (:REWRITE |(equal (/ x) (/ y))|))
 (6 6 (:REWRITE |(equal (- x) c)|))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 (5 5 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (5 5 (:REWRITE DEFAULT-EXPT-2))
 (5 5 (:REWRITE |(expt 1/c n)|))
 (5 5 (:REWRITE |(expt (- x) n)|))
 (4 4 (:LINEAR EXPT-X->=-X))
 (4 4 (:LINEAR EXPT-X->-X))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-UPPER-<))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<=))
 (4 4 (:LINEAR EXPT-LINEAR-LOWER-<))
 (4 4 (:LINEAR EXPT->=-1-TWO))
 (4 4 (:LINEAR EXPT->=-1-ONE))
 (4 4 (:LINEAR EXPT->-1-TWO))
 (4 4 (:LINEAR EXPT->-1-ONE))
 (4 4 (:LINEAR EXPT-<=-1-TWO))
 (4 4 (:LINEAR EXPT-<=-1-ONE))
 (4 4 (:LINEAR EXPT-<-1-TWO))
 (4 4 (:LINEAR EXPT-<-1-ONE))
 (3 3 (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (3 3 (:REWRITE |(mod x (- y))| . 3))
 (3 3 (:REWRITE |(mod x (- y))| . 2))
 (3 3 (:REWRITE |(mod x (- y))| . 1))
 (3 3 (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (3 3 (:REWRITE |(mod (- x) y)| . 3))
 (3 3 (:REWRITE |(mod (- x) y)| . 2))
 (3 3 (:REWRITE |(mod (- x) y)| . 1))
 (3 3 (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (3 3 (:REWRITE |(- (* c x))|))
 (3 3 (:REWRITE |(* 0 x)|))
 )
(NARY::MOD-EXPT-CONGRUENCE
 (33 10 (:REWRITE DEFAULT-*-2))
 (30 10 (:REWRITE COMMUTATIVITY-OF-+))
 (20 20 (:REWRITE DEFAULT-+-2))
 (20 20 (:REWRITE DEFAULT-+-1))
 (18 18 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (18 18 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (15 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-<-1))
 (13 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (13 10 (:REWRITE DEFAULT-*-1))
 (12 12 (:REWRITE ZIP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION EXPT))
 )
(NARY::MOD---CONGRUENCE
 (3812 18 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (3557 849 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (3557 849 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (3185 3185 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (3185 3185 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3185 3185 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (2140 18 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (1904 70 (:LINEAR MOD-BOUNDS-2))
 (1904 70 (:LINEAR MOD-BOUNDS-1))
 (1005 849 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (849 849 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (849 849 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (824 13 (:REWRITE MOD-X-Y-=-X . 3))
 (821 13 (:REWRITE MOD-X-Y-=-X . 4))
 (677 677 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (677 677 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (675 20 (:REWRITE MOD-ZERO . 4))
 (590 20 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (590 20 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (590 20 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (590 20 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (415 93 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (398 78 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (313 220 (:REWRITE |(< c (- x))|))
 (310 217 (:REWRITE |(< (- x) c)|))
 (272 214 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (272 214 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (249 220 (:REWRITE DEFAULT-LESS-THAN-2))
 (249 220 (:REWRITE DEFAULT-LESS-THAN-1))
 (244 186 (:REWRITE DEFAULT-TIMES-2))
 (244 186 (:REWRITE DEFAULT-TIMES-1))
 (240 13 (:REWRITE CANCEL-MOD-+))
 (220 220 (:REWRITE THE-FLOOR-BELOW))
 (220 220 (:REWRITE THE-FLOOR-ABOVE))
 (220 220 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (220 220 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (220 220 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (220 220 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (220 220 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (220 220 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (220 220 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (220 220 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (220 220 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (220 220 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (220 220 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (220 220 (:REWRITE |(< (/ x) (/ y))|))
 (220 220 (:REWRITE |(< (- x) (- y))|))
 (214 214 (:REWRITE SIMPLIFY-SUMS-<))
 (214 214 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (214 214 (:REWRITE INTEGERP-<-CONSTANT))
 (214 214 (:REWRITE CONSTANT-<-INTEGERP))
 (212 143 (:REWRITE DEFAULT-PLUS-2))
 (210 123 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (164 143 (:REWRITE DEFAULT-PLUS-1))
 (138 96 (:REWRITE |(equal (- x) c)|))
 (125 15 (:REWRITE REDUCE-RATIONALP-*))
 (123 123 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (123 123 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (123 123 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (110 110 (:REWRITE |(< 0 (/ x))|))
 (110 110 (:REWRITE |(< 0 (* x y))|))
 (110 110 (:REWRITE |(< (/ x) 0)|))
 (110 110 (:REWRITE |(< (* x y) 0)|))
 (107 107 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (107 107 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (107 107 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (107 107 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (97 97 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (97 97 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (97 97 (:REWRITE |(equal (/ x) (/ y))|))
 (96 96 (:REWRITE |(equal c (/ x))|))
 (96 96 (:REWRITE |(equal c (- x))|))
 (96 96 (:REWRITE |(equal (/ x) c)|))
 (93 93 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (92 92 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (92 92 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (92 92 (:REWRITE DEFAULT-DIVIDE))
 (92 13 (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (88 13 (:REWRITE MOD-CANCEL-*-CONST))
 (85 13 (:REWRITE MOD-X-Y-=-X . 2))
 (85 13 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (85 13 (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (84 15 (:REWRITE RATIONALP-X))
 (79 15 (:REWRITE |(equal (mod (+ x y) z) x)|))
 (61 57 (:REWRITE INTEGERP-MINUS-X))
 (57 57 (:REWRITE REDUCE-INTEGERP-+))
 (57 57 (:META META-INTEGERP-CORRECT))
 (56 1 (:REWRITE |(equal (mod a n) (mod b n))|))
 (49 49 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (45 9 (:REWRITE BUBBLE-DOWN-+-MATCH-3))
 (34 34 (:REWRITE |(equal (+ (- c) x) y)|))
 (33 9 (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (33 9 (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (29 29 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (29 29 (:REWRITE |(- (* c x))|))
 (28 28 (:REWRITE DEFAULT-MOD-2))
 (27 3 (:REWRITE ACL2-NUMBERP-X))
 (26 26 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (21 21 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (21 5 (:REWRITE MOD-ZERO . 2))
 (20 4 (:DEFINITION RFIX))
 (15 15 (:REWRITE REDUCE-RATIONALP-+))
 (15 15 (:REWRITE RATIONALP-MINUS-X))
 (15 15 (:META META-RATIONALP-CORRECT))
 (13 13 (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (12 12 (:REWRITE |(mod x (- y))| . 3))
 (12 12 (:REWRITE |(mod x (- y))| . 2))
 (12 12 (:REWRITE |(mod x (- y))| . 1))
 (12 12 (:REWRITE |(mod (- x) y)| . 3))
 (12 12 (:REWRITE |(mod (- x) y)| . 2))
 (9 9 (:REWRITE NARY::MOD-NOT-ACL2-NUMBERP))
 (9 9 (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (9 9 (:REWRITE |(+ c (+ d x))|))
 (9 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (9 1 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (9 1 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (9 1 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (9 1 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (9 1 (:REWRITE MOD-POSITIVE . 3))
 (9 1 (:REWRITE MOD-NEGATIVE . 3))
 (8 2 (:REWRITE |(+ x x)|))
 (6 6 (:REWRITE |(* 0 x)|))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (5 1 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (5 1 (:REWRITE MOD-NONPOSITIVE))
 (5 1 (:REWRITE MOD-NONNEGATIVE))
 (4 4 (:REWRITE |(not (equal x (/ y)))|))
 (4 4 (:REWRITE |(equal x (/ y))|))
 (1 1 (:REWRITE MOD-POSITIVE . 2))
 (1 1 (:REWRITE MOD-POSITIVE . 1))
 (1 1 (:REWRITE MOD-NEGATIVE . 2))
 (1 1 (:REWRITE MOD-NEGATIVE . 1))
 (1 1 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (1 1 (:REWRITE |(mod (mod x y) z)| . 3))
 (1 1 (:REWRITE |(mod (mod x y) z)| . 2))
 )
(NARY::INTEGERP---TYPE)
(NARY::INTEGERP-+-TYPE)
(NARY::INTEGERP-*-TYPE)
(NARY::INTEGERP-EXPT-TYPE
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (2 2 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (2 2 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 )
(NARY::INTEGERP-MOD-TYPE
 (18 3 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (8 3 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (8 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (8 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-4B))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (6 6 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (6 6 (:TYPE-PRESCRIPTION NARY::INTEGERP-*-TYPE))
 (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 4))
 (3 3 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (3 3 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (3 3 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (3 3 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (3 3 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 )
