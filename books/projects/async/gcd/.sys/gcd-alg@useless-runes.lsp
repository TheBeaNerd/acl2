(ADE::GCD-ALG
 (103 3 (:REWRITE |(< (if a b c) x)|))
 (45 5 (:REWRITE ACL2-NUMBERP-X))
 (26 26 (:REWRITE THE-FLOOR-BELOW))
 (26 26 (:REWRITE THE-FLOOR-ABOVE))
 (26 26 (:REWRITE DEFAULT-LESS-THAN-2))
 (26 26 (:REWRITE DEFAULT-LESS-THAN-1))
 (23 23 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (23 23 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (23 23 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (23 23 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (23 23 (:REWRITE INTEGERP-<-CONSTANT))
 (23 23 (:REWRITE CONSTANT-<-INTEGERP))
 (23 23 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (23 23 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (23 23 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (23 23 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< c (- x))|))
 (23 23 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (23 23 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (23 23 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (23 23 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (23 23 (:REWRITE |(< (/ x) (/ y))|))
 (23 23 (:REWRITE |(< (- x) c)|))
 (23 23 (:REWRITE |(< (- x) (- y))|))
 (22 22 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (20 5 (:REWRITE RATIONALP-X))
 (13 13 (:REWRITE |(< (/ x) 0)|))
 (13 13 (:REWRITE |(< (* x y) 0)|))
 (11 11 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (11 11 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (8 8 (:REWRITE ZP-OPEN))
 (7 7 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:META META-INTEGERP-CORRECT))
 (5 5 (:REWRITE REDUCE-RATIONALP-+))
 (5 5 (:REWRITE REDUCE-RATIONALP-*))
 (5 5 (:REWRITE RATIONALP-MINUS-X))
 (5 5 (:REWRITE |(< (+ c/d x) y)|))
 (5 5 (:REWRITE |(< (+ (- c) x) y)|))
 (5 5 (:META META-RATIONALP-CORRECT))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 4 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (4 4 (:REWRITE DEFAULT-MINUS))
 (4 4 (:REWRITE |(equal c (/ x))|))
 (4 4 (:REWRITE |(equal c (- x))|))
 (4 4 (:REWRITE |(equal (/ x) c)|))
 (4 4 (:REWRITE |(equal (/ x) (/ y))|))
 (4 4 (:REWRITE |(equal (- x) c)|))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(+ c (+ d x))|))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 )
(ADE::GCD-ALG-IS-POSITIVE
 (25 5 (:REWRITE |(+ y x)|))
 (21 21 (:REWRITE THE-FLOOR-BELOW))
 (21 21 (:REWRITE THE-FLOOR-ABOVE))
 (21 21 (:REWRITE SIMPLIFY-SUMS-<))
 (21 21 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (21 21 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (21 21 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (21 21 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (21 21 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (21 21 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (21 21 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (21 21 (:REWRITE INTEGERP-<-CONSTANT))
 (21 21 (:REWRITE DEFAULT-LESS-THAN-2))
 (21 21 (:REWRITE DEFAULT-LESS-THAN-1))
 (21 21 (:REWRITE CONSTANT-<-INTEGERP))
 (21 21 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (21 21 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (21 21 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (21 21 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< c (- x))|))
 (21 21 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (21 21 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (21 21 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (21 21 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (21 21 (:REWRITE |(< (/ x) (/ y))|))
 (21 21 (:REWRITE |(< (- x) c)|))
 (21 21 (:REWRITE |(< (- x) (- y))|))
 (15 15 (:REWRITE DEFAULT-PLUS-2))
 (15 15 (:REWRITE DEFAULT-PLUS-1))
 (15 10 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (15 10 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (10 10 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (10 10 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (10 10 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (10 10 (:REWRITE NORMALIZE-ADDENDS))
 (10 10 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (10 10 (:REWRITE DEFAULT-MINUS))
 (10 10 (:REWRITE |(equal c (/ x))|))
 (10 10 (:REWRITE |(equal c (- x))|))
 (10 10 (:REWRITE |(equal (/ x) c)|))
 (10 10 (:REWRITE |(equal (/ x) (/ y))|))
 (10 10 (:REWRITE |(equal (- x) c)|))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 (8 8 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (8 8 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (8 8 (:REWRITE |(< (/ x) 0)|))
 (8 8 (:REWRITE |(< (* x y) 0)|))
 (7 7 (:REWRITE REDUCE-INTEGERP-+))
 (7 7 (:REWRITE INTEGERP-MINUS-X))
 (7 7 (:META META-INTEGERP-CORRECT))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (6 6 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (6 6 (:REWRITE |(< 0 (/ x))|))
 (6 6 (:REWRITE |(< 0 (* x y))|))
 (5 5 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 )
(ADE::GCD-ALG-COMMUTATIVE
 (495 15 (:DEFINITION POSP))
 (55 55 (:REWRITE THE-FLOOR-BELOW))
 (55 55 (:REWRITE THE-FLOOR-ABOVE))
 (55 55 (:REWRITE SIMPLIFY-SUMS-<))
 (55 55 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (55 55 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (55 55 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (55 55 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (55 55 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (55 55 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (55 55 (:REWRITE INTEGERP-<-CONSTANT))
 (55 55 (:REWRITE DEFAULT-LESS-THAN-2))
 (55 55 (:REWRITE DEFAULT-LESS-THAN-1))
 (55 55 (:REWRITE CONSTANT-<-INTEGERP))
 (55 55 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (55 55 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (55 55 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (55 55 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< c (- x))|))
 (55 55 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (55 55 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (55 55 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (55 55 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (55 55 (:REWRITE |(< (/ x) (/ y))|))
 (55 55 (:REWRITE |(< (- x) c)|))
 (55 55 (:REWRITE |(< (- x) (- y))|))
 (40 40 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (25 13 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (25 13 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (25 13 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (21 21 (:REWRITE REDUCE-INTEGERP-+))
 (21 21 (:REWRITE INTEGERP-MINUS-X))
 (21 21 (:META META-INTEGERP-CORRECT))
 (20 4 (:REWRITE |(+ y x)|))
 (16 16 (:REWRITE ZP-OPEN))
 (16 16 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (16 16 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (16 16 (:REWRITE |(< (/ x) 0)|))
 (16 16 (:REWRITE |(< (* x y) 0)|))
 (15 15 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (15 15 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (15 15 (:REWRITE |(< 0 (/ x))|))
 (15 15 (:REWRITE |(< 0 (* x y))|))
 (13 13 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (13 13 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (13 13 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (13 13 (:REWRITE |(equal c (/ x))|))
 (13 13 (:REWRITE |(equal c (- x))|))
 (13 13 (:REWRITE |(equal (/ x) c)|))
 (13 13 (:REWRITE |(equal (/ x) (/ y))|))
 (13 13 (:REWRITE |(equal (- x) c)|))
 (13 13 (:REWRITE |(equal (- x) (- y))|))
 (12 12 (:REWRITE DEFAULT-PLUS-2))
 (12 12 (:REWRITE DEFAULT-PLUS-1))
 (8 8 (:TYPE-PRESCRIPTION POSP))
 (8 8 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (8 8 (:REWRITE NORMALIZE-ADDENDS))
 (8 8 (:REWRITE DEFAULT-MINUS))
 )
(ADE::GCD-ALG-IS-COMMON-DIVISOR
 (9341 20 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (5431 20 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (4882 4882 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (4882 4882 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (4882 4882 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (3432 126 (:DEFINITION POSP))
 (3352 888 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (3352 888 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (2873 62 (:REWRITE CANCEL-MOD-+))
 (2754 448 (:REWRITE DEFAULT-PLUS-2))
 (2580 153 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2157 62 (:REWRITE MOD-X-Y-=-X . 3))
 (1399 448 (:REWRITE DEFAULT-PLUS-1))
 (1256 62 (:REWRITE MOD-X-Y-=-X . 2))
 (1225 74 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1127 62 (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1117 62 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (971 77 (:REWRITE DEFAULT-MOD-RATIO))
 (888 888 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (888 888 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (870 870 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (870 870 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (785 399 (:REWRITE DEFAULT-LESS-THAN-1))
 (757 370 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (724 724 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (720 177 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (628 62 (:REWRITE MOD-X-Y-=-X . 4))
 (594 316 (:REWRITE DEFAULT-TIMES-2))
 (562 399 (:REWRITE DEFAULT-LESS-THAN-2))
 (484 163 (:REWRITE DEFAULT-MINUS))
 (451 73 (:REWRITE MOD-ZERO . 4))
 (418 219 (:REWRITE DEFAULT-DIVIDE))
 (416 13 (:REWRITE MOD-ZERO . 1))
 (409 397 (:REWRITE |(< (- x) (- y))|))
 (400 400 (:REWRITE THE-FLOOR-BELOW))
 (400 400 (:REWRITE THE-FLOOR-ABOVE))
 (397 397 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (397 397 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (397 397 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (397 397 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (397 397 (:REWRITE INTEGERP-<-CONSTANT))
 (397 397 (:REWRITE CONSTANT-<-INTEGERP))
 (397 397 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (397 397 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (397 397 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (397 397 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (397 397 (:REWRITE |(< c (- x))|))
 (397 397 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (397 397 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (397 397 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (397 397 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (397 397 (:REWRITE |(< (/ x) (/ y))|))
 (397 397 (:REWRITE |(< (- x) c)|))
 (384 76 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (374 74 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (358 13 (:REWRITE MOD-ZERO . 2))
 (330 58 (:LINEAR MOD-BOUNDS-2))
 (316 316 (:REWRITE DEFAULT-TIMES-1))
 (237 237 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (233 62 (:REWRITE MOD-CANCEL-*-CONST))
 (220 177 (:REWRITE |(equal (- x) (- y))|))
 (219 219 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (216 177 (:REWRITE |(equal (- x) c)|))
 (208 62 (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (178 57 (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (178 57 (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (177 177 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (177 177 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (177 177 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (177 177 (:REWRITE |(equal c (/ x))|))
 (177 177 (:REWRITE |(equal c (- x))|))
 (177 177 (:REWRITE |(equal (/ x) c)|))
 (177 177 (:REWRITE |(equal (/ x) (/ y))|))
 (162 162 (:REWRITE |(< 0 (/ x))|))
 (162 162 (:REWRITE |(< 0 (* x y))|))
 (159 159 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (159 159 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (156 42 (:REWRITE ZP-OPEN))
 (151 141 (:REWRITE INTEGERP-MINUS-X))
 (142 77 (:REWRITE DEFAULT-MOD-2))
 (142 62 (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (141 141 (:REWRITE REDUCE-INTEGERP-+))
 (141 141 (:META META-INTEGERP-CORRECT))
 (137 57 (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (137 57 (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (136 4 (:REWRITE |(* (+ x y) z)|))
 (130 60 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (105 105 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (102 102 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (98 98 (:TYPE-PRESCRIPTION POSP))
 (83 75 (:REWRITE |(- (* c x))|))
 (77 77 (:REWRITE DEFAULT-MOD-1))
 (74 74 (:REWRITE |(< (/ x) 0)|))
 (74 74 (:REWRITE |(< (* x y) 0)|))
 (62 62 (:REWRITE |(mod x (- y))| . 3))
 (62 62 (:REWRITE |(mod x (- y))| . 2))
 (62 62 (:REWRITE |(mod x (- y))| . 1))
 (62 62 (:REWRITE |(mod (- x) y)| . 3))
 (62 62 (:REWRITE |(mod (- x) y)| . 2))
 (57 9 (:REWRITE |(+ x x)|))
 (47 47 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (47 47 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (45 1 (:REWRITE |(equal (mod a n) (mod b n))|))
 (40 20 (:REWRITE |(equal (mod (+ x y) z) x)|))
 (38 38 (:REWRITE |(equal (+ (- c) x) y)|))
 (20 2 (:REWRITE |(* x (- y))|))
 (19 2 (:REWRITE |(- (+ x y))|))
 (18 18 (:REWRITE |(+ c (+ d x))|))
 (16 3 (:REWRITE |(* a (/ a))|))
 (12 12 (:REWRITE |(< (+ c/d x) y)|))
 (12 12 (:REWRITE |(< (+ (- c) x) y)|))
 (9 9 (:REWRITE |(< y (+ (- c) x))|))
 (9 9 (:REWRITE |(< x (+ c/d y))|))
 (4 1 (:REWRITE |(* y x)|))
 (3 3 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (2 2 (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (1 1 (:REWRITE MOD-NEGATIVE . 3))
 (1 1 (:REWRITE MOD-NEGATIVE . 2))
 (1 1 (:REWRITE |(* 0 x)|))
 )
(ADE::GCD-ALG-IS-LARGEST-COMMON-DIVISOR-MOD
 (12216 69 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (9660 210 (:LINEAR MOD-BOUNDS-2))
 (9660 210 (:LINEAR MOD-BOUNDS-1))
 (9267 9267 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (9267 9267 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (9267 9267 (:TYPE-PRESCRIPTION NOT-INTEGERP-1B))
 (7225 1298 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5951 69 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (5909 796 (:REWRITE RATIONALP-X))
 (5192 2236 (:TYPE-PRESCRIPTION MOD-POSITIVE . 2))
 (5192 2236 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (4926 92 (:REWRITE MOD-X-Y-=-X . 3))
 (4579 3299 (:REWRITE DEFAULT-TIMES-2))
 (4152 92 (:REWRITE MOD-X-Y-=-X . 4))
 (3575 399 (:REWRITE ACL2-NUMBERP-X))
 (3555 105 (:LINEAR MOD-BOUNDS-3))
 (3488 2598 (:REWRITE DEFAULT-PLUS-1))
 (3430 98 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (3430 98 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (3342 100 (:DEFINITION POSP))
 (3334 98 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (3334 98 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (3194 98 (:REWRITE MOD-ZERO . 4))
 (3032 2598 (:REWRITE DEFAULT-PLUS-2))
 (3001 1095 (:REWRITE DEFAULT-DIVIDE))
 (2236 2236 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (2236 2236 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (2235 2235 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (2217 2217 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (2217 2217 (:TYPE-PRESCRIPTION MOD-NONNEGATIVE))
 (2199 2199 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (2183 69 (:REWRITE MOD-ZERO . 1))
 (1784 64 (:REWRITE |(+ (+ x y) z)|))
 (1641 92 (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (1605 92 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (1543 92 (:REWRITE MOD-X-Y-=-X . 2))
 (1459 997 (:REWRITE |(equal (- x) c)|))
 (1458 1298 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1457 1457 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1332 700 (:REWRITE REDUCE-RATIONALP-+))
 (1314 1298 (:REWRITE DEFAULT-LESS-THAN-2))
 (1314 1298 (:REWRITE DEFAULT-LESS-THAN-1))
 (1314 1182 (:REWRITE INTEGERP-MINUS-X))
 (1308 69 (:REWRITE MOD-ZERO . 2))
 (1298 1298 (:REWRITE THE-FLOOR-BELOW))
 (1298 1298 (:REWRITE THE-FLOOR-ABOVE))
 (1298 1298 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (1298 1298 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (1298 1298 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (1298 1298 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (1298 1298 (:REWRITE INTEGERP-<-CONSTANT))
 (1298 1298 (:REWRITE CONSTANT-<-INTEGERP))
 (1298 1298 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (1298 1298 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (1298 1298 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (1298 1298 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (1298 1298 (:REWRITE |(< c (- x))|))
 (1298 1298 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (1298 1298 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (1298 1298 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (1298 1298 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (1298 1298 (:REWRITE |(< (/ x) (/ y))|))
 (1298 1298 (:REWRITE |(< (- x) c)|))
 (1298 1298 (:REWRITE |(< (- x) (- y))|))
 (1250 200 (:REWRITE |(+ x x)|))
 (1246 990 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (1182 1182 (:REWRITE REDUCE-INTEGERP-+))
 (1182 1182 (:META META-INTEGERP-CORRECT))
 (1073 1073 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (1073 1073 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (1073 1073 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (1013 1007 (:REWRITE |(equal (/ x) (/ y))|))
 (1007 1007 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1007 1007 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1007 1007 (:REWRITE |(equal c (/ x))|))
 (1007 1007 (:REWRITE |(equal (- x) (- y))|))
 (997 997 (:REWRITE |(equal c (- x))|))
 (990 990 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (985 985 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (863 849 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (843 499 (:REWRITE DEFAULT-MINUS))
 (747 731 (:REWRITE RATIONALP-MINUS-X))
 (703 703 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (700 700 (:META META-RATIONALP-CORRECT))
 (577 577 (:REWRITE |(< 0 (/ x))|))
 (577 577 (:REWRITE |(< 0 (* x y))|))
 (550 90 (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (550 90 (:REWRITE MOD-CANCEL-*-CONST))
 (545 89 (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (545 89 (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (518 518 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (518 518 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (486 486 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (474 474 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (446 446 (:REWRITE |(< (/ x) 0)|))
 (446 446 (:REWRITE |(< (* x y) 0)|))
 (444 444 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (444 444 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (424 424 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (393 59 (:REWRITE |(* (if a b c) x)|))
 (365 69 (:REWRITE |(equal (mod (+ x y) z) x)|))
 (356 156 (:REWRITE |(- (* c x))|))
 (323 6 (:REWRITE |(rationalp (- x))|))
 (314 7 (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 1))
 (260 7 (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (231 15 (:REWRITE |(+ x (if a b c))|))
 (218 218 (:REWRITE |(equal (+ (- c) x) y)|))
 (217 217 (:REWRITE |(+ c (+ d x))|))
 (97 97 (:REWRITE |(< y (+ (- c) x))|))
 (97 97 (:REWRITE |(< x (+ c/d y))|))
 (90 90 (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (90 90 (:REWRITE |(mod x (- y))| . 3))
 (90 90 (:REWRITE |(mod x (- y))| . 2))
 (90 90 (:REWRITE |(mod x (- y))| . 1))
 (90 90 (:REWRITE |(mod (- x) y)| . 3))
 (90 90 (:REWRITE |(mod (- x) y)| . 2))
 (89 89 (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (89 89 (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (71 71 (:TYPE-PRESCRIPTION POSP))
 (60 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (60 12 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (60 12 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (60 12 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (60 12 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (59 59 (:REWRITE INTEGERP-/))
 (56 56 (:REWRITE |(< 0 (* x y)) rationalp (* x y)|))
 (56 44 (:REWRITE |(equal x (/ y))|))
 (50 44 (:REWRITE |(not (equal x (/ y)))|))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 2))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (36 12 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (34 34 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (34 34 (:REWRITE |(< (+ c/d x) y)|))
 (34 34 (:REWRITE |(< (+ (- c) x) y)|))
 (22 22 (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (21 21 (:REWRITE FOLD-CONSTS-IN-+))
 (19 19 (:REWRITE |(equal x (if a b c))|))
 (8 4 (:REWRITE |(- (if a b c))|))
 (7 7 (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (7 7 (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 (7 7 (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (7 7 (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (5 5 (:REWRITE |(equal (* x y) 0)|))
 (2 2 (:REWRITE |(+ (if a b c) x)|))
 (1 1 (:REWRITE |(< x (if a b c))|))
 (1 1 (:REWRITE |(< (if a b c) x)|))
 )
(ADE::GCD-ALG-IS-LARGEST-COMMON-DIVISOR-<=
 (5845 5845 (:TYPE-PRESCRIPTION NOT-INTEGERP-3B))
 (5845 5845 (:TYPE-PRESCRIPTION NOT-INTEGERP-2B))
 (3597 733 (:TYPE-PRESCRIPTION MOD-ZERO . 2))
 (3337 97 (:REWRITE CANCEL-MOD-+))
 (3311 109 (:REWRITE MOD-X-Y-=-X-Y . 2))
 (3076 97 (:REWRITE MOD-X-Y-=-X . 3))
 (2921 733 (:TYPE-PRESCRIPTION MOD-ZERO . 1))
 (2318 253 (:REWRITE RATIONALP-X))
 (2061 733 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 2))
 (1954 1362 (:REWRITE DEFAULT-TIMES-2))
 (1947 109 (:REWRITE MOD-X-Y-=-X+Y . 2))
 (1860 29 (:REWRITE MOD-X-Y-=-X-Y . 1))
 (1762 1362 (:REWRITE DEFAULT-TIMES-1))
 (1433 97 (:REWRITE MOD-X-Y-=-X . 4))
 (1142 785 (:REWRITE DEFAULT-PLUS-1))
 (1116 46 (:LINEAR MOD-BOUNDS-2))
 (1045 785 (:REWRITE DEFAULT-PLUS-2))
 (955 109 (:REWRITE MOD-ZERO . 4))
 (941 329 (:REWRITE DEFAULT-MINUS))
 (869 29 (:REWRITE MOD-ZERO . 1))
 (803 171 (:REWRITE REDUCE-RATIONALP-+))
 (741 741 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (734 32 (:REWRITE ZP-OPEN))
 (733 733 (:TYPE-PRESCRIPTION MOD-NONPOSITIVE))
 (733 733 (:TYPE-PRESCRIPTION MOD-NEGATIVE . 1))
 (733 733 (:TYPE-PRESCRIPTION INTEGERP-MOD-2))
 (733 733 (:TYPE-PRESCRIPTION INTEGERP-MOD-1))
 (727 727 (:TYPE-PRESCRIPTION MOD-ZERO . 3))
 (727 727 (:TYPE-PRESCRIPTION MOD-POSITIVE . 1))
 (665 109 (:REWRITE MOD-X-Y-=-X-Y . 3))
 (665 109 (:REWRITE MOD-X-Y-=-X+Y . 3))
 (663 23 (:LINEAR MOD-BOUNDS-3))
 (572 508 (:REWRITE INTEGERP-MINUS-X))
 (524 524 (:REWRITE DEFAULT-DIVIDE))
 (519 519 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (513 97 (:REWRITE MOD-X-Y-=-X . 2))
 (513 97 (:REWRITE MOD-CANCEL-*-REWRITING-GOAL-LITERAL))
 (513 97 (:REWRITE |(mod (+ x (mod a b)) y)|))
 (513 97 (:REWRITE |(mod (+ x (- (mod a b))) y)|))
 (510 508 (:REWRITE REDUCE-INTEGERP-+))
 (508 508 (:META META-INTEGERP-CORRECT))
 (483 444 (:REWRITE DEFAULT-LESS-THAN-1))
 (453 85 (:REWRITE |(mod x (* y (/ z))) rewriting-goal-literal|))
 (453 85 (:REWRITE |(mod (* x (/ y)) z) rewriting-goal-literal|))
 (452 29 (:REWRITE MOD-X-Y-=-X+Y . 1))
 (444 444 (:REWRITE THE-FLOOR-BELOW))
 (444 444 (:REWRITE THE-FLOOR-ABOVE))
 (444 444 (:REWRITE DEFAULT-LESS-THAN-2))
 (441 97 (:REWRITE MOD-CANCEL-*-CONST))
 (436 436 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (436 436 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (436 436 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (432 48 (:REWRITE ACL2-NUMBERP-X))
 (427 427 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (427 427 (:REWRITE INTEGERP-<-CONSTANT))
 (427 427 (:REWRITE CONSTANT-<-INTEGERP))
 (427 427 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (427 427 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (427 427 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (427 427 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (427 427 (:REWRITE |(< c (- x))|))
 (427 427 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (427 427 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (427 427 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (427 427 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (427 427 (:REWRITE |(< (/ x) (/ y))|))
 (427 427 (:REWRITE |(< (- x) c)|))
 (427 427 (:REWRITE |(< (- x) (- y))|))
 (388 165 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (323 6 (:REWRITE |(rationalp (- x))|))
 (298 298 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (298 167 (:REWRITE |(equal (- x) c)|))
 (242 172 (:REWRITE |(equal (/ x) c)|))
 (225 209 (:REWRITE RATIONALP-MINUS-X))
 (223 215 (:REWRITE |(- (* c x))|))
 (221 29 (:REWRITE MOD-ZERO . 2))
 (172 172 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (172 172 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (172 172 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (172 172 (:REWRITE |(equal c (/ x))|))
 (172 172 (:REWRITE |(equal (/ x) (/ y))|))
 (172 172 (:REWRITE |(equal (- x) (- y))|))
 (171 171 (:META META-RATIONALP-CORRECT))
 (167 167 (:REWRITE |(equal c (- x))|))
 (165 165 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (132 132 (:REWRITE DEFAULT-MOD-2))
 (119 119 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (118 8 (:REWRITE |(+ (+ x y) z)|))
 (99 12 (:REWRITE |(<= (/ x) y) with (< x 0)|))
 (99 12 (:REWRITE |(<= (/ x) y) with (< 0 x)|))
 (99 12 (:REWRITE |(< x (/ y)) with (< y 0)|))
 (97 97 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (97 97 (:REWRITE MOD-CANCEL-*-NOT-REWRITING-GOAL-LITERAL))
 (97 97 (:REWRITE |(mod x (- y))| . 3))
 (97 97 (:REWRITE |(mod x (- y))| . 2))
 (97 97 (:REWRITE |(mod x (- y))| . 1))
 (97 97 (:REWRITE |(mod (- x) y)| . 3))
 (97 97 (:REWRITE |(mod (- x) y)| . 2))
 (85 85 (:REWRITE |(mod x (* y (/ z))) not rewriting-goal-literal|))
 (85 85 (:REWRITE |(mod (* x (/ y)) z) not rewriting-goal-literal|))
 (79 79 (:REWRITE |(< (/ x) 0)|))
 (79 79 (:REWRITE |(< (* x y) 0)|))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (76 76 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (72 72 (:REWRITE |(< 0 (* x y))|))
 (71 71 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (71 71 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (67 8 (:REWRITE |(- (+ x y))|))
 (66 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 2))
 (65 65 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (65 2 (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 1))
 (63 63 (:REWRITE |(< 0 (/ x))|))
 (61 29 (:REWRITE |(equal (mod (+ x y) z) x)|))
 (57 57 (:REWRITE |(equal (+ (- c) x) y)|))
 (54 6 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 1))
 (54 6 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 1))
 (54 6 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 1))
 (53 53 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (53 53 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (42 6 (:REWRITE |(+ x x)|))
 (38 38 (:REWRITE INTEGERP-/))
 (32 32 (:REWRITE |(+ c (+ d x))|))
 (30 30 (:REWRITE |(< y (+ (- c) x))|))
 (30 30 (:REWRITE |(< x (+ c/d y))|))
 (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 4))
 (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 3))
 (30 6 (:TYPE-PRESCRIPTION FLOOR-ZERO . 1))
 (30 6 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 3))
 (30 6 (:TYPE-PRESCRIPTION FLOOR-POSITIVE . 2))
 (30 6 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 3))
 (30 6 (:TYPE-PRESCRIPTION FLOOR-NONPOSITIVE . 2))
 (30 6 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 3))
 (30 6 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 3))
 (30 6 (:TYPE-PRESCRIPTION FLOOR-NEGATIVE . 2))
 (29 29 (:REWRITE |(< (+ c/d x) y)|))
 (29 29 (:REWRITE |(< (+ (- c) x) y)|))
 (27 3 (:TYPE-PRESCRIPTION FLOOR-NONNEGATIVE . 1))
 (17 17 (:REWRITE INTEGERP-+-REDUCE-CONSTANT))
 (8 8 (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 3))
 (8 8 (:REWRITE |(mod (+ x y) z) where (<= 0 z)| . 2))
 (7 7 (:REWRITE |(< (* x y) 0) rationalp (* x y)|))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE |(not (equal x (/ y)))|))
 (5 5 (:REWRITE |(equal x (/ y))|))
 (5 5 (:REWRITE |(/ (/ x))|))
 (2 2 (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 3))
 (2 2 (:REWRITE |(mod (+ x y) z) where (<= z 0)| . 2))
 )
