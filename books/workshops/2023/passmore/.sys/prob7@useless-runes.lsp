(SQUARE
 (5 5 (:TYPE-PRESCRIPTION NONNEGATIVE-PRODUCT))
 )
(SQUARE-PSD
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(SQUARE-TYPE
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(PROB-0
 (21 21 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 )
(GOAL)
(CONE-CF-0
 (154 154 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (154 154 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (70 70 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 )
(CONE-CF-0-TYPE
 (2657 42 (:REWRITE DEFAULT-PLUS-2))
 (1143 42 (:REWRITE DEFAULT-PLUS-1))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (319 319 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (305 27 (:REWRITE DEFAULT-TIMES-2))
 (170 170 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (170 170 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (170 170 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (82 27 (:REWRITE DEFAULT-TIMES-1))
 (36 3 (:REWRITE DEFAULT-MINUS))
 (25 25 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (25 25 (:REWRITE NORMALIZE-ADDENDS))
 (19 19 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (15 15 (:REWRITE DEFAULT-EXPT-2))
 (15 15 (:REWRITE DEFAULT-EXPT-1))
 (15 15 (:REWRITE |(expt 1/c n)|))
 (15 15 (:REWRITE |(expt (- x) n)|))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (13 13 (:REWRITE |(+ c (+ d x))|))
 (12 3 (:REWRITE RATIONALP-X))
 (9 9 (:REWRITE |(* (- x) y)|))
 (4 4 (:REWRITE |(* c (* d x))|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE |(- (* c x))|))
 )
(CONE-CF-0-PSD
 (3482 64 (:REWRITE DEFAULT-PLUS-2))
 (1496 64 (:REWRITE DEFAULT-PLUS-1))
 (885 885 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (885 885 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (885 885 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (885 885 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (885 885 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (885 885 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (885 885 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (885 885 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (885 885 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (885 885 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (617 42 (:REWRITE DEFAULT-TIMES-2))
 (546 18 (:REWRITE DEFAULT-MINUS))
 (342 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (310 4 (:REWRITE DEFAULT-LESS-THAN-1))
 (277 277 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (277 277 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (277 277 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (122 42 (:REWRITE DEFAULT-TIMES-1))
 (103 4 (:REWRITE DEFAULT-LESS-THAN-2))
 (68 2 (:REWRITE SIMPLIFY-SUMS-<))
 (37 4 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (36 36 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (26 26 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (21 21 (:REWRITE DEFAULT-EXPT-2))
 (21 21 (:REWRITE DEFAULT-EXPT-1))
 (21 21 (:REWRITE |(expt 1/c n)|))
 (21 21 (:REWRITE |(expt (- x) n)|))
 (20 20 (:REWRITE FOLD-CONSTS-IN-+))
 (20 20 (:REWRITE |(+ c (+ d x))|))
 (12 12 (:REWRITE |(* c (* d x))|))
 (12 3 (:REWRITE RATIONALP-X))
 (11 11 (:REWRITE |(* (- x) y)|))
 (4 4 (:REWRITE THE-FLOOR-BELOW))
 (4 4 (:REWRITE THE-FLOOR-ABOVE))
 (4 4 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (4 4 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (4 4 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (4 4 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (4 4 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (4 4 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (4 4 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (4 4 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (4 4 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (4 4 (:REWRITE |(< (/ x) (/ y))|))
 (4 4 (:REWRITE |(< (- x) (- y))|))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-<-CONSTANT))
 (3 3 (:REWRITE CONSTANT-<-INTEGERP))
 (3 3 (:REWRITE |(< (- x) c)|))
 (3 3 (:REWRITE |(< (+ c/d x) y)|))
 (3 3 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 )
(MONOID-CF-0
 (21 21 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP-BASE))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (21 21 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 )
(CERT)
(CERT-KEY
 (147582 1676 (:REWRITE DEFAULT-PLUS-2))
 (49399 1676 (:REWRITE DEFAULT-PLUS-1))
 (20136 20136 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (20136 20136 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (20136 20136 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (20136 20136 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (20136 20136 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (20136 20136 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (11152 11152 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (8248 390 (:REWRITE DEFAULT-TIMES-2))
 (2873 146 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (2729 2729 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2729 2729 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2729 2729 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2166 390 (:REWRITE DEFAULT-TIMES-1))
 (1494 59 (:REWRITE DEFAULT-MINUS))
 (932 107 (:REWRITE DEFAULT-EXPT-1))
 (671 671 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (615 615 (:REWRITE |(+ c (+ d x))|))
 (547 547 (:REWRITE FOLD-CONSTS-IN-+))
 (471 15 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (471 15 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (107 107 (:REWRITE DEFAULT-EXPT-2))
 (67 67 (:REWRITE |(expt 1/c n)|))
 (18 18 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (18 18 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (18 18 (:REWRITE |(equal c (/ x))|))
 (18 18 (:REWRITE |(equal c (- x))|))
 (18 18 (:REWRITE |(equal (/ x) c)|))
 (18 18 (:REWRITE |(equal (/ x) (/ y))|))
 (18 18 (:REWRITE |(equal (- x) c)|))
 (18 18 (:REWRITE |(equal (- x) (- y))|))
 (15 15 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (15 15 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (12 3 (:REWRITE RATIONALP-X))
 (8 8 (:REWRITE |(* c (expt d n))|))
 (7 7 (:REWRITE |(equal (+ (- c) x) y)|))
 (6 6 (:REWRITE |(expt (- c) n)|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 )
(CERT-CONTRA-M-0
 (1650 44 (:REWRITE DEFAULT-PLUS-2))
 (1020 30 (:REWRITE DEFAULT-MINUS))
 (706 44 (:REWRITE DEFAULT-PLUS-1))
 (624 30 (:REWRITE DEFAULT-TIMES-2))
 (548 548 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (548 548 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (548 548 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (548 548 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (548 548 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (548 548 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (548 548 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (548 548 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (548 548 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (548 548 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (268 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (204 6 (:REWRITE DEFAULT-LESS-THAN-2))
 (204 6 (:REWRITE DEFAULT-LESS-THAN-1))
 (134 2 (:REWRITE SIMPLIFY-SUMS-<))
 (80 30 (:REWRITE DEFAULT-TIMES-1))
 (74 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (22 22 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (16 16 (:REWRITE |(* c (* d x))|))
 (14 14 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (14 14 (:REWRITE |(+ c (+ d x))|))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (12 3 (:REWRITE RATIONALP-X))
 (6 6 (:REWRITE THE-FLOOR-BELOW))
 (6 6 (:REWRITE THE-FLOOR-ABOVE))
 (6 6 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (6 6 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (6 6 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (6 6 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (6 6 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (6 6 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (6 6 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (6 6 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (6 6 (:REWRITE |(< (/ x) (/ y))|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (4 4 (:REWRITE |(* (- x) y)|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE |(< y (+ (- c) x))|))
 (2 2 (:REWRITE |(< x (+ c/d y))|))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 )
(CERT-CONTRA-C-0)
(CERT-CONTRA
 (14 8 (:REWRITE DEFAULT-PLUS-2))
 (14 8 (:REWRITE DEFAULT-PLUS-1))
 (12 3 (:REWRITE RATIONALP-X))
 (6 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 3 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (5 3 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (5 3 (:REWRITE DEFAULT-LESS-THAN-1))
 (4 3 (:REWRITE DEFAULT-LESS-THAN-2))
 (3 3 (:REWRITE THE-FLOOR-BELOW))
 (3 3 (:REWRITE THE-FLOOR-ABOVE))
 (3 3 (:REWRITE SIMPLIFY-SUMS-<))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (3 3 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-<-CONSTANT))
 (3 3 (:REWRITE CONSTANT-<-INTEGERP))
 (3 3 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (3 3 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (3 3 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (3 3 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (3 3 (:REWRITE |(< c (- x))|))
 (3 3 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (3 3 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (3 3 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (3 3 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (3 3 (:REWRITE |(< (/ x) (/ y))|))
 (3 3 (:REWRITE |(< (- x) c)|))
 (3 3 (:REWRITE |(< (- x) (- y))|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-REMAINDER))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-AX+BX-RATIONAL-COMMON))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE |(< 0 (/ x))|))
 (2 2 (:REWRITE |(< 0 (* x y))|))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-REMAINDER))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-<-0-RATIONAL-COMMON))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< (/ x) 0)|))
 (1 1 (:REWRITE |(< (+ c/d x) y)|))
 (1 1 (:REWRITE |(< (+ (- c) x) y)|))
 (1 1 (:REWRITE |(< (* x y) 0)|))
 )
(MAIN
 (21 12 (:REWRITE DEFAULT-PLUS-2))
 (21 12 (:REWRITE DEFAULT-PLUS-1))
 (3 3 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (3 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 1 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-AX+BX-=-0))
 (1 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (1 1 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE REDUCE-ADDITIVE-CONSTANT-EQUAL))
 (1 1 (:REWRITE EQUAL-OF-PREDICATES-REWRITE))
 (1 1 (:REWRITE |(equal c (/ x))|))
 (1 1 (:REWRITE |(equal c (- x))|))
 (1 1 (:REWRITE |(equal (/ x) c)|))
 (1 1 (:REWRITE |(equal (/ x) (/ y))|))
 (1 1 (:REWRITE |(equal (- x) c)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(equal (+ (- c) x) y)|))
 )
(FINAL
 (1313 37 (:REWRITE DEFAULT-PLUS-2))
 (633 37 (:REWRITE DEFAULT-PLUS-1))
 (605 605 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE))
 (605 605 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-ODD-EXPONENT))
 (605 605 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONPOSITIVE-BASE-EVEN-EXPONENT))
 (605 605 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE))
 (605 605 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-0-BASE))
 (605 605 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT))
 (605 605 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT))
 (605 605 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-B))
 (605 605 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE-A))
 (605 605 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE))
 (556 28 (:REWRITE DEFAULT-TIMES-2))
 (544 16 (:REWRITE DEFAULT-MINUS))
 (268 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (203 5 (:REWRITE DEFAULT-LESS-THAN-1))
 (137 5 (:REWRITE DEFAULT-LESS-THAN-2))
 (134 2 (:REWRITE SIMPLIFY-SUMS-<))
 (87 87 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (78 28 (:REWRITE DEFAULT-TIMES-1))
 (74 8 (:TYPE-PRESCRIPTION BUBBLE-DOWN))
 (16 16 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 14 (:REWRITE |(* c (* d x))|))
 (12 12 (:REWRITE DEFAULT-EXPT-2))
 (12 12 (:REWRITE DEFAULT-EXPT-1))
 (12 12 (:REWRITE |(expt 1/c n)|))
 (12 12 (:REWRITE |(expt (- x) n)|))
 (12 3 (:REWRITE RATIONALP-X))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE |(+ c (+ d x))|))
 (5 5 (:REWRITE THE-FLOOR-BELOW))
 (5 5 (:REWRITE THE-FLOOR-ABOVE))
 (5 5 (:REWRITE REDUCE-RATIONAL-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE REDUCE-MULTIPLICATIVE-CONSTANT-<))
 (5 5 (:REWRITE REDUCE-ADDITIVE-CONSTANT-<))
 (5 5 (:REWRITE |(< c (/ x)) positive c --- present in goal|))
 (5 5 (:REWRITE |(< c (/ x)) positive c --- obj t or nil|))
 (5 5 (:REWRITE |(< c (/ x)) negative c --- present in goal|))
 (5 5 (:REWRITE |(< c (/ x)) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< (/ x) c) positive c --- present in goal|))
 (5 5 (:REWRITE |(< (/ x) c) positive c --- obj t or nil|))
 (5 5 (:REWRITE |(< (/ x) c) negative c --- present in goal|))
 (5 5 (:REWRITE |(< (/ x) c) negative c --- obj t or nil|))
 (5 5 (:REWRITE |(< (/ x) (/ y))|))
 (5 5 (:REWRITE |(< (- x) (- y))|))
 (4 4 (:REWRITE REMOVE-WEAK-INEQUALITIES))
 (4 4 (:REWRITE REMOVE-STRICT-INEQUALITIES))
 (4 4 (:REWRITE INTEGERP-<-CONSTANT))
 (4 4 (:REWRITE CONSTANT-<-INTEGERP))
 (4 4 (:REWRITE |(< (- x) c)|))
 (4 4 (:REWRITE |(< (+ c/d x) y)|))
 (4 4 (:REWRITE |(< (+ (- c) x) y)|))
 (3 3 (:REWRITE REDUCE-RATIONALP-+))
 (3 3 (:REWRITE REDUCE-RATIONALP-*))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE RATIONALP-MINUS-X))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:REWRITE |(* (- x) y)|))
 (3 3 (:META META-RATIONALP-CORRECT))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE |(< (/ x) 0)|))
 (2 2 (:REWRITE |(< (* x y) 0)|))
 (1 1 (:REWRITE |(< y (+ (- c) x))|))
 (1 1 (:REWRITE |(< x (+ c/d y))|))
 (1 1 (:REWRITE |(< 0 (/ x))|))
 (1 1 (:REWRITE |(< 0 (* x y))|))
 )
