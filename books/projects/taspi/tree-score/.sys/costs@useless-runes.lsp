(RATIONAL-OR-NIL-LISTP)
(RATIONAL-OR-NIL-LIST-LISTP)
(PLUS-NIL-INF)
(MIN-NIL-INF)
(MIN-LIST
 (82 82 (:REWRITE DEFAULT-CAR))
 (62 62 (:REWRITE DEFAULT-CDR))
 (22 22 (:REWRITE SIMPLIFY-SUMS-<))
 (22 22 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (22 22 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (22 22 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (22 22 (:REWRITE DEFAULT-<-2))
 (22 22 (:REWRITE DEFAULT-<-1))
 (22 22 (:REWRITE |(< (- x) (- y))|))
 (5 5 (:TYPE-PRESCRIPTION MIN-NIL-INF))
 )
(SUM-LIST
 (80 80 (:REWRITE DEFAULT-CAR))
 (62 62 (:REWRITE DEFAULT-CDR))
 (22 22 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (22 22 (:REWRITE NORMALIZE-ADDENDS))
 (22 22 (:REWRITE DEFAULT-+-2))
 (22 22 (:REWRITE DEFAULT-+-1))
 )
(RATIONALP-MIN-LIST
 (38 38 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 )
(SUM-MINIMA)
(RATIONALP-SUM-MINIMA
 (105 105 (:REWRITE DEFAULT-CAR))
 (94 94 (:REWRITE DEFAULT-CDR))
 (27 27 (:REWRITE SIMPLIFY-SUMS-<))
 (27 27 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (27 27 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (27 27 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (27 27 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (27 27 (:REWRITE DEFAULT-<-2))
 (27 27 (:REWRITE DEFAULT-<-1))
 (27 27 (:REWRITE |(< (- x) (- y))|))
 (20 20 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:REWRITE NORMALIZE-ADDENDS))
 (20 20 (:REWRITE DEFAULT-+-2))
 (20 20 (:REWRITE DEFAULT-+-1))
 )
(SUM-MINIMA
 (96 8 (:DEFINITION MIN-LIST))
 (72 8 (:DEFINITION MIN-NIL-INF))
 (47 47 (:REWRITE DEFAULT-CAR))
 (44 44 (:REWRITE DEFAULT-CDR))
 (42 2 (:DEFINITION SUM-MINIMA))
 (12 2 (:DEFINITION PLUS-NIL-INF))
 (8 8 (:REWRITE SIMPLIFY-SUMS-<))
 (8 8 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (8 8 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE |(< (- x) (- y))|))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(SEQUENCE-SCORELISTP)
(CHAR-SCORELISTP-RATIONAL-OR-NIL-LIST-LISTP
 (98 14 (:DEFINITION LEN))
 (53 53 (:REWRITE DEFAULT-CAR))
 (50 50 (:REWRITE DEFAULT-CDR))
 (28 14 (:REWRITE DEFAULT-+-2))
 (14 14 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (14 14 (:REWRITE NORMALIZE-ADDENDS))
 (14 14 (:REWRITE DEFAULT-+-1))
 (12 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (12 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (12 5 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 )
(RATIONAL-OR-NIL-LISTP-MAKE-LIST-AC
 (60 42 (:REWRITE DEFAULT-CDR))
 (60 42 (:REWRITE DEFAULT-CAR))
 (22 10 (:REWRITE ZP-OPEN))
 (10 10 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (10 10 (:REWRITE NORMALIZE-ADDENDS))
 (10 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (9 1 (:REWRITE |(< d (+ c x))|))
 (5 1 (:REWRITE |(+ c (+ d x))|))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (1 1 (:REWRITE SIMPLIFY-SUMS-<))
 (1 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (1 1 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE |(< (- x) (- y))|))
 )
(RATIONAL-OR-NIL-LISTP-CONST-LIST-ACC
 (12 2 (:DEFINITION MAKE-LIST-AC))
 (5 1 (:DEFINITION RATIONAL-OR-NIL-LISTP))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(RATIONAL-OR-NIL-LISTP-NIL-LIST)
(LEN-CONST-LIST-ACC
 (36 19 (:REWRITE DEFAULT-+-2))
 (19 19 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (19 19 (:REWRITE NORMALIZE-ADDENDS))
 (19 19 (:REWRITE DEFAULT-+-1))
 (17 11 (:REWRITE DEFAULT-CDR))
 (9 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 3 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ c x) d)|))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE |(< (- x) 0)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(LEN-NIL-LIST
 (11 1 (:DEFINITION LEN))
 (6 1 (:DEFINITION MAKE-LIST-AC))
 (3 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MAKE-LIST-AC))
 (2 2 (:TYPE-PRESCRIPTION MAKE-LIST-AC))
 (2 2 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (2 2 (:REWRITE NORMALIZE-ADDENDS))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(LEN-MAKE-LIST-AC
 (36 19 (:REWRITE DEFAULT-+-2))
 (19 19 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (19 19 (:REWRITE NORMALIZE-ADDENDS))
 (19 19 (:REWRITE DEFAULT-+-1))
 (17 11 (:REWRITE DEFAULT-CDR))
 (9 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 3 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE |(equal (+ c x) d)|))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE |(< (- x) 0)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(ZERO-SCORES)
(ZERO-SCORES-LEN
 (14 7 (:REWRITE DEFAULT-+-2))
 (9 8 (:REWRITE DEFAULT-CDR))
 (9 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (9 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (9 3 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (7 7 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (7 7 (:REWRITE NORMALIZE-ADDENDS))
 (7 7 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 )
(ZERO-SCORES-RATIONAL-OR-NIL-LISP
 (10 9 (:REWRITE DEFAULT-CDR))
 (10 8 (:REWRITE DEFAULT-CAR))
 )
(CHARSTATE-SCORELIST-MAP-P)
(ASSOC-HQUAL-STATE-SCORELIST-MAP
 (330 6 (:REWRITE VALID-SEQUENCES-SAME-LENGTH-ASSOC-HQUAL))
 (318 6 (:DEFINITION VALID-SEQUENCES-SAME-LENGTH))
 (237 237 (:REWRITE DEFAULT-CAR))
 (178 166 (:REWRITE DEFAULT-CDR))
 (162 6 (:DEFINITION VALID-SEQUENCES-LENGTH-N))
 (154 40 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (114 114 (:TYPE-PRESCRIPTION STRIP-CARS-GEN))
 (114 114 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (84 12 (:DEFINITION VALID-SEQ))
 (81 19 (:REWRITE MEMBER-STRIP-CARS-GOOD-TAXON-BDD-ASSOC))
 (72 18 (:REWRITE MEMBER-TAXA-ASSOC-HQUAL))
 (58 29 (:REWRITE DEFAULT-+-2))
 (57 57 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (48 48 (:TYPE-PRESCRIPTION VALID-SEQ))
 (48 24 (:TYPE-PRESCRIPTION INTEGER-ASSOC-HQUAL-INTEGER-HALISTP))
 (48 12 (:REWRITE ATOM-CDR-ASSOC-GOOD-TAXON-LIST))
 (42 27 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (42 27 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (42 27 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (40 40 (:REWRITE SUBSET-SAME-MEMBERS))
 (40 40 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (40 40 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (39 39 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (39 39 (:REWRITE NOT-MEMBER-SUBSET))
 (37 37 (:TYPE-PRESCRIPTION GOOD-TAXON-BDD-ALIST))
 (29 29 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (29 29 (:REWRITE NORMALIZE-ADDENDS))
 (29 29 (:REWRITE DEFAULT-+-1))
 (27 27 (:REWRITE |(equal (- x) (- y))|))
 (24 24 (:TYPE-PRESCRIPTION VALID-SEQUENCES-LENGTH-N))
 (24 24 (:TYPE-PRESCRIPTION INTEGER-HALISTP))
 (24 24 (:TYPE-PRESCRIPTION GOOD-INDEX-TAXON-HALIST))
 (19 19 (:REWRITE GOOD-TAXON-BDD-ALIST-WHEN-NOT-CONSP))
 (18 18 (:REWRITE MEMBER-GIVES-ASSOC-HQUAL))
 (12 12 (:REWRITE GOOD-INDEX-TAXON-HALIST-WHEN-NOT-CONSP))
 (12 12 (:DEFINITION VALID-TAXON))
 (6 6 (:TYPE-PRESCRIPTION VALID-SEQUENCES-SAME-LENGTH))
 (6 6 (:REWRITE ASSOC-HQUAL-VALID-SEQUENCES-LENGTH-N))
 (4 1 (:REWRITE ASSOC-CAR-FROM-SUBSET))
 )
(MAKE-LEAF-SCORE-LIST
 (46 1 (:DEFINITION HONS-ASSOC-EQUAL))
 (39 3 (:REWRITE NOT-MEMBER-NOT-CONSP-ASSOC))
 (30 30 (:REWRITE DEFAULT-CAR))
 (25 25 (:REWRITE DEFAULT-CDR))
 (21 3 (:DEFINITION LEN))
 (15 3 (:DEFINITION RATIONAL-OR-NIL-LISTP))
 (12 3 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (12 3 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (9 9 (:TYPE-PRESCRIPTION STRIP-CARS-GEN))
 (7 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 4 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION MEMBER-GEN))
 (6 6 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (6 3 (:REWRITE DEFAULT-+-2))
 (5 1 (:DEFINITION HONS-EQUAL))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE SUBSET-SAME-MEMBERS))
 (3 3 (:REWRITE STRIP-CARS-GEN-WHEN-NOT-CONSP))
 (3 3 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (3 3 (:REWRITE NOT-MEMBER-SUBSET))
 (3 3 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (3 3 (:REWRITE NORMALIZE-ADDENDS))
 (3 3 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (3 3 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (3 3 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (2 2 (:REWRITE SIMPLIFY-SUMS-<))
 (2 2 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (2 2 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (2 2 (:REWRITE REDUCE-INTEGERP-+))
 (2 2 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (2 2 (:REWRITE INTEGERP-MINUS-X))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE |(< (- x) 0)|))
 (2 2 (:REWRITE |(< (- x) (- y))|))
 (2 2 (:META META-INTEGERP-CORRECT))
 )
(SEQUENCE-SCORELISTP-MAKE-LEAF-SCORE-LIST
 (512 10 (:DEFINITION HONS-ASSOC-EQUAL))
 (390 30 (:REWRITE NOT-MEMBER-NOT-CONSP-ASSOC))
 (192 6 (:DEFINITION CHARSTATE-SCORELIST-MAP-P))
 (130 120 (:REWRITE DEFAULT-CAR))
 (120 30 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (120 30 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (111 106 (:REWRITE DEFAULT-CDR))
 (90 90 (:TYPE-PRESCRIPTION STRIP-CARS-GEN))
 (90 12 (:DEFINITION LEN))
 (84 84 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (72 72 (:TYPE-PRESCRIPTION LEN))
 (66 12 (:DEFINITION RATIONAL-OR-NIL-LISTP))
 (60 60 (:TYPE-PRESCRIPTION MEMBER-GEN))
 (50 10 (:DEFINITION HONS-EQUAL))
 (48 8 (:DEFINITION MAKE-LIST-AC))
 (42 42 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (34 22 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (34 22 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (34 22 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (32 20 (:REWRITE DEFAULT-+-2))
 (30 30 (:REWRITE SUBSET-SAME-MEMBERS))
 (30 30 (:REWRITE STRIP-CARS-GEN-WHEN-NOT-CONSP))
 (30 30 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (30 30 (:REWRITE NOT-MEMBER-SUBSET))
 (30 30 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (30 30 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (24 6 (:REWRITE MEMBER-TAXA-ASSOC-HQUAL))
 (24 6 (:REWRITE MEMBER-STRIP-CARS-GOOD-TAXON-BDD-ASSOC))
 (24 6 (:REWRITE ASSOC-CAR-FROM-SUBSET))
 (22 22 (:REWRITE |(equal (- x) (- y))|))
 (20 20 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (20 20 (:REWRITE NORMALIZE-ADDENDS))
 (20 20 (:REWRITE DEFAULT-+-1))
 (12 12 (:TYPE-PRESCRIPTION GOOD-TAXON-BDD-ALIST))
 (8 8 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (6 6 (:REWRITE SIMPLIFY-SUMS-<))
 (6 6 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (6 6 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (6 6 (:REWRITE REDUCE-INTEGERP-+))
 (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (6 6 (:REWRITE MEMBER-GIVES-ASSOC-HQUAL))
 (6 6 (:REWRITE INTEGERP-MINUS-X))
 (6 6 (:REWRITE GOOD-TAXON-BDD-ALIST-WHEN-NOT-CONSP))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE |(< (- x) 0)|))
 (6 6 (:REWRITE |(< (- x) (- y))|))
 (6 6 (:META META-INTEGERP-CORRECT))
 (6 6 (:DEFINITION VALID-CHAR))
 )
(LEN-MAKE-LEAF-SCORE-LIST
 (512 10 (:DEFINITION HONS-ASSOC-EQUAL))
 (390 30 (:REWRITE NOT-MEMBER-NOT-CONSP-ASSOC))
 (120 30 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (120 30 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (90 90 (:TYPE-PRESCRIPTION STRIP-CARS-GEN))
 (84 84 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (71 66 (:REWRITE DEFAULT-CDR))
 (60 60 (:TYPE-PRESCRIPTION MEMBER-GEN))
 (50 50 (:REWRITE DEFAULT-CAR))
 (50 29 (:REWRITE DEFAULT-+-2))
 (50 10 (:DEFINITION HONS-EQUAL))
 (48 8 (:DEFINITION MAKE-LIST-AC))
 (42 42 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (30 30 (:REWRITE SUBSET-SAME-MEMBERS))
 (30 30 (:REWRITE STRIP-CARS-GEN-WHEN-NOT-CONSP))
 (30 30 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (30 30 (:REWRITE NOT-MEMBER-SUBSET))
 (30 30 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (30 30 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (29 29 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (29 29 (:REWRITE NORMALIZE-ADDENDS))
 (29 29 (:REWRITE DEFAULT-+-1))
 (28 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (28 16 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (28 16 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (24 6 (:REWRITE MEMBER-TAXA-ASSOC-HQUAL))
 (24 6 (:REWRITE MEMBER-STRIP-CARS-GOOD-TAXON-BDD-ASSOC))
 (24 6 (:REWRITE ASSOC-CAR-FROM-SUBSET))
 (16 16 (:REWRITE |(equal (- x) (- y))|))
 (12 12 (:TYPE-PRESCRIPTION GOOD-TAXON-BDD-ALIST))
 (8 8 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE MEMBER-GIVES-ASSOC-HQUAL))
 (6 6 (:REWRITE GOOD-TAXON-BDD-ALIST-WHEN-NOT-CONSP))
 (2 1 (:REWRITE |(equal (+ c x) d)|))
 )
(COST-ROWP)
(COST-MATRIXP)
(COST-MATRIXP-NSTATES)
(COST-MATRIXP-NSTATES-COST-MATRIXP
 (66 66 (:REWRITE DEFAULT-CAR))
 (45 45 (:REWRITE DEFAULT-CDR))
 (28 4 (:DEFINITION LEN))
 (8 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8 4 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (8 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (4 4 (:REWRITE NORMALIZE-ADDENDS))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 )
(COST-MATRIX-HET
 (90 90 (:REWRITE DEFAULT-CAR))
 (68 17 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (55 49 (:REWRITE DEFAULT-CDR))
 (54 54 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (51 51 (:TYPE-PRESCRIPTION STRIP-CARS-GEN))
 (45 10 (:REWRITE MEMBER-STRIP-CARS-GOOD-TAXON-BDD-ASSOC))
 (36 9 (:REWRITE MEMBER-TAXA-ASSOC-HQUAL))
 (27 27 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (20 10 (:TYPE-PRESCRIPTION INTEGER-ASSOC-HQUAL-INTEGER-HALISTP))
 (20 5 (:REWRITE ATOM-CDR-ASSOC-GOOD-TAXON-LIST))
 (19 19 (:TYPE-PRESCRIPTION GOOD-TAXON-BDD-ALIST))
 (19 19 (:REWRITE SUBSET-SAME-MEMBERS))
 (19 19 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (19 19 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (18 18 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (18 18 (:REWRITE NOT-MEMBER-SUBSET))
 (12 12 (:REWRITE COST-MATRIXP-NSTATES-COST-MATRIXP))
 (10 10 (:TYPE-PRESCRIPTION INTEGER-HALISTP))
 (10 10 (:TYPE-PRESCRIPTION GOOD-INDEX-TAXON-HALIST))
 (10 10 (:REWRITE GOOD-TAXON-BDD-ALIST-WHEN-NOT-CONSP))
 (9 9 (:REWRITE MEMBER-GIVES-ASSOC-HQUAL))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 (5 5 (:REWRITE GOOD-INDEX-TAXON-HALIST-WHEN-NOT-CONSP))
 (5 5 (:REWRITE ASSOC-HQUAL-STATE-SCORELIST-MAP))
 (4 1 (:REWRITE ASSOC-CAR-FROM-SUBSET))
 )
(MAKE-DEFAULT-COSTLIST)
(MAKE-DEFAULT-CMAT)
(MAKE-DEFAULT-COST-MATRIX)
