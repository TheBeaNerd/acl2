(TREE-LIST-DOMAIN-ALISTP
 (138 7 (:REWRITE INTEGER-HALISTP-HALISTP))
 (122 9 (:DEFINITION INTEGER-HALISTP))
 (37 37 (:REWRITE DEFAULT-CAR))
 (36 8 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (28 7 (:REWRITE GOOD-TAXON-INTEGER-LISTP-ALISTP-GEN))
 (28 4 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (27 27 (:TYPE-PRESCRIPTION INTEGER-HALISTP))
 (20 20 (:REWRITE DEFAULT-CDR))
 (14 14 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (12 12 (:REWRITE REDUCE-INTEGERP-+))
 (12 12 (:REWRITE INTEGERP-MINUS-X))
 (12 12 (:META META-INTEGERP-CORRECT))
 (8 8 (:TYPE-PRESCRIPTION TIP-P))
 (8 2 (:REWRITE TREE-LIST-LISTP-TREE-LISTP))
 (7 7 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (7 7 (:REWRITE ALISTP-GEN-OF-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION NON-TIP-TREE-LISTP))
 (2 2 (:REWRITE TREE-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE NON-TIP-TREE-LISTP-WHEN-NOT-CONSP))
 )
(TREE-LIST-DOMAIN-ALISTP-WHEN-NOT-CONSP)
(TREE-LIST-DOMAIN-ALISTP-OF-CONSP
 (24 24 (:REWRITE DEFAULT-CAR))
 (20 5 (:REWRITE TREE-LIST-LISTP-TREE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION NON-TIP-TREE-LISTP))
 (8 8 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE TREE-LIST-DOMAIN-ALISTP-WHEN-NOT-CONSP))
 (5 5 (:REWRITE TREE-LISTP-WHEN-NOT-CONSP))
 (5 5 (:REWRITE NON-TIP-TREE-LISTP-WHEN-NOT-CONSP))
 )
(MEMBER-GIVES-ASSOC-HQUAL
 (246 42 (:REWRITE SUBSET-SAME-MEMBERS))
 (117 45 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (108 27 (:REWRITE PERM-WHEN-NOT-CONSP))
 (90 6 (:REWRITE PERM-OF-CONSP))
 (84 21 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (84 21 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (72 6 (:REWRITE SUBSET-OF-CONSP))
 (62 62 (:REWRITE GET-TAXA-FROM-TAXON-INDEX-WHEN-NOT-CONSP))
 (54 54 (:TYPE-PRESCRIPTION PERM))
 (48 12 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (42 42 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (42 42 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (24 6 (:REWRITE DEL-WHEN-NOT-CONSP))
 (21 21 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (20 20 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE SUBSET-TRANSITIVE))
 (18 18 (:REWRITE SUBSET-APPEND-GIVES-2))
 (18 18 (:REWRITE SUBSET-APPEND-GIVES-1))
 (10 10 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (10 10 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (10 10 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (10 10 (:REWRITE |(equal (- x) (- y))|))
 )
(NOT-CONSP-TASPI-T-GIVES-ASSOC-EQUAL-FIRST
 (46 4 (:REWRITE PERM-IMPLIES-SUBSET))
 (24 2 (:REWRITE PERM-OF-CONSP))
 (18 18 (:TYPE-PRESCRIPTION GET-TAXA-FROM-TAXON-INDEX))
 (15 3 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (14 4 (:REWRITE PERM-WHEN-NOT-CONSP))
 (13 2 (:REWRITE TIP-P-GIVES-TASPIP-T))
 (11 3 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (10 4 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (8 2 (:REWRITE DEL-WHEN-NOT-CONSP))
 (6 6 (:TYPE-PRESCRIPTION TIP-P))
 (6 6 (:REWRITE SUBSET-SAME-MEMBERS))
 (6 6 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (6 6 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (6 6 (:REWRITE GET-TAXA-FROM-TAXON-INDEX-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION PERM))
 (4 4 (:REWRITE TASPIP-FLG-CONSP-GIVES-TASPIP-NIL))
 (4 4 (:REWRITE SUBSET-TRANSITIVE))
 (4 4 (:REWRITE SUBSET-APPEND-GIVES-2))
 (4 4 (:REWRITE SUBSET-APPEND-GIVES-1))
 (4 4 (:REWRITE NOT-MEMBER-SUBSET))
 (4 4 (:REWRITE NOT-INTERSECT-TOPS-NOT-SUBSET))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE TASPIP-FLG-AND-FLG-GIVES-T))
 )
(SUBSET-TIPS-ASSOC-HQUAL-FIRST-TAXON
 (1350 30 (:DEFINITION HONS-ASSOC-EQUAL))
 (675 90 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (450 30 (:DEFINITION HONS-EQUAL))
 (245 23 (:REWRITE PERM-IMPLIES-SUBSET))
 (235 87 (:REWRITE TASPIP-NIL-AND-CONSP-GIVES-TASPIP-FLG))
 (193 47 (:REWRITE TIP-P-GIVES-TASPIP-T))
 (137 137 (:REWRITE DEFAULT-CAR))
 (136 136 (:TYPE-PRESCRIPTION MYTIPS))
 (120 30 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (120 30 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (120 30 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (101 23 (:REWRITE PERM-WHEN-NOT-CONSP))
 (96 96 (:TYPE-PRESCRIPTION TIP-P))
 (85 19 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (75 75 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (64 64 (:REWRITE DEFAULT-CDR))
 (60 48 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (47 47 (:REWRITE TASPIP-FLG-AND-FLG-GIVES-T))
 (46 46 (:TYPE-PRESCRIPTION PERM))
 (43 43 (:REWRITE GET-TAXA-FROM-TAXON-INDEX-WHEN-NOT-CONSP))
 (30 30 (:REWRITE |(equal (- x) (- y))|))
 (30 2 (:REWRITE PERM-OF-CONSP))
 (24 24 (:REWRITE TASPIP-FLG-CONSP-GIVES-TASPIP-NIL))
 (23 23 (:REWRITE SUBSET-TRANSITIVE))
 (23 23 (:REWRITE SUBSET-APPEND-GIVES-2))
 (21 21 (:REWRITE NOT-INTERSECT-TOPS-NOT-SUBSET))
 (19 1 (:REWRITE SUBSET-SUBSET-GIVES-SUBSET-APPEND))
 (18 6 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (12 12 (:TYPE-PRESCRIPTION GET-TAXA-FROM-TAXON-INDEX))
 (11 3 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (8 2 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (8 2 (:REWRITE DEL-WHEN-NOT-CONSP))
 (6 6 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (4 4 (:REWRITE SUBSET-SAME-MEMBERS))
 (4 4 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (4 4 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE NOT-MEMBER-SUBSET))
 )
(CONSP-SUBSET-MEMBER-FIRST-TAXON
 (485 145 (:REWRITE TASPIP-NIL-AND-CONSP-GIVES-TASPIP-FLG))
 (290 69 (:REWRITE PERM-WHEN-NOT-CONSP))
 (140 140 (:TYPE-PRESCRIPTION PERM))
 (135 135 (:REWRITE TASPIP-FLG-CONSP-GIVES-TASPIP-NIL))
 (85 15 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (75 30 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (73 73 (:REWRITE SUBSET-TRANSITIVE))
 (72 72 (:REWRITE SUBSET-SAME-MEMBERS))
 (72 72 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (70 10 (:REWRITE TIP-P-GIVES-TASPIP-T))
 (69 69 (:REWRITE NOT-INTERSECT-TOPS-NOT-SUBSET))
 (66 66 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (58 4 (:REWRITE SUBSET-SUBSET-GIVES-SUBSET-APPEND))
 (48 24 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (41 6 (:REWRITE PERM-OF-CONSP))
 (40 40 (:TYPE-PRESCRIPTION TIP-P))
 (39 39 (:REWRITE DEFAULT-CDR))
 (39 39 (:REWRITE DEFAULT-CAR))
 (24 24 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (15 15 (:REWRITE REDUCE-INTEGERP-+))
 (15 15 (:REWRITE INTEGERP-MINUS-X))
 (15 15 (:META META-INTEGERP-CORRECT))
 (10 10 (:REWRITE TASPIP-FLG-AND-FLG-GIVES-T))
 (2 2 (:REWRITE DEL-WHEN-NOT-CONSP))
 )
(MEMBER-INT-OR-SYMBOL
 (221 51 (:REWRITE SUBSET-SAME-MEMBERS))
 (148 37 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (117 117 (:REWRITE DEFAULT-CAR))
 (115 53 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (96 24 (:REWRITE PERM-WHEN-NOT-CONSP))
 (71 71 (:REWRITE GET-TAXA-FROM-TAXON-INDEX-WHEN-NOT-CONSP))
 (60 4 (:REWRITE PERM-OF-CONSP))
 (58 15 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (51 51 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (48 48 (:TYPE-PRESCRIPTION PERM))
 (48 12 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (48 4 (:REWRITE SUBSET-OF-CONSP))
 (34 34 (:REWRITE REDUCE-INTEGERP-+))
 (34 34 (:REWRITE INTEGERP-MINUS-X))
 (34 34 (:META META-INTEGERP-CORRECT))
 (33 33 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (28 28 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE SUBSET-TRANSITIVE))
 (16 16 (:REWRITE SUBSET-APPEND-GIVES-2))
 (16 16 (:REWRITE SUBSET-APPEND-GIVES-1))
 (16 4 (:REWRITE DEL-WHEN-NOT-CONSP))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 )
(GOOD-INDEX-FLATTEN-TASPIP
 (53 10 (:REWRITE PERM-IMPLIES-SUBSET))
 (23 23 (:REWRITE TASPIP-FLG-CONSP-GIVES-TASPIP-NIL))
 (21 21 (:REWRITE TASPIP-WHEN-NOT-CONSP))
 (21 21 (:REWRITE GET-TAXA-FROM-TAXON-INDEX-WHEN-NOT-CONSP))
 (20 20 (:TYPE-PRESCRIPTION PERM))
 (18 18 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (10 10 (:REWRITE SUBSET-TRANSITIVE))
 (10 10 (:REWRITE SUBSET-APPEND-GIVES-2))
 (10 10 (:REWRITE SUBSET-APPEND-GIVES-1))
 (10 10 (:REWRITE PERM-WHEN-NOT-CONSP))
 (10 10 (:REWRITE NOT-INTERSECT-TOPS-NOT-SUBSET))
 (9 9 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (4 1 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (3 3 (:TYPE-PRESCRIPTION GET-TAXA-FROM-TAXON-INDEX))
 (1 1 (:REWRITE TASPIP-FLG-AND-FLG-GIVES-T))
 (1 1 (:REWRITE SUBSET-SAME-MEMBERS))
 (1 1 (:REWRITE NOT-MEMBER-SUBSET))
 (1 1 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (1 1 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 )
(NOT-MEMBER-NIL-MYTIPS-ANS
 (1080 56 (:REWRITE SUBSET-SAME-MEMBERS))
 (470 142 (:REWRITE PERM-WHEN-NOT-CONSP))
 (466 128 (:REWRITE TASPIP-NIL-AND-CONSP-GIVES-TASPIP-FLG))
 (457 63 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (370 88 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (283 283 (:TYPE-PRESCRIPTION PERM))
 (205 52 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (112 112 (:REWRITE TASPIP-FLG-CONSP-GIVES-TASPIP-NIL))
 (112 112 (:REWRITE GOOD-INDEX-FLATTEN-TASPIP))
 (90 90 (:REWRITE SUBSET-TRANSITIVE))
 (88 88 (:REWRITE SUBSET-APPEND-GIVES-2))
 (88 88 (:REWRITE SUBSET-APPEND-GIVES-1))
 (70 16 (:REWRITE TIP-P-GIVES-TASPIP-T))
 (59 3 (:REWRITE SUBSET-SUBSET-GIVES-SUBSET-APPEND))
 (56 56 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (50 10 (:DEFINITION BINARY-APPEND))
 (48 48 (:REWRITE DEFAULT-CDR))
 (48 48 (:REWRITE DEFAULT-CAR))
 (36 36 (:TYPE-PRESCRIPTION TIP-P))
 (31 17 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (16 16 (:REWRITE TASPIP-FLG-AND-FLG-GIVES-T))
 (15 6 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (15 1 (:REWRITE SUBSET-CONS))
 (12 1 (:REWRITE PERM-OF-CONSP))
 (4 1 (:REWRITE DEL-WHEN-NOT-CONSP))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 )
(MEMBER-FIRST-TAXON-TIPS
 (8 2 (:REWRITE TASPIP-NIL-AND-CONSP-GIVES-TASPIP-FLG))
 (2 2 (:REWRITE TASPIP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE TASPIP-FLG-CONSP-GIVES-TASPIP-NIL))
 (2 2 (:REWRITE MYTIPS-WHEN-NOT-CONSP))
 (2 2 (:REWRITE GOOD-INDEX-FLATTEN-TASPIP))
 (1 1 (:REWRITE FIRST-TAXON-WHEN-NOT-CONSP))
 )
(MEMBER-TAXA-ASSOC-HQUAL
 (184 43 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (173 35 (:REWRITE SUBSET-SAME-MEMBERS))
 (96 24 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (91 37 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (90 90 (:REWRITE DEFAULT-CAR))
 (88 22 (:REWRITE PERM-WHEN-NOT-CONSP))
 (54 54 (:REWRITE GET-TAXA-FROM-TAXON-INDEX-WHEN-NOT-CONSP))
 (48 12 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (45 3 (:REWRITE PERM-OF-CONSP))
 (44 44 (:TYPE-PRESCRIPTION PERM))
 (39 39 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (36 3 (:REWRITE SUBSET-OF-CONSP))
 (35 35 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (30 30 (:REWRITE DEFAULT-CDR))
 (27 27 (:REWRITE MEMBER-GIVES-ASSOC-HQUAL))
 (16 16 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (16 16 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (16 16 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (16 16 (:REWRITE |(equal (- x) (- y))|))
 (15 15 (:REWRITE SUBSET-TRANSITIVE))
 (15 15 (:REWRITE SUBSET-APPEND-GIVES-2))
 (15 15 (:REWRITE SUBSET-APPEND-GIVES-1))
 (12 3 (:REWRITE DEL-WHEN-NOT-CONSP))
 (4 1 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (1 1 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 )
(ASSOC-CAR-FROM-SUBSET
 (100 4 (:DEFINITION HONS-ASSOC-EQUAL))
 (68 12 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (20 4 (:DEFINITION HONS-EQUAL))
 (18 18 (:REWRITE DEFAULT-CAR))
 (15 15 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (15 3 (:REWRITE PERM-IMPLIES-SUBSET))
 (9 9 (:REWRITE GET-TAXA-FROM-TAXON-INDEX-WHEN-NOT-CONSP))
 (8 8 (:REWRITE DEFAULT-CDR))
 (6 6 (:TYPE-PRESCRIPTION PERM))
 (6 6 (:REWRITE MEMBER-GIVES-ASSOC-HQUAL))
 (4 4 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (4 4 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (4 4 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (4 4 (:REWRITE |(equal (- x) (- y))|))
 (4 1 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (3 3 (:TYPE-PRESCRIPTION GET-TAXA-FROM-TAXON-INDEX))
 (3 3 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (3 3 (:REWRITE SUBSET-TRANSITIVE))
 (3 3 (:REWRITE SUBSET-SAME-MEMBERS))
 (3 3 (:REWRITE SUBSET-APPEND-GIVES-2))
 (3 3 (:REWRITE SUBSET-APPEND-GIVES-1))
 (3 3 (:REWRITE PERM-WHEN-NOT-CONSP))
 (3 3 (:REWRITE NOT-INTERSECT-TOPS-NOT-SUBSET))
 (3 3 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (3 3 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (1 1 (:REWRITE NOT-MEMBER-SUBSET))
 )
(PROPER-SUBTREE-MEMBER-GEN
 (176 44 (:REWRITE TIP-P-NOT-PROPER-SUBTREE))
 (115 23 (:REWRITE SUBTREE-P-WHEN-NOT-EQUAL))
 (88 88 (:TYPE-PRESCRIPTION TIP-P))
 (49 14 (:REWRITE SUBSET-SAME-MEMBERS))
 (44 44 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (44 44 (:REWRITE PROPER-SUBTREEP-WHEN-NOT-CONSP))
 (35 35 (:REWRITE DEFAULT-CAR))
 (33 33 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (33 33 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (33 33 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (33 33 (:REWRITE |(equal (- x) (- y))|))
 (32 32 (:REWRITE DEFAULT-CDR))
 (24 2 (:REWRITE SUBSET-OF-CONSP))
 (22 15 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (18 2 (:REWRITE PERM-OF-CONSP))
 (16 16 (:TYPE-PRESCRIPTION PERM))
 (14 14 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (8 8 (:REWRITE PERM-WHEN-NOT-CONSP))
 (7 7 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (6 6 (:REWRITE SUBSET-TRANSITIVE))
 (6 6 (:REWRITE SUBSET-APPEND-GIVES-2))
 (6 6 (:REWRITE SUBSET-APPEND-GIVES-1))
 (4 4 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (2 2 (:REWRITE DEL-WHEN-NOT-CONSP))
 (1 1 (:REWRITE NOT-MEMBER-GEN-CDR))
 )
(SUBSET-MEMBER-HQUAL
 (557 209 (:REWRITE SUBSET-SAME-MEMBERS))
 (293 218 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (209 209 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (207 207 (:TYPE-PRESCRIPTION PERM))
 (182 182 (:REWRITE DEFAULT-CDR))
 (176 176 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (164 164 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (164 164 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (164 164 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (164 164 (:REWRITE |(equal (- x) (- y))|))
 (162 18 (:REWRITE PERM-OF-CONSP))
 (142 142 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (108 105 (:REWRITE PERM-WHEN-NOT-CONSP))
 (84 84 (:REWRITE SUBSET-TRANSITIVE))
 (84 84 (:REWRITE SUBSET-APPEND-GIVES-2))
 (84 84 (:REWRITE SUBSET-APPEND-GIVES-1))
 (26 26 (:REWRITE NOT-INTERSECT-TOPS-NOT-SUBSET))
 (18 18 (:REWRITE DEL-WHEN-NOT-CONSP))
 )
(NOT-MEMBER-THROUGH-EVENS
 (246 28 (:REWRITE SUBSET-SAME-MEMBERS))
 (107 41 (:REWRITE PERM-WHEN-NOT-CONSP))
 (94 29 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (92 29 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (80 80 (:TYPE-PRESCRIPTION PERM))
 (67 5 (:REWRITE PERM-OF-CONSP))
 (49 49 (:REWRITE EVENS-GEN-WHEN-NOT-CONSP))
 (34 2 (:REWRITE SUBSET-OF-CONSP))
 (31 31 (:REWRITE SUBSET-TRANSITIVE))
 (31 31 (:REWRITE SUBSET-APPEND-GIVES-2))
 (31 31 (:REWRITE SUBSET-APPEND-GIVES-1))
 (28 28 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (24 24 (:REWRITE DEFAULT-CDR))
 (22 22 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (11 5 (:REWRITE DEL-WHEN-NOT-CONSP))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 )
(HHSHRINK-ALIST-TREE-LIST-DOMAIN-ALISTP1
 (660 660 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (506 110 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (506 110 (:REWRITE MEMBER-TAXA-ASSOC-HQUAL))
 (506 110 (:REWRITE ASSOC-CAR-FROM-SUBSET))
 (348 348 (:REWRITE DEFAULT-CAR))
 (330 330 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (222 12 (:REWRITE GOOD-TAXON-INDEX-HALIST-OF-CONSP))
 (128 128 (:REWRITE DEFAULT-CDR))
 (110 110 (:REWRITE MEMBER-GIVES-ASSOC-HQUAL))
 (54 15 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (50 50 (:TYPE-PRESCRIPTION FAST-ALIST-FORK))
 (42 42 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (42 42 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (42 42 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (42 42 (:REWRITE |(equal (- x) (- y))|))
 (24 24 (:TYPE-PRESCRIPTION TIP-P))
 (24 24 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:META META-INTEGERP-CORRECT))
 (21 12 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (13 4 (:REWRITE TREE-LIST-LISTP-TREE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION NON-TIP-TREE-LISTP))
 (4 4 (:REWRITE TREE-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE NON-TIP-TREE-LISTP-WHEN-NOT-CONSP))
 )
(HSHRINK-ALIST-TREE-LIST-DOMAIN-ALISTP1
 (660 660 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (506 110 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (506 110 (:REWRITE MEMBER-TAXA-ASSOC-HQUAL))
 (506 110 (:REWRITE ASSOC-CAR-FROM-SUBSET))
 (348 348 (:REWRITE DEFAULT-CAR))
 (330 330 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (222 12 (:REWRITE GOOD-TAXON-INDEX-HALIST-OF-CONSP))
 (128 128 (:REWRITE DEFAULT-CDR))
 (110 110 (:REWRITE MEMBER-GIVES-ASSOC-HQUAL))
 (54 15 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (50 50 (:TYPE-PRESCRIPTION FAST-ALIST-FORK))
 (42 42 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (42 42 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (42 42 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (42 42 (:REWRITE |(equal (- x) (- y))|))
 (24 24 (:TYPE-PRESCRIPTION TIP-P))
 (24 24 (:REWRITE REDUCE-INTEGERP-+))
 (24 24 (:REWRITE INTEGERP-MINUS-X))
 (24 24 (:META META-INTEGERP-CORRECT))
 (21 12 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (13 4 (:REWRITE TREE-LIST-LISTP-TREE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION NON-TIP-TREE-LISTP))
 (4 4 (:REWRITE TREE-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE NON-TIP-TREE-LISTP-WHEN-NOT-CONSP))
 )
(MEMBER-GEN-GIVES-SMALLER-DEL
 (3902 208 (:DEFINITION INTEGER-ABS))
 (2488 856 (:REWRITE DEFAULT-+-2))
 (1976 104 (:REWRITE |(+ (if a b c) x)|))
 (1170 104 (:REWRITE NUMERATOR-NEGATIVE))
 (1088 856 (:REWRITE DEFAULT-+-1))
 (1040 104 (:DEFINITION LENGTH))
 (856 856 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (728 104 (:DEFINITION LEN))
 (642 220 (:REWRITE DEFAULT-UNARY-MINUS))
 (445 59 (:REWRITE SUBSET-SAME-MEMBERS))
 (428 371 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (416 416 (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 2))
 (416 416 (:TYPE-PRESCRIPTION NUMERATOR-POSITIVE . 1))
 (416 416 (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 2))
 (416 416 (:TYPE-PRESCRIPTION NUMERATOR-NEGATIVE . 1))
 (412 371 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (363 363 (:REWRITE |(< (- x) (- y))|))
 (342 259 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (342 259 (:REWRITE PREFER-POSITIVE-ADDENDS-<))
 (316 316 (:REWRITE |(< (- x) 0)|))
 (290 253 (:REWRITE DEFAULT-<-1))
 (289 253 (:REWRITE DEFAULT-<-2))
 (286 286 (:REWRITE |(+ c (+ d x))|))
 (266 266 (:REWRITE FOLD-CONSTS-IN-+))
 (246 246 (:REWRITE DEFAULT-CDR))
 (231 21 (:REWRITE SUBTREEP-SMALLER))
 (223 64 (:REWRITE PERM-WHEN-NOT-CONSP))
 (212 212 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (197 61 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (166 166 (:REWRITE DEFAULT-CAR))
 (147 39 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (140 35 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (140 8 (:REWRITE SUBSET-OF-CONSP))
 (128 128 (:TYPE-PRESCRIPTION PERM))
 (126 126 (:LINEAR SUBTREEP-SMALLER))
 (125 125 (:REWRITE STRIP-CARS-GEN-WHEN-NOT-CONSP))
 (120 8 (:REWRITE PERM-OF-CONSP))
 (105 21 (:REWRITE SUBTREE-P-WHEN-NOT-EQUAL))
 (104 104 (:TYPE-PRESCRIPTION LEN))
 (104 104 (:REWRITE REDUCE-INTEGERP-+))
 (104 104 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (104 104 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (104 104 (:REWRITE INTEGERP-MINUS-X))
 (104 104 (:REWRITE DEFAULT-REALPART))
 (104 104 (:REWRITE DEFAULT-NUMERATOR))
 (104 104 (:REWRITE DEFAULT-IMAGPART))
 (104 104 (:REWRITE DEFAULT-DENOMINATOR))
 (104 104 (:REWRITE DEFAULT-COERCE-2))
 (104 104 (:REWRITE DEFAULT-COERCE-1))
 (104 104 (:META META-INTEGERP-CORRECT))
 (84 4 (:REWRITE |(< (if a b c) x)|))
 (63 21 (:REWRITE PROPER-GIVES-SUBTREE))
 (59 59 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (47 47 (:REWRITE SUBSET-TRANSITIVE))
 (47 47 (:REWRITE SUBSET-APPEND-GIVES-2))
 (47 47 (:REWRITE SUBSET-APPEND-GIVES-1))
 (42 42 (:TYPE-PRESCRIPTION SUBTREEP))
 (42 42 (:TYPE-PRESCRIPTION PROPER-SUBTREEP))
 (41 41 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (32 8 (:REWRITE DEL-WHEN-NOT-CONSP))
 (31 31 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (31 31 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (31 31 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (31 31 (:REWRITE DEL-PAIR-WHEN-NOT-CONSP))
 (31 31 (:REWRITE |(equal (- x) (- y))|))
 (30 20 (:REWRITE |(< d (+ c x y))|))
 (10 4 (:REWRITE |(< (+ d x) (+ c y))|))
 (10 4 (:REWRITE |(< (+ c x) (+ d y))|))
 (9 4 (:REWRITE |(< (+ c x) d)|))
 (4 2 (:REWRITE |(- (if a b c))|))
 (3 2 (:REWRITE |(< (+ c x y) d)|))
 )
(ALISTP-GEN-THROUGH-DEL-PAIR
 (680 27 (:REWRITE INTEGER-HALISTP-HALISTP))
 (604 32 (:DEFINITION INTEGER-HALISTP))
 (220 49 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (169 25 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (145 145 (:TYPE-PRESCRIPTION INTEGER-HALISTP))
 (128 27 (:REWRITE GOOD-TAXON-INTEGER-LISTP-ALISTP-GEN))
 (91 91 (:REWRITE DEFAULT-CAR))
 (75 75 (:REWRITE DEFAULT-CDR))
 (63 63 (:REWRITE REDUCE-INTEGERP-+))
 (63 63 (:REWRITE INTEGERP-MINUS-X))
 (63 63 (:META META-INTEGERP-CORRECT))
 (54 54 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (50 50 (:TYPE-PRESCRIPTION TIP-P))
 (27 27 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (26 26 (:REWRITE ALISTP-GEN-OF-NOT-CONSP))
 (22 1 (:REWRITE GOOD-TAXON-INDEX-HALIST-OF-CONSP))
 (13 13 (:REWRITE DEL-PAIR-WHEN-NOT-CONSP))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (3 3 (:REWRITE CDR-CONS))
 )
(NOT-MEMBER-THROUGH-DEL-PAIR
 (505 42 (:REWRITE SUBSET-SAME-MEMBERS))
 (236 71 (:REWRITE PERM-WHEN-NOT-CONSP))
 (172 46 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (164 164 (:REWRITE STRIP-CARS-GEN-WHEN-NOT-CONSP))
 (120 8 (:REWRITE PERM-OF-CONSP))
 (104 26 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (84 84 (:REWRITE DEL-PAIR-WHEN-NOT-CONSP))
 (72 4 (:REWRITE SUBSET-OF-CONSP))
 (50 50 (:REWRITE SUBSET-TRANSITIVE))
 (50 50 (:REWRITE SUBSET-APPEND-GIVES-2))
 (50 50 (:REWRITE SUBSET-APPEND-GIVES-1))
 (42 42 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (32 32 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (32 8 (:REWRITE DEL-WHEN-NOT-CONSP))
 (14 14 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (7 7 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (7 7 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (7 7 (:REWRITE |(equal (- x) (- y))|))
 )
(SUBSET-THROUGH-DEL-PAIR
 (180 180 (:TYPE-PRESCRIPTION STRIP-CARS-GEN))
 (130 34 (:REWRITE PERM-WHEN-NOT-CONSP))
 (112 28 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (68 68 (:TYPE-PRESCRIPTION PERM))
 (64 64 (:REWRITE STRIP-CARS-GEN-WHEN-NOT-CONSP))
 (34 34 (:REWRITE NOT-INTERSECT-TOPS-NOT-SUBSET))
 (30 30 (:REWRITE SUBSET-APPEND-GIVES-2))
 (30 30 (:REWRITE SUBSET-APPEND-GIVES-1))
 (30 30 (:REWRITE DEL-PAIR-WHEN-NOT-CONSP))
 (16 2 (:REWRITE PERM-OF-CONSP))
 (6 6 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:REWRITE SUBSET-SAME-MEMBERS))
 (4 4 (:REWRITE NOT-MEMBER-SUBSET))
 (4 4 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (4 4 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (4 4 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEL-WHEN-NOT-CONSP))
 )
(TASPIP-T-GIVES-MEMBER-GEN-FIRST-TAXON-MYTIPS
 (99 28 (:REWRITE TASPIP-NIL-AND-CONSP-GIVES-TASPIP-FLG))
 (50 11 (:REWRITE TIP-P-GIVES-TASPIP-T))
 (26 26 (:TYPE-PRESCRIPTION TIP-P))
 (26 12 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (24 6 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (20 6 (:REWRITE CONSP-SUBSET-MEMBER-FIRST-TAXON))
 (17 17 (:REWRITE TASPIP-FLG-CONSP-GIVES-TASPIP-NIL))
 (17 17 (:REWRITE GOOD-INDEX-FLATTEN-TASPIP))
 (15 6 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (12 12 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (11 11 (:REWRITE TASPIP-FLG-AND-FLG-GIVES-T))
 (8 8 (:REWRITE SUBSET-SAME-MEMBERS))
 (8 8 (:REWRITE NOT-MEMBER-SUBSET))
 (8 8 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (8 8 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (6 6 (:TYPE-PRESCRIPTION SUBSET))
 (6 6 (:REWRITE PERM-IMPLIES-SUBSET))
 (3 3 (:REWRITE REDUCE-INTEGERP-+))
 (3 3 (:REWRITE INTEGERP-MINUS-X))
 (3 3 (:META META-INTEGERP-CORRECT))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(NOT-MEMBER-NIL-MYTIPS
 (207 11 (:REWRITE SUBSET-SAME-MEMBERS))
 (96 12 (:REWRITE NOT-MEMBER-NIL-MYTIPS-ANS))
 (94 25 (:REWRITE PERM-WHEN-NOT-CONSP))
 (88 19 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (74 14 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (50 50 (:TYPE-PRESCRIPTION PERM))
 (40 10 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (40 2 (:REWRITE SUBSET-SUBSET-GIVES-SUBSET-APPEND))
 (36 36 (:TYPE-PRESCRIPTION TASPIP))
 (36 12 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (25 5 (:DEFINITION BINARY-APPEND))
 (24 12 (:REWRITE TASPIP-NIL-AND-CONSP-GIVES-TASPIP-FLG))
 (19 19 (:REWRITE SUBSET-TRANSITIVE))
 (19 19 (:REWRITE SUBSET-APPEND-GIVES-2))
 (19 19 (:REWRITE SUBSET-APPEND-GIVES-1))
 (14 14 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (12 12 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (12 12 (:REWRITE TASPIP-WHEN-NOT-CONSP))
 (12 12 (:REWRITE TASPIP-FLG-CONSP-GIVES-TASPIP-NIL))
 (12 12 (:REWRITE GOOD-INDEX-FLATTEN-TASPIP))
 (11 11 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (11 11 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 )
(TASPIP-NIL-THROUGH-DEL-PAIR
 (142 58 (:REWRITE TASPIP-WHEN-NOT-CONSP))
 (64 58 (:REWRITE TASPIP-FLG-CONSP-GIVES-TASPIP-NIL))
 (58 58 (:REWRITE GOOD-INDEX-FLATTEN-TASPIP))
 (8 2 (:REWRITE TIP-P-GIVES-TASPIP-T))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 (4 4 (:TYPE-PRESCRIPTION TIP-P))
 (2 2 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 )
(TASPIP-NIL-STRIPS-CDRS-MEMBER-GIVES-TASPIP-T
 (606 92 (:REWRITE TASPIP-NIL-AND-CONSP-GIVES-TASPIP-FLG))
 (330 92 (:REWRITE TASPIP-WHEN-NOT-CONSP))
 (288 20 (:REWRITE TIP-P-GIVES-TASPIP-T))
 (245 41 (:REWRITE SUBSET-SAME-MEMBERS))
 (228 20 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (198 99 (:TYPE-PRESCRIPTION INTEGER-ASSOC-HQUAL-INTEGER-HALISTP))
 (114 42 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (112 28 (:REWRITE NOT-CONSP-ASSOC-NOT-ASSOC-HQUAL))
 (112 28 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (100 25 (:REWRITE PERM-WHEN-NOT-CONSP))
 (99 99 (:TYPE-PRESCRIPTION INTEGER-HALISTP))
 (80 32 (:REWRITE ATOM-CDR-ASSOC-GOOD-TAXON-LIST))
 (78 78 (:TYPE-PRESCRIPTION STRIP-CDRS-GEN))
 (72 72 (:REWRITE TASPIP-FLG-CONSP-GIVES-TASPIP-NIL))
 (72 72 (:REWRITE GOOD-INDEX-FLATTEN-TASPIP))
 (63 63 (:REWRITE STRIP-CARS-GEN-WHEN-NOT-CONSP))
 (60 4 (:REWRITE PERM-OF-CONSP))
 (56 56 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (50 50 (:TYPE-PRESCRIPTION PERM))
 (48 12 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (48 4 (:REWRITE SUBSET-OF-CONSP))
 (41 41 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (40 40 (:TYPE-PRESCRIPTION TIP-P))
 (32 32 (:TYPE-PRESCRIPTION GOOD-INDEX-TAXON-HALIST))
 (30 30 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (28 28 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (22 22 (:REWRITE STRIP-CDRS-GEN-WHEN-NOT-CONSP))
 (16 16 (:REWRITE SUBSET-TRANSITIVE))
 (16 16 (:REWRITE SUBSET-APPEND-GIVES-2))
 (16 16 (:REWRITE SUBSET-APPEND-GIVES-1))
 (16 16 (:REWRITE GOOD-INDEX-TAXON-HALIST-WHEN-NOT-CONSP))
 (16 4 (:REWRITE DEL-WHEN-NOT-CONSP))
 (14 14 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (14 14 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (14 14 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (14 14 (:REWRITE |(equal (- x) (- y))|))
 )
(MEMBER-GEN-X-DEL-PAIR-MEMBER-ORIGINAL
 (435 38 (:REWRITE SUBSET-SAME-MEMBERS))
 (225 42 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (210 63 (:REWRITE PERM-WHEN-NOT-CONSP))
 (156 42 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (146 146 (:REWRITE STRIP-CDRS-GEN-WHEN-NOT-CONSP))
 (126 126 (:TYPE-PRESCRIPTION PERM))
 (96 24 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (90 6 (:REWRITE PERM-OF-CONSP))
 (78 78 (:REWRITE DEL-PAIR-WHEN-NOT-CONSP))
 (72 4 (:REWRITE SUBSET-OF-CONSP))
 (46 46 (:REWRITE SUBSET-TRANSITIVE))
 (46 46 (:REWRITE SUBSET-APPEND-GIVES-2))
 (46 46 (:REWRITE SUBSET-APPEND-GIVES-1))
 (38 38 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (30 30 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (24 6 (:REWRITE DEL-WHEN-NOT-CONSP))
 (5 5 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (5 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (5 5 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (5 5 (:REWRITE |(equal (- x) (- y))|))
 )
(SUBSET-X-DEL-PAIR-SUBSET-ORIGINAL
 (79 79 (:REWRITE STRIP-CDRS-GEN-WHEN-NOT-CONSP))
 (70 70 (:TYPE-PRESCRIPTION PERM))
 (68 35 (:REWRITE PERM-WHEN-NOT-CONSP))
 (66 33 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (36 36 (:REWRITE DEL-PAIR-WHEN-NOT-CONSP))
 (34 34 (:REWRITE SUBSET-APPEND-GIVES-2))
 (34 34 (:REWRITE SUBSET-APPEND-GIVES-1))
 (32 8 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (24 24 (:REWRITE NOT-INTERSECT-TOPS-NOT-SUBSET))
 (8 8 (:REWRITE SUBSET-SAME-MEMBERS))
 (8 8 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (8 8 (:REWRITE NOT-MEMBER-SUBSET))
 (8 8 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (8 8 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 1 (:REWRITE PERM-OF-CONSP))
 (7 7 (:REWRITE DEFAULT-CAR))
 (4 1 (:REWRITE DEL-WHEN-NOT-CONSP))
 )
(SUBSET-MYTIPS-CDR-ASSOC-HQUAL
 (508 121 (:REWRITE MYTIPS-WHEN-NOT-CONSP))
 (184 184 (:TYPE-PRESCRIPTION MYTIPS))
 (126 63 (:TYPE-PRESCRIPTION INTEGER-ASSOC-HQUAL-INTEGER-HALISTP))
 (125 32 (:REWRITE PERM-WHEN-NOT-CONSP))
 (108 27 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (90 90 (:TYPE-PRESCRIPTION STRIP-CDRS-GEN))
 (84 21 (:REWRITE ATOM-CDR-ASSOC-GOOD-TAXON-LIST))
 (64 64 (:TYPE-PRESCRIPTION PERM))
 (63 63 (:TYPE-PRESCRIPTION INTEGER-HALISTP))
 (42 42 (:TYPE-PRESCRIPTION GOOD-INDEX-TAXON-HALIST))
 (37 37 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (37 37 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (37 37 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (37 37 (:REWRITE |(equal (- x) (- y))|))
 (27 27 (:REWRITE SUBSET-APPEND-GIVES-2))
 (27 27 (:REWRITE SUBSET-APPEND-GIVES-1))
 (26 26 (:REWRITE NOT-INTERSECT-TOPS-NOT-SUBSET))
 (21 21 (:REWRITE GOOD-INDEX-TAXON-HALIST-WHEN-NOT-CONSP))
 (18 9 (:TYPE-PRESCRIPTION BOUND-TO-NAT-HET-NUMBER))
 )
(SUBSET-MYTIPS-STRIP-CDRS-DEL-PAIR
 (154 70 (:REWRITE MYTIPS-WHEN-NOT-CONSP))
 (102 102 (:TYPE-PRESCRIPTION MYTIPS))
 (84 84 (:TYPE-PRESCRIPTION STRIP-CDRS-GEN))
 (73 16 (:REWRITE PERM-WHEN-NOT-CONSP))
 (44 11 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (32 32 (:TYPE-PRESCRIPTION PERM))
 (13 13 (:REWRITE NOT-INTERSECT-TOPS-NOT-SUBSET))
 (11 11 (:REWRITE SUBSET-APPEND-GIVES-2))
 (11 11 (:REWRITE SUBSET-APPEND-GIVES-1))
 (9 3 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 )
(NOT-INT-SYM-MEMBER-NOT-INT-SYMLIST
 (138 35 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (109 39 (:REWRITE SUBSET-SAME-MEMBERS))
 (67 67 (:TYPE-PRESCRIPTION TIP-P))
 (55 41 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (48 4 (:REWRITE SUBSET-OF-CONSP))
 (39 39 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (37 33 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (36 4 (:REWRITE PERM-OF-CONSP))
 (34 34 (:REWRITE REDUCE-INTEGERP-+))
 (34 34 (:REWRITE INTEGERP-MINUS-X))
 (34 34 (:META META-INTEGERP-CORRECT))
 (32 32 (:TYPE-PRESCRIPTION PERM))
 (29 29 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (29 29 (:REWRITE DEFAULT-CAR))
 (25 25 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (23 23 (:REWRITE INT-SYMLIST-WHEN-NOT-CONSP))
 (16 16 (:REWRITE PERM-WHEN-NOT-CONSP))
 (14 14 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE SUBSET-TRANSITIVE))
 (12 12 (:REWRITE SUBSET-APPEND-GIVES-2))
 (12 12 (:REWRITE SUBSET-APPEND-GIVES-1))
 (8 8 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (4 4 (:REWRITE DEL-WHEN-NOT-CONSP))
 (2 2 (:REWRITE NOT-MEMBER-GEN-CDR))
 )
(NOT-MEMBER-NIL-INTSYMLIST
 (125 55 (:REWRITE SUBSET-SAME-MEMBERS))
 (71 57 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (55 55 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (48 4 (:REWRITE SUBSET-OF-CONSP))
 (38 10 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (36 4 (:REWRITE PERM-OF-CONSP))
 (32 32 (:TYPE-PRESCRIPTION PERM))
 (27 27 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (25 25 (:REWRITE DEFAULT-CAR))
 (23 23 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (20 20 (:REWRITE INT-SYMLIST-WHEN-NOT-CONSP))
 (17 17 (:TYPE-PRESCRIPTION TIP-P))
 (16 16 (:REWRITE PERM-WHEN-NOT-CONSP))
 (16 16 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE SUBSET-TRANSITIVE))
 (12 12 (:REWRITE SUBSET-APPEND-GIVES-2))
 (12 12 (:REWRITE SUBSET-APPEND-GIVES-1))
 (12 8 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (9 9 (:REWRITE REDUCE-INTEGERP-+))
 (9 9 (:REWRITE INTEGERP-MINUS-X))
 (9 9 (:META META-INTEGERP-CORRECT))
 (8 8 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (4 4 (:REWRITE DEL-WHEN-NOT-CONSP))
 (2 2 (:REWRITE NOT-MEMBER-GEN-CDR))
 )
(DEL-INTSYM-ELEMENT-INTSYMLIST-SAME
 (170 170 (:REWRITE SUBSET-SAME-MEMBERS))
 (170 170 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (170 170 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (112 28 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (94 50 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (94 50 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (94 50 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (56 56 (:TYPE-PRESCRIPTION TIP-P))
 (50 50 (:REWRITE |(equal (- x) (- y))|))
 (30 30 (:REWRITE REDUCE-INTEGERP-+))
 (30 30 (:REWRITE INTEGERP-MINUS-X))
 (30 30 (:META META-INTEGERP-CORRECT))
 (28 28 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (26 26 (:REWRITE DEFAULT-CAR))
 (24 24 (:REWRITE DEFAULT-CDR))
 )
(PERM-IMPLIES-EQUAL-INT-SYMLIST-1
 (1044 25 (:REWRITE DIFF-LENS-NOT-PERM))
 (500 62 (:DEFINITION LEN))
 (146 73 (:REWRITE DEFAULT-+-2))
 (126 51 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (126 51 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (126 51 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (103 103 (:REWRITE SUBSET-SAME-MEMBERS))
 (103 103 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (81 81 (:REWRITE DEFAULT-CDR))
 (73 73 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (73 73 (:REWRITE NORMALIZE-ADDENDS))
 (73 73 (:REWRITE DEFAULT-+-1))
 (51 51 (:REWRITE |(equal (- x) (- y))|))
 (32 8 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (29 29 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE |(equal (+ c x) d)|))
 (16 16 (:TYPE-PRESCRIPTION TIP-P))
 (10 2 (:REWRITE MEMBER-GEN-OF-CONSP))
 (8 8 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (8 8 (:REWRITE REDUCE-INTEGERP-+))
 (8 8 (:REWRITE INTEGERP-MINUS-X))
 (8 8 (:REWRITE DEL-WHEN-NOT-CONSP))
 (8 8 (:META META-INTEGERP-CORRECT))
 (3 3 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (3 3 (:REWRITE NOT-MEMBER-SUBSET))
 (3 3 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (1 1 (:REWRITE |(equal (- x) 0)|))
 )
(NOT-MEMBER-NOT-CONSP-ASSOC
 (127 21 (:REWRITE SUBSET-SAME-MEMBERS))
 (126 20 (:REWRITE NOT-MEMBER-SUBSET))
 (104 12 (:REWRITE PERM-IMPLIES-SUBSET))
 (81 19 (:REWRITE MEMBER-TAXA-ASSOC-HQUAL))
 (72 18 (:REWRITE PERM-WHEN-NOT-CONSP))
 (67 21 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (51 51 (:REWRITE DEFAULT-CAR))
 (48 12 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (36 36 (:TYPE-PRESCRIPTION PERM))
 (24 24 (:TYPE-PRESCRIPTION SUBSET))
 (21 21 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (20 20 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (19 19 (:REWRITE MEMBER-GIVES-ASSOC-HQUAL))
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE SUBSET-TRANSITIVE))
 (12 12 (:REWRITE SUBSET-APPEND-GIVES-2))
 (12 12 (:REWRITE SUBSET-APPEND-GIVES-1))
 (8 8 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (8 8 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (8 8 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (8 8 (:REWRITE |(equal (- x) (- y))|))
 (4 1 (:REWRITE ASSOC-CAR-FROM-SUBSET))
 (1 1 (:REWRITE GET-TAXA-FROM-TAXON-INDEX-WHEN-NOT-CONSP))
 )
(NOT-MEMBER-THROUGH-BUILD-FAST
 (1278 71 (:REWRITE SUBSET-SAME-MEMBERS))
 (546 196 (:REWRITE PERM-WHEN-NOT-CONSP))
 (267 267 (:REWRITE DEFAULT-CAR))
 (232 232 (:REWRITE DEFAULT-CDR))
 (204 51 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (192 12 (:REWRITE PERM-OF-CONSP))
 (150 150 (:TYPE-PRESCRIPTION BUILD-FAST-ALIST-FROM-ALIST))
 (144 144 (:REWRITE SUBSET-X-DEL-PAIR-SUBSET-ORIGINAL))
 (143 143 (:REWRITE SUBSET-TRANSITIVE))
 (143 143 (:REWRITE SUBSET-APPEND-GIVES-2))
 (143 143 (:REWRITE SUBSET-APPEND-GIVES-1))
 (127 5 (:REWRITE SUBSET-OF-CONSP))
 (72 72 (:REWRITE MEMBER-GEN-X-DEL-PAIR-MEMBER-ORIGINAL))
 (71 71 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (57 57 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (48 12 (:REWRITE DEL-WHEN-NOT-CONSP))
 (16 1 (:REWRITE SUBSET-CONS))
 (3 3 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (3 3 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (3 3 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (3 3 (:REWRITE |(equal (- x) (- y))|))
 )
(MEMBER-THROUGH-BUILD-FAST
 (412 18 (:REWRITE INTEGER-HALISTP-HALISTP))
 (396 57 (:REWRITE MEMBER-PERM-GIVES-MEMBER))
 (371 25 (:DEFINITION INTEGER-HALISTP))
 (344 212 (:REWRITE STRIP-CARS-GEN-WHEN-NOT-CONSP))
 (318 99 (:REWRITE PERM-WHEN-NOT-CONSP))
 (261 261 (:REWRITE DEFAULT-CAR))
 (234 66 (:REWRITE SUBSET-WHEN-NOT-CONS))
 (187 187 (:REWRITE DEFAULT-CDR))
 (148 37 (:REWRITE MEMBER-GEN-WHEN-NOT-CONS))
 (132 132 (:TYPE-PRESCRIPTION BUILD-FAST-ALIST-FROM-ALIST))
 (120 8 (:REWRITE PERM-OF-CONSP))
 (108 24 (:REWRITE TIP-P-NOT-INTEGER-GIVES-SYMBOLP))
 (85 4 (:REWRITE SUBSET-OF-CONSP))
 (84 12 (:REWRITE TIP-P-WHEN-NOT-CONSP))
 (80 80 (:TYPE-PRESCRIPTION INTEGER-HALISTP))
 (72 18 (:REWRITE GOOD-TAXON-INTEGER-LISTP-ALISTP-GEN))
 (70 70 (:REWRITE SUBSET-TRANSITIVE))
 (70 70 (:REWRITE SUBSET-APPEND-GIVES-2))
 (70 70 (:REWRITE SUBSET-APPEND-GIVES-1))
 (54 54 (:REWRITE MEMBER-DIFFERENCE-MEMBER))
 (48 3 (:REWRITE SUBSET-CONS))
 (43 43 (:REWRITE PROPER-SUBTREE-MEMBER-GEN))
 (38 38 (:REWRITE REDUCE-INTEGERP-+))
 (38 38 (:REWRITE INTEGERP-MINUS-X))
 (38 38 (:META META-INTEGERP-CORRECT))
 (36 36 (:TYPE-PRESCRIPTION GOOD-TAXON-INDEX-HALIST))
 (32 8 (:REWRITE DEL-WHEN-NOT-CONSP))
 (24 24 (:TYPE-PRESCRIPTION TIP-P))
 (18 18 (:REWRITE GOOD-TAXON-INDEX-HALIST-WHEN-NOT-CONSP))
 (18 18 (:REWRITE ALISTP-GEN-OF-NOT-CONSP))
 (6 6 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (6 6 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (6 6 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (6 6 (:REWRITE |(equal (- x) (- y))|))
 )
