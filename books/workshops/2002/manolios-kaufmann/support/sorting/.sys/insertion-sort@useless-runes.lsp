(INSERT)
(ISORT)
(ORDERED-INSERT
 (1112 101 (:REWRITE <<-IMPLIES-LEXORDER))
 (714 185 (:REWRITE <<-TRICHOTOMY))
 (542 542 (:TYPE-PRESCRIPTION <<))
 (185 185 (:REWRITE <<-TRANSITIVE))
 (172 86 (:REWRITE <<-ASYMMETRIC))
 (129 96 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE <<-IRREFLEXIVE))
 )
(ORDERED-SORT
 (84 6 (:DEFINITION <<=))
 (72 6 (:REWRITE <<-IMPLIES-LEXORDER))
 (69 3 (:DEFINITION ORDEREDP))
 (63 3 (:DEFINITION INSERT))
 (48 12 (:REWRITE <<-TRICHOTOMY))
 (36 36 (:TYPE-PRESCRIPTION <<))
 (15 15 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE DEFAULT-CDR))
 (12 12 (:TYPE-PRESCRIPTION ISORT))
 (12 12 (:REWRITE <<-TRANSITIVE))
 (12 6 (:REWRITE <<-ASYMMETRIC))
 (6 6 (:TYPE-PRESCRIPTION LEXORDER))
 (6 6 (:REWRITE LEXORDER-TRANSITIVE))
 )
(PERM-INSERT
 (414 35 (:REWRITE <<-IMPLIES-LEXORDER))
 (397 322 (:REWRITE DEFAULT-CAR))
 (335 335 (:TYPE-PRESCRIPTION INSERT))
 (304 254 (:REWRITE DEFAULT-CDR))
 (274 69 (:REWRITE <<-TRICHOTOMY))
 (246 69 (:REWRITE PERM-TRANSITIVE))
 (206 206 (:TYPE-PRESCRIPTION <<))
 (182 16 (:REWRITE CAR-PERM))
 (112 7 (:REWRITE REMOVE-EL-SWAP))
 (69 69 (:REWRITE <<-TRANSITIVE))
 (68 34 (:REWRITE <<-ASYMMETRIC))
 (7 7 (:REWRITE REMOVE-EL-IN))
 (1 1 (:REWRITE CONS-CAR-CDR))
 (1 1 (:REWRITE <<-IRREFLEXIVE))
 )
(PERM-SORT
 (39 6 (:DEFINITION IN))
 (36 6 (:DEFINITION REMOVE-EL))
 (33 33 (:TYPE-PRESCRIPTION ISORT))
 (33 33 (:REWRITE DEFAULT-CAR))
 (27 27 (:REWRITE DEFAULT-CDR))
 (18 18 (:TYPE-PRESCRIPTION IN))
 (18 18 (:REWRITE PERM-TRANSITIVE))
 (6 6 (:REWRITE CAR-PERM))
 )
(INSERT-INSERT
 (1069 92 (:REWRITE <<-IMPLIES-LEXORDER))
 (704 178 (:REWRITE <<-TRICHOTOMY))
 (530 530 (:TYPE-PRESCRIPTION <<))
 (211 146 (:REWRITE DEFAULT-CAR))
 (178 178 (:REWRITE <<-TRANSITIVE))
 (174 87 (:REWRITE <<-ASYMMETRIC))
 (121 76 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE <<-IRREFLEXIVE))
 )
(INSERT-IN
 (534 45 (:REWRITE <<-IMPLIES-LEXORDER))
 (354 89 (:REWRITE <<-TRICHOTOMY))
 (266 266 (:TYPE-PRESCRIPTION <<))
 (108 91 (:REWRITE DEFAULT-CAR))
 (89 89 (:REWRITE <<-TRANSITIVE))
 (88 44 (:REWRITE <<-ASYMMETRIC))
 (60 49 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE <<-IRREFLEXIVE))
 )
(INSERT-SORT-REMOVE
 (1363 65 (:DEFINITION INSERT))
 (910 65 (:DEFINITION <<=))
 (780 65 (:REWRITE <<-IMPLIES-LEXORDER))
 (520 130 (:REWRITE <<-TRICHOTOMY))
 (390 390 (:TYPE-PRESCRIPTION <<))
 (256 230 (:REWRITE DEFAULT-CAR))
 (184 165 (:REWRITE DEFAULT-CDR))
 (130 130 (:REWRITE <<-TRANSITIVE))
 (130 65 (:REWRITE <<-ASYMMETRIC))
 (65 65 (:TYPE-PRESCRIPTION LEXORDER))
 (65 65 (:REWRITE LEXORDER-TRANSITIVE))
 )
(SORT-CANONICAL
 (630 30 (:DEFINITION INSERT))
 (420 30 (:DEFINITION <<=))
 (360 30 (:REWRITE <<-IMPLIES-LEXORDER))
 (282 38 (:REWRITE PERM-SYMMETRIC))
 (240 60 (:REWRITE <<-TRICHOTOMY))
 (203 203 (:REWRITE DEFAULT-CAR))
 (180 180 (:TYPE-PRESCRIPTION <<))
 (152 152 (:REWRITE DEFAULT-CDR))
 (140 28 (:DEFINITION REMOVE-EL))
 (88 22 (:DEFINITION IN))
 (60 60 (:REWRITE <<-TRANSITIVE))
 (60 30 (:REWRITE <<-ASYMMETRIC))
 (44 4 (:REWRITE REMOVE-EL-SWAP))
 (38 38 (:REWRITE PERM-TRANSITIVE))
 (30 30 (:TYPE-PRESCRIPTION LEXORDER))
 (30 30 (:REWRITE LEXORDER-TRANSITIVE))
 (15 15 (:REWRITE CAR-PERM))
 (4 4 (:REWRITE REMOVE-EL-IN))
 )
(MAIN
 (226 28 (:REWRITE PERM-SYMMETRIC))
 (84 4 (:DEFINITION INSERT))
 (72 72 (:REWRITE DEFAULT-CAR))
 (67 11 (:DEFINITION IN))
 (63 11 (:DEFINITION REMOVE-EL))
 (57 57 (:REWRITE DEFAULT-CDR))
 (56 4 (:DEFINITION <<=))
 (48 4 (:REWRITE <<-IMPLIES-LEXORDER))
 (32 8 (:REWRITE <<-TRICHOTOMY))
 (24 24 (:TYPE-PRESCRIPTION <<))
 (10 10 (:REWRITE CAR-PERM))
 (8 8 (:REWRITE <<-TRANSITIVE))
 (8 4 (:REWRITE <<-ASYMMETRIC))
 (4 4 (:TYPE-PRESCRIPTION LEXORDER))
 (4 4 (:REWRITE LEXORDER-TRANSITIVE))
 )
(MAIN2
 (162 14 (:REWRITE <<-IMPLIES-LEXORDER))
 (106 27 (:REWRITE <<-TRICHOTOMY))
 (80 80 (:TYPE-PRESCRIPTION <<))
 (51 50 (:REWRITE DEFAULT-CAR))
 (48 47 (:REWRITE DEFAULT-CDR))
 (45 2 (:DEFINITION PERM))
 (36 5 (:REWRITE PERM-SYMMETRIC))
 (27 27 (:REWRITE <<-TRANSITIVE))
 (26 13 (:REWRITE <<-ASYMMETRIC))
 (10 2 (:DEFINITION REMOVE-EL))
 (9 2 (:DEFINITION IN))
 (6 6 (:TYPE-PRESCRIPTION IN))
 (5 5 (:REWRITE PERM-TRANSITIVE))
 (2 2 (:REWRITE CAR-PERM))
 (1 1 (:REWRITE <<-IRREFLEXIVE))
 )
(MAIN3
 (48 4 (:REWRITE <<-IMPLIES-LEXORDER))
 (42 2 (:DEFINITION INSERT))
 (32 8 (:REWRITE <<-TRICHOTOMY))
 (24 24 (:TYPE-PRESCRIPTION <<))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE <<-TRANSITIVE))
 (8 4 (:REWRITE <<-ASYMMETRIC))
 (4 4 (:REWRITE LEXORDER-TRANSITIVE))
 )
