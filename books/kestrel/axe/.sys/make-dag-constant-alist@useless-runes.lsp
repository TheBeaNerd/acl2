(MAKE-DAG-CONSTANT-ALIST-AUX
 (612 337 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (337 337 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (160 160 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (45 27 (:REWRITE DEFAULT-<-1))
 (34 2 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (33 27 (:REWRITE DEFAULT-<-2))
 (30 10 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (27 27 (:REWRITE USE-ALL-<=-2))
 (27 27 (:REWRITE USE-ALL-<=))
 (27 27 (:REWRITE USE-ALL-<-2))
 (27 27 (:REWRITE USE-ALL-<))
 (27 27 (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (24 3 (:REWRITE NOT-EQUAL-OF-CAR-AND-QUOTE-WHEN-LEN-WRONG-AND-PSEUDO-DAG-ARRAYP-AUX))
 (20 10 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DIMENSIONS))
 (18 15 (:REWRITE DEFAULT-+-1))
 (18 9 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (18 2 (:REWRITE CONSP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE-IFF))
 (16 8 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (15 15 (:REWRITE DEFAULT-+-2))
 (14 1 (:REWRITE ALL-DARGP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (12 12 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (12 3 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (11 11 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (10 10 (:REWRITE USE-ALL-RATIONALP-2))
 (10 10 (:REWRITE USE-ALL-RATIONALP))
 (10 10 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (8 2 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (6 4 (:REWRITE USE-ALL-CONSP))
 (6 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE USE-ALL-NATP-2))
 (5 5 (:REWRITE USE-ALL-NATP))
 (5 5 (:REWRITE NATP-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE USE-ALL-CONSP-2))
 (3 3 (:REWRITE QUOTE-LEMMA-FOR-ALL-DARGP-LESS-THAN-GEN-ALT))
 (3 3 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (2 2 (:TYPE-PRESCRIPTION MEMBERP))
 (2 2 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 )
(DAG-CONSTANT-ALISTP-OF-MAKE-DAG-CONSTANT-ALIST-AUX
 (563 18 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (212 53 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (166 83 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (144 72 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (144 72 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-SIMPLE))
 (136 17 (:REWRITE NOT-EQUAL-OF-CAR-AND-QUOTE-WHEN-LEN-WRONG-AND-PSEUDO-DAG-ARRAYP-AUX))
 (135 45 (:REWRITE FOLD-CONSTS-IN-+))
 (135 18 (:REWRITE CONSP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE-IFF))
 (133 133 (:REWRITE DEFAULT-+-2))
 (133 133 (:REWRITE DEFAULT-+-1))
 (117 117 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (108 18 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (106 53 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (87 51 (:REWRITE DEFAULT-<-2))
 (87 51 (:REWRITE DEFAULT-<-1))
 (83 83 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (72 72 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (72 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (68 17 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (58 34 (:REWRITE USE-ALL-CONSP))
 (53 53 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (53 53 (:TYPE-PRESCRIPTION ARRAY1P))
 (51 51 (:REWRITE USE-ALL-<=-2))
 (51 51 (:REWRITE USE-ALL-<=))
 (51 51 (:REWRITE USE-ALL-<-2))
 (51 51 (:REWRITE USE-ALL-<))
 (51 51 (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (34 34 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (34 34 (:REWRITE USE-ALL-CONSP-2))
 (24 24 (:TYPE-PRESCRIPTION MEMBERP))
 (24 24 (:REWRITE USE-ALL-RATIONALP-2))
 (24 24 (:REWRITE USE-ALL-RATIONALP))
 (21 21 (:REWRITE DEFAULT-CAR))
 (19 19 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (19 19 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (18 18 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (17 17 (:REWRITE QUOTE-LEMMA-FOR-ALL-DARGP-LESS-THAN-GEN-ALT))
 (17 17 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (17 17 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (15 15 (:REWRITE USE-ALL-NATP-2))
 (15 15 (:REWRITE USE-ALL-NATP))
 (15 15 (:REWRITE NATP-WHEN-ALL-DARGP-LESS-THAN-GEN))
 )
(ALL-<-OF-STRIP-CDRS-OF-MAKE-DAG-CONSTANT-ALIST-AUX
 (5126 56 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2514 24 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (1925 45 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (1748 40 (:DEFINITION NAT-LISTP))
 (1466 48 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (1430 195 (:REWRITE DEFAULT-CDR))
 (1288 113 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (966 48 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (948 24 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (613 37 (:REWRITE NOT-EQUAL-OF-CAR-AND-QUOTE-WHEN-LEN-WRONG-AND-PSEUDO-DAG-ARRAYP-AUX))
 (460 115 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (407 289 (:REWRITE USE-ALL-CONSP))
 (399 75 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (348 329 (:REWRITE DEFAULT-+-2))
 (345 115 (:REWRITE FOLD-CONSTS-IN-+))
 (339 171 (:REWRITE USE-ALL-<))
 (329 329 (:REWRITE DEFAULT-+-1))
 (326 51 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (315 113 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (304 152 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (304 152 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-SIMPLE))
 (298 149 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (297 38 (:REWRITE CONSP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE-IFF))
 (294 294 (:TYPE-PRESCRIPTION NAT-LISTP))
 (289 289 (:REWRITE USE-ALL-CONSP-2))
 (286 286 (:TYPE-PRESCRIPTION MEMBERP))
 (286 36 (:REWRITE USE-ALL-<-FOR-CAR))
 (234 36 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (230 115 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (228 2 (:REWRITE ALL-NATP-OF-CONS))
 (225 75 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (213 171 (:REWRITE DEFAULT-<-2))
 (213 171 (:REWRITE DEFAULT-<-1))
 (201 51 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (175 159 (:REWRITE DEFAULT-CAR))
 (171 171 (:REWRITE USE-ALL-<-2))
 (171 171 (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (169 169 (:REWRITE USE-ALL-<=-2))
 (169 169 (:REWRITE USE-ALL-<=))
 (152 152 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (152 122 (:TYPE-PRESCRIPTION MAKE-DAG-CONSTANT-ALIST-AUX))
 (150 150 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (150 75 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (142 142 (:TYPE-PRESCRIPTION ALL-NATP))
 (115 115 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (115 115 (:TYPE-PRESCRIPTION ARRAY1P))
 (102 34 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (100 100 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (96 48 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (84 45 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (75 75 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (75 75 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (75 75 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (75 75 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (72 36 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (72 36 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (68 48 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (59 59 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (59 59 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (55 55 (:REWRITE USE-ALL-NATP-2))
 (55 55 (:REWRITE USE-ALL-NATP))
 (55 55 (:REWRITE NATP-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (50 50 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (39 39 (:REWRITE USE-ALL-RATIONALP-2))
 (39 39 (:REWRITE USE-ALL-RATIONALP))
 (38 38 (:REWRITE QUOTE-LEMMA-FOR-ALL-DARGP-LESS-THAN-GEN-ALT))
 (38 38 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (36 36 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (36 36 (:REWRITE NOT-<-OF-CAR-WHEN-ALL-DARGP-LESS-THAN-2))
 (36 36 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-DARGP-LESS-THAN))
 (23 23 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 (23 1 (:REWRITE LEN-OF-AREF1-WHEN-QUOTEP-AND-PSEUDO-DAG-ARRAYP-AUX))
 (21 21 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (21 21 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (8 1 (:DEFINITION LEN))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 )
(BOUNDED-DAG-CONSTANT-ALISTP-OF-MAKE-DAG-CONSTANT-ALIST-AUX
 (65 3 (:DEFINITION STRIP-CDRS))
 (51 6 (:REWRITE DEFAULT-CDR))
 (27 1 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (15 3 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (9 3 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (7 7 (:REWRITE USE-ALL-CONSP-2))
 (7 7 (:REWRITE USE-ALL-CONSP))
 (6 6 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (6 6 (:TYPE-PRESCRIPTION ALL-CONSP))
 (6 3 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (4 1 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (4 1 (:REWRITE DEFAULT-+-2))
 (3 3 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (3 3 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (3 3 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (3 3 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (3 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (2 2 (:TYPE-PRESCRIPTION MAKE-DAG-CONSTANT-ALIST-AUX))
 (2 1 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE USE-ALL-RATIONALP-2))
 (1 1 (:REWRITE USE-ALL-RATIONALP))
 (1 1 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (1 1 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE BOUNDED-DAG-CONSTANT-ALISTP-MONOTONE))
 (1 1 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (1 1 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (1 1 (:REWRITE ALL-<-TRANSITIVE))
 )
(MAKE-DAG-CONSTANT-ALIST-AUX-BASE
 (190 6 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (60 20 (:REWRITE FOLD-CONSTS-IN-+))
 (54 54 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-AUX))
 (54 54 (:REWRITE DEFAULT-+-2))
 (54 54 (:REWRITE DEFAULT-+-1))
 (48 24 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (48 24 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-SIMPLE))
 (48 12 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (48 6 (:REWRITE NOT-EQUAL-OF-CAR-AND-QUOTE-WHEN-LEN-WRONG-AND-PSEUDO-DAG-ARRAYP-AUX))
 (48 6 (:REWRITE CONSP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE-IFF))
 (36 36 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP))
 (36 18 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (36 6 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (24 12 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (24 6 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (22 22 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (18 18 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (16 12 (:REWRITE USE-ALL-CONSP))
 (14 8 (:REWRITE DEFAULT-<-2))
 (12 12 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (12 12 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (12 12 (:TYPE-PRESCRIPTION ARRAY1P))
 (12 12 (:REWRITE USE-ALL-CONSP-2))
 (10 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE USE-ALL-<=-2))
 (8 8 (:REWRITE USE-ALL-<=))
 (8 8 (:REWRITE USE-ALL-<-2))
 (8 8 (:REWRITE USE-ALL-<))
 (8 8 (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (8 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE QUOTE-LEMMA-FOR-ALL-DARGP-LESS-THAN-GEN-ALT))
 (6 6 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (6 6 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 4 (:TYPE-PRESCRIPTION MEMBERP))
 (2 2 (:REWRITE USE-ALL-RATIONALP-2))
 (2 2 (:REWRITE USE-ALL-RATIONALP))
 (2 2 (:REWRITE USE-ALL-NATP-2))
 (2 2 (:REWRITE USE-ALL-NATP))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE NATP-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(MAKE-DAG-CONSTANT-ALIST-AUX-OF-ASET1-EXPANDABLE
 (6624 219 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (5384 2623 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (2861 137 (:REWRITE CONSP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE-IFF))
 (2623 2623 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (1832 1828 (:REWRITE DEFAULT-+-2))
 (1828 1828 (:REWRITE DEFAULT-+-1))
 (1671 118 (:REWRITE NOT-EQUAL-OF-CAR-AND-QUOTE-WHEN-LEN-WRONG-AND-PSEUDO-DAG-ARRAYP-AUX))
 (1324 524 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (971 419 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (966 69 (:REWRITE PSEUDO-DAG-ARRAYP-OF-ASET1-EXPANDABLE))
 (805 219 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (750 382 (:REWRITE USE-ALL-CONSP))
 (645 645 (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (644 640 (:REWRITE DEFAULT-<-2))
 (640 640 (:REWRITE USE-ALL-<-2))
 (640 640 (:REWRITE USE-ALL-<))
 (640 640 (:REWRITE DEFAULT-<-1))
 (636 636 (:REWRITE USE-ALL-<=-2))
 (636 636 (:REWRITE USE-ALL-<=))
 (589 69 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-OF-ASET1-EXPANDABLE))
 (573 126 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (560 280 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-SIMPLE))
 (524 524 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (490 245 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (414 69 (:REWRITE PSEUDO-DAG-ARRAYP-OF-ASET1-EXPANDABLE-SPECIAL))
 (382 382 (:REWRITE USE-ALL-CONSP-2))
 (368 368 (:TYPE-PRESCRIPTION MEMBERP))
 (252 252 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (210 201 (:REWRITE DEFAULT-CAR))
 (195 126 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (181 181 (:REWRITE QUOTE-LEMMA-FOR-ALL-DARGP-LESS-THAN-GEN-ALT))
 (164 4 (:LINEAR <-OF-NTH-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-LINEAR))
 (136 8 (:DEFINITION NTH))
 (126 126 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (102 20 (:REWRITE ALL-CONSP-OF-CDR))
 (80 4 (:DEFINITION LEN))
 (69 69 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-OF-ASET1-EXPANDABLE-SPECIAL))
 (67 58 (:REWRITE DEFAULT-CDR))
 (62 62 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (32 4 (:LINEAR NONNEG-OF-NTH-OF-DARGS-OF-AREF1))
 (32 4 (:LINEAR <-OF-NTH-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (26 26 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (24 24 (:TYPE-PRESCRIPTION LEN))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (8 8 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (8 8 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE CAR-OF-DARGS-BECOMES-NTH-0-OF-DARGS))
 (4 4 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (4 4 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 )
(MAKE-DAG-CONSTANT-ALIST)
(DAG-CONSTANT-ALISTP-OF-MAKE-DAG-CONSTANT-ALIST)
(MAKE-DAG-CONSTANT-ALIST-OF-0)
(BOUNDED-DAG-CONSTANT-ALISTP-OF-MAKE-DAG-CONSTANT-ALIST
 (52 52 (:TYPE-PRESCRIPTION NATP))
 (52 26 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (52 26 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (29 2 (:REWRITE NOT-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP))
 (15 15 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (8 2 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (5 3 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE USE-ALL-<=-2))
 (3 3 (:REWRITE USE-ALL-<=))
 (3 3 (:REWRITE USE-ALL-<-2))
 (3 3 (:REWRITE USE-ALL-<))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (2 2 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ARRAY1P-WHEN-PSEUDO-DAG-ARRAYP))
 (2 2 (:LINEAR ARRAY2P-LINEAR))
 (1 1 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 )
(ALL-<-OF-STRIP-CDRS-OF-MAKE-DAG-CONSTANT-ALIST
 (52 52 (:TYPE-PRESCRIPTION NATP))
 (52 26 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (52 26 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (29 2 (:REWRITE NOT-<-OF-ALEN1-WHEN-PSEUDO-DAG-ARRAYP))
 (23 1 (:DEFINITION STRIP-CDRS))
 (17 2 (:REWRITE DEFAULT-CDR))
 (15 15 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (8 2 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (5 3 (:REWRITE DEFAULT-<-1))
 (5 1 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (4 4 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE USE-ALL-<=-2))
 (3 3 (:REWRITE USE-ALL-<=))
 (3 3 (:REWRITE USE-ALL-<-2))
 (3 3 (:REWRITE USE-ALL-<))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (3 1 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (2 2 (:TYPE-PRESCRIPTION MAKE-DAG-CONSTANT-ALIST-AUX))
 (2 2 (:TYPE-PRESCRIPTION ALL-CONSP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ARRAY1P-WHEN-PSEUDO-DAG-ARRAYP))
 (2 2 (:LINEAR ARRAY2P-LINEAR))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1 1 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (1 1 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (1 1 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (1 1 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 )
(MAKE-DAG-CONSTANT-ALIST-OF-ASET1-EXPANDABLE
 (180 4 (:DEFINITION MAKE-DAG-CONSTANT-ALIST-AUX))
 (104 52 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (70 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (52 52 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (52 52 (:TYPE-PRESCRIPTION ARRAY1P))
 (32 16 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (32 4 (:REWRITE NOT-EQUAL-OF-CAR-AND-QUOTE-WHEN-LEN-WRONG-AND-PSEUDO-DAG-ARRAYP-AUX))
 (28 4 (:REWRITE CONSP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE-IFF))
 (20 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (16 4 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (12 12 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (10 2 (:REWRITE ALL-CONSP-OF-CDR))
 (8 8 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (8 8 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-AUX))
 (8 8 (:REWRITE USE-ALL-CONSP-2))
 (8 8 (:REWRITE USE-ALL-CONSP))
 (6 6 (:REWRITE USE-ALL-<=-2))
 (6 6 (:REWRITE USE-ALL-<=))
 (6 6 (:REWRITE USE-ALL-<-2))
 (6 6 (:REWRITE USE-ALL-<))
 (6 6 (:REWRITE QUOTE-LEMMA-FOR-ALL-DARGP-LESS-THAN-GEN-ALT))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (5 5 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (4 4 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (4 4 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
