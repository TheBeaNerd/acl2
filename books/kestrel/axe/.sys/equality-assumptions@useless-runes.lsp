(REPLACE-FUN-CALL-USING-EQUALITY-PAIRS
 (2008 8 (:DEFINITION PSEUDO-TERMP))
 (830 415 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (808 24 (:DEFINITION LENGTH))
 (777 5 (:LINEAR LARGEST-NON-QUOTEP-BOUND))
 (742 62 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (672 32 (:DEFINITION LEN))
 (672 19 (:DEFINITION NATP))
 (639 205 (:REWRITE DEFAULT-CAR))
 (526 70 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (457 15 (:DEFINITION NAT-LISTP))
 (424 8 (:DEFINITION SYMBOL-LISTP))
 (422 14 (:REWRITE USE-ALL-<-FOR-CAR))
 (415 415 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (415 415 (:TYPE-PRESCRIPTION ARRAY1P))
 (361 15 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (335 20 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (324 196 (:REWRITE USE-ALL-CONSP))
 (196 196 (:REWRITE USE-ALL-CONSP-2))
 (171 10 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (170 62 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (169 145 (:REWRITE DEFAULT-CDR))
 (161 10 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (128 128 (:TYPE-PRESCRIPTION MEMBERP))
 (124 62 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (118 118 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (110 5 (:LINEAR LARGEST-NON-QUOTEP-BOUND-ALT))
 (108 108 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (100 100 (:TYPE-PRESCRIPTION NAT-LISTP))
 (95 39 (:REWRITE DEFAULT-+-2))
 (80 16 (:REWRITE ALL-CONSP-OF-CDR))
 (72 72 (:TYPE-PRESCRIPTION LEN))
 (70 70 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (66 66 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (64 64 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (64 64 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (64 64 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (62 62 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (62 62 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (62 62 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (55 55 (:TYPE-PRESCRIPTION ALL-NATP))
 (48 24 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (45 5 (:LINEAR <=-OF--1-AND-LARGEST-NON-QUOTEP-LINEAR))
 (39 39 (:REWRITE DEFAULT-+-1))
 (38 38 (:TYPE-PRESCRIPTION ALL-<))
 (36 36 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (35 15 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (34 34 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (34 17 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-CONSP-CHEAP))
 (32 32 (:TYPE-PRESCRIPTION NATP))
 (32 17 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-MYQUOTEP-CHEAP))
 (31 9 (:REWRITE ALL-MYQUOTEP-WHEN-NOT-CONSP))
 (30 15 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (28 14 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (25 25 (:REWRITE USE-ALL-NATP-2))
 (25 25 (:REWRITE USE-ALL-NATP))
 (25 25 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (24 24 (:TYPE-PRESCRIPTION AXE-TREEP))
 (24 24 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (21 7 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (20 10 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (20 10 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (20 10 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (20 5 (:DEFINITION NTH))
 (19 19 (:REWRITE USE-ALL-<=-2))
 (19 19 (:REWRITE USE-ALL-<=))
 (19 19 (:REWRITE USE-ALL-<-2))
 (19 19 (:REWRITE USE-ALL-<))
 (19 19 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (19 19 (:REWRITE DEFAULT-<-2))
 (19 19 (:REWRITE DEFAULT-<-1))
 (19 19 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (19 19 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (16 16 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (16 16 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (16 16 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (15 15 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (15 15 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (14 14 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (10 10 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (10 10 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (10 10 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP))
 (10 10 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (10 10 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (10 10 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (10 10 (:REWRITE ALL-<-TRANSITIVE))
 (8 8 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (8 8 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (8 8 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (8 8 (:REWRITE DEFAULT-COERCE-2))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 (8 4 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (7 7 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:LINEAR <-OF-LARGEST-NON-QUOTEP))
 )
(AXE-TREEP-OF-REPLACE-FUN-CALL-USING-EQUALITY-PAIRS
 (6684 382 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (4804 702 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (4012 1520 (:REWRITE DEFAULT-CAR))
 (3804 1616 (:REWRITE DEFAULT-CDR))
 (1935 320 (:REWRITE ALL-CONSP-OF-CDR))
 (1404 1404 (:TYPE-PRESCRIPTION ALL-CONSP))
 (1291 1291 (:REWRITE USE-ALL-CONSP-2))
 (1291 1291 (:REWRITE USE-ALL-CONSP))
 (1146 382 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (904 27 (:REWRITE AXE-TREE-LISTP-WHEN-ALL-DARGP))
 (864 27 (:REWRITE AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (811 14 (:REWRITE AXE-TREE-LISTP-OF-CDR-2))
 (764 764 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (764 382 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (757 28 (:DEFINITION PSEUDO-TERM-LISTP))
 (702 702 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (624 40 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (604 29 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (574 287 (:REWRITE DEFAULT-+-2))
 (566 566 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (559 559 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (559 559 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (559 559 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (408 408 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (382 382 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (382 382 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (382 382 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (319 157 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (315 10 (:DEFINITION DARGP))
 (287 287 (:REWRITE DEFAULT-+-1))
 (190 190 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (185 17 (:DEFINITION NATP))
 (157 157 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (151 151 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (148 148 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (118 118 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (104 13 (:REWRITE ALL-DARGP-OF-CDR))
 (102 23 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (98 98 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (80 80 (:TYPE-PRESCRIPTION ALL-DARGP))
 (80 40 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (68 68 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (65 65 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (61 29 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP))
 (57 57 (:REWRITE DEFAULT-COERCE-2))
 (57 57 (:REWRITE DEFAULT-COERCE-1))
 (40 40 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (40 40 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (40 40 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (39 13 (:REWRITE PSEUDO-TERMP-OF-CDR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
 (31 30 (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP))
 (30 30 (:REWRITE AXE-TREEP-WHEN-BOUNDED-AXE-TREEP))
 (29 29 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP-CHEAP))
 (28 27 (:REWRITE AXE-TREEP-WHEN-SYMBOLP-CHEAP))
 (26 13 (:REWRITE SYMBOLP-OF-CDAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (25 25 (:TYPE-PRESCRIPTION DARGP))
 (25 8 (:REWRITE USE-ALL-EQUALITY-PAIRP-FOR-CAR))
 (24 24 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (24 24 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (24 24 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (24 23 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (23 23 (:REWRITE USE-ALL-DARGP-2))
 (23 23 (:REWRITE USE-ALL-DARGP))
 (23 23 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (21 10 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (20 10 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (18 18 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (17 17 (:REWRITE USE-ALL-NATP-2))
 (17 17 (:REWRITE USE-ALL-NATP))
 (17 17 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (16 16 (:REWRITE USE-ALL-<=-2))
 (16 16 (:REWRITE USE-ALL-<=))
 (16 16 (:REWRITE USE-ALL-<-2))
 (16 16 (:REWRITE USE-ALL-<))
 (16 16 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (16 16 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (16 16 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (13 13 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (13 13 (:TYPE-PRESCRIPTION MYQUOTEP))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:REWRITE USE-ALL-EQUALITY-PAIRP-2))
 (8 8 (:REWRITE USE-ALL-EQUALITY-PAIRP))
 (3 3 (:TYPE-PRESCRIPTION QUOTEP))
 )
(BOUNDED-AXE-TREEP-OF-REPLACE-FUN-CALL-USING-EQUALITY-PAIRS
 (6732 33 (:DEFINITION PSEUDO-TERMP))
 (2856 99 (:DEFINITION LENGTH))
 (2295 132 (:DEFINITION LEN))
 (1736 116 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (1417 33 (:DEFINITION SYMBOL-LISTP))
 (1165 653 (:REWRITE DEFAULT-CAR))
 (1064 200 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (970 632 (:REWRITE DEFAULT-CDR))
 (522 522 (:TYPE-PRESCRIPTION LEN))
 (485 485 (:REWRITE USE-ALL-CONSP-2))
 (485 485 (:REWRITE USE-ALL-CONSP))
 (420 84 (:REWRITE ALL-CONSP-OF-CDR))
 (400 400 (:TYPE-PRESCRIPTION ALL-CONSP))
 (348 116 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (264 264 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (264 264 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (264 264 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (264 132 (:REWRITE DEFAULT-+-2))
 (238 238 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (232 232 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (232 116 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (200 200 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (156 77 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (138 138 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (132 132 (:REWRITE DEFAULT-+-1))
 (116 116 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (116 116 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (116 116 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (99 99 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (93 93 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (77 77 (:TYPE-PRESCRIPTION AXE-TREEP))
 (77 77 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (74 74 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (66 66 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (63 63 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (55 26 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP))
 (44 44 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (33 33 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (33 33 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (33 33 (:REWRITE DEFAULT-COERCE-2))
 (33 33 (:REWRITE DEFAULT-COERCE-1))
 (33 11 (:REWRITE PSEUDO-TERMP-OF-CDR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
 (29 29 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (26 26 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP-CHEAP))
 (23 7 (:REWRITE USE-ALL-EQUALITY-PAIRP-FOR-CAR))
 (22 11 (:REWRITE SYMBOLP-OF-CDAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (14 7 (:REWRITE BOUNDED-AXE-TREEP-WHEN-DARGP-LESS-THAN-CHEAP))
 (11 11 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (7 7 (:TYPE-PRESCRIPTION DARGP-LESS-THAN))
 (7 7 (:REWRITE USE-ALL-EQUALITY-PAIRP-2))
 (7 7 (:REWRITE USE-ALL-EQUALITY-PAIRP))
 )
(REPLACE-VAR-USING-EQUALITY-PAIRS
 (25 5 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (24 9 (:REWRITE DEFAULT-CAR))
 (15 5 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (10 10 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (10 10 (:TYPE-PRESCRIPTION ALL-CONSP))
 (10 5 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (7 7 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (6 6 (:REWRITE USE-ALL-CONSP-2))
 (6 6 (:REWRITE USE-ALL-CONSP))
 (5 5 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (5 5 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (5 5 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (5 5 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (4 4 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (4 4 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (4 2 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (3 3 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(AXE-TREEP-OF-REPLACE-VAR-USING-EQUALITY-PAIRS
 (6679 381 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (4803 701 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (3995 1518 (:REWRITE DEFAULT-CAR))
 (3798 1616 (:REWRITE DEFAULT-CDR))
 (1935 320 (:REWRITE ALL-CONSP-OF-CDR))
 (1402 1402 (:TYPE-PRESCRIPTION ALL-CONSP))
 (1290 1290 (:REWRITE USE-ALL-CONSP-2))
 (1290 1290 (:REWRITE USE-ALL-CONSP))
 (1143 381 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (904 27 (:REWRITE AXE-TREE-LISTP-WHEN-ALL-DARGP))
 (864 27 (:REWRITE AXE-TREE-LISTP-WHEN-PSEUDO-TERM-LISTP))
 (811 14 (:REWRITE AXE-TREE-LISTP-OF-CDR-2))
 (762 762 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (762 381 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (757 28 (:DEFINITION PSEUDO-TERM-LISTP))
 (701 701 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (624 40 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (581 29 (:REWRITE AXE-TREEP-WHEN-DARGP))
 (574 287 (:REWRITE DEFAULT-+-2))
 (565 565 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (559 559 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (559 559 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (559 559 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (407 407 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (381 381 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (381 381 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (381 381 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (310 157 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (295 10 (:DEFINITION DARGP))
 (287 287 (:REWRITE DEFAULT-+-1))
 (206 206 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (190 190 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (180 17 (:DEFINITION NATP))
 (157 157 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (151 151 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (148 148 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (118 118 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (104 13 (:REWRITE ALL-DARGP-OF-CDR))
 (101 23 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (98 98 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (80 80 (:TYPE-PRESCRIPTION ALL-DARGP))
 (80 40 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (68 68 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (61 29 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP))
 (57 57 (:REWRITE DEFAULT-COERCE-2))
 (57 57 (:REWRITE DEFAULT-COERCE-1))
 (40 40 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (40 40 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (40 40 (:REWRITE ALL-DARGP-WHEN-BOUNDED-DARG-LISTP))
 (39 13 (:REWRITE PSEUDO-TERMP-OF-CDR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
 (30 30 (:REWRITE AXE-TREEP-WHEN-NOT-CONSP-AND-NOT-SYMBOLP-CHEAP))
 (30 30 (:REWRITE AXE-TREEP-WHEN-BOUNDED-AXE-TREEP))
 (29 29 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP-CHEAP))
 (27 27 (:REWRITE AXE-TREEP-WHEN-SYMBOLP-CHEAP))
 (26 13 (:REWRITE SYMBOLP-OF-CDAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (25 25 (:TYPE-PRESCRIPTION DARGP))
 (25 8 (:REWRITE USE-ALL-EQUALITY-PAIRP-FOR-CAR))
 (24 24 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (24 24 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (24 24 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (23 23 (:REWRITE USE-ALL-DARGP-2))
 (23 23 (:REWRITE USE-ALL-DARGP))
 (23 23 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (23 23 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (20 10 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (20 10 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (18 18 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (17 17 (:REWRITE USE-ALL-NATP-2))
 (17 17 (:REWRITE USE-ALL-NATP))
 (17 17 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (16 16 (:REWRITE USE-ALL-<=-2))
 (16 16 (:REWRITE USE-ALL-<=))
 (16 16 (:REWRITE USE-ALL-<-2))
 (16 16 (:REWRITE USE-ALL-<))
 (16 16 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (16 16 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-<-1))
 (16 16 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (16 16 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (13 13 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (13 13 (:TYPE-PRESCRIPTION MYQUOTEP))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:REWRITE USE-ALL-EQUALITY-PAIRP-2))
 (8 8 (:REWRITE USE-ALL-EQUALITY-PAIRP))
 (3 3 (:TYPE-PRESCRIPTION QUOTEP))
 )
(BOUNDED-AXE-TREEP-OF-REPLACE-VAR-USING-EQUALITY-PAIRS
 (6725 33 (:DEFINITION PSEUDO-TERMP))
 (2856 99 (:DEFINITION LENGTH))
 (2295 132 (:DEFINITION LEN))
 (1731 115 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (1416 33 (:DEFINITION SYMBOL-LISTP))
 (1148 651 (:REWRITE DEFAULT-CAR))
 (1063 199 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (970 632 (:REWRITE DEFAULT-CDR))
 (522 522 (:TYPE-PRESCRIPTION LEN))
 (484 484 (:REWRITE USE-ALL-CONSP-2))
 (484 484 (:REWRITE USE-ALL-CONSP))
 (420 84 (:REWRITE ALL-CONSP-OF-CDR))
 (398 398 (:TYPE-PRESCRIPTION ALL-CONSP))
 (345 115 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (264 264 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (264 264 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (264 264 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (264 132 (:REWRITE DEFAULT-+-2))
 (237 237 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (230 230 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (230 115 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (199 199 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (154 77 (:REWRITE SYMBOLP-OF-CAR-WHEN-AXE-TREEP-CHEAP))
 (137 137 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (132 132 (:REWRITE DEFAULT-+-1))
 (115 115 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (115 115 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (115 115 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (99 99 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (93 93 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (77 77 (:TYPE-PRESCRIPTION AXE-TREEP))
 (77 77 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (74 74 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (66 66 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (63 63 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (55 26 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP))
 (54 54 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (44 44 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (33 33 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (33 33 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (33 33 (:REWRITE DEFAULT-COERCE-2))
 (33 33 (:REWRITE DEFAULT-COERCE-1))
 (33 11 (:REWRITE PSEUDO-TERMP-OF-CDR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP))
 (26 26 (:REWRITE ALL-EQUALITY-PAIRP-WHEN-NOT-CONSP-CHEAP))
 (23 7 (:REWRITE USE-ALL-EQUALITY-PAIRP-FOR-CAR))
 (22 11 (:REWRITE SYMBOLP-OF-CDAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (14 7 (:REWRITE BOUNDED-AXE-TREEP-WHEN-DARGP-LESS-THAN-CHEAP))
 (11 11 (:TYPE-PRESCRIPTION WEAK-DAGP-AUX))
 (7 7 (:TYPE-PRESCRIPTION DARGP-LESS-THAN))
 (7 7 (:REWRITE USE-ALL-EQUALITY-PAIRP-2))
 (7 7 (:REWRITE USE-ALL-EQUALITY-PAIRP))
 )
