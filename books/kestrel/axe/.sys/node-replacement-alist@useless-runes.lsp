(NODE-REPLACEMENT-ALISTP
 (512 16 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (487 11 (:DEFINITION NAT-LISTP))
 (153 13 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (120 15 (:REWRITE USE-ALL-<-FOR-CAR))
 (103 46 (:REWRITE DEFAULT-CAR))
 (78 78 (:TYPE-PRESCRIPTION NAT-LISTP))
 (73 16 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (55 11 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (38 38 (:REWRITE USE-ALL-CONSP-2))
 (38 38 (:REWRITE USE-ALL-CONSP))
 (32 16 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (30 15 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (28 15 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (26 23 (:REWRITE DEFAULT-CDR))
 (23 16 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (22 22 (:TYPE-PRESCRIPTION ALL-CONSP))
 (22 11 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (21 21 (:REWRITE USE-ALL-<-2))
 (21 21 (:REWRITE USE-ALL-<))
 (21 21 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (21 21 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (21 21 (:REWRITE DEFAULT-<-2))
 (21 21 (:REWRITE DEFAULT-<-1))
 (15 15 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (15 15 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (15 15 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (15 15 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (15 15 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (15 15 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (15 15 (:REWRITE ALL-<-TRANSITIVE))
 (15 13 (:REWRITE USE-ALL-NATP))
 (13 13 (:REWRITE USE-ALL-NATP-2))
 (11 11 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (11 11 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (11 11 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION MEMBERP))
 )
(NODE-REPLACEMENT-ALISTP-OF-NIL
 (2 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (2 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (1 1 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 )
(NODE-REPLACEMENT-ALISTP-FORWARD-TO-EQLABLE-ALISTP
 (926 28 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (885 19 (:DEFINITION NAT-LISTP))
 (297 23 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (262 30 (:REWRITE USE-ALL-<-FOR-CAR))
 (161 85 (:REWRITE DEFAULT-CAR))
 (138 138 (:TYPE-PRESCRIPTION NAT-LISTP))
 (102 39 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (97 28 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (96 20 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (69 69 (:REWRITE USE-ALL-CONSP-2))
 (69 69 (:REWRITE USE-ALL-CONSP))
 (60 30 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (59 37 (:REWRITE DEFAULT-CDR))
 (56 28 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (53 39 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (52 27 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (48 39 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (47 39 (:REWRITE ALL-<-TRANSITIVE))
 (40 20 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (39 39 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (39 34 (:REWRITE DEFAULT-<-2))
 (39 28 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (38 38 (:TYPE-PRESCRIPTION ALL-CONSP))
 (38 34 (:REWRITE USE-ALL-<))
 (34 34 (:REWRITE USE-ALL-<-2))
 (34 34 (:REWRITE DEFAULT-<-1))
 (30 30 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (30 5 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (27 27 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (27 27 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (27 27 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (25 23 (:REWRITE USE-ALL-NATP))
 (23 23 (:REWRITE USE-ALL-NATP-2))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (19 19 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (19 19 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (14 7 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (14 7 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (9 9 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (9 9 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (7 7 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (7 7 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 (6 6 (:TYPE-PRESCRIPTION MEMBERP))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE CDR-CONS))
 (4 4 (:REWRITE CAR-CONS))
 (4 2 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (2 2 (:REWRITE DARGP-LESS-THAN-MONO))
 )
(NODE-REPLACEMENT-ALISTP-FORWARD-TO-ALISTP)
(NODE-REPLACEMENT-ALISTP-MONOTONE
 (105 7 (:DEFINITION STRIP-CARS))
 (83 20 (:REWRITE DEFAULT-CAR))
 (75 3 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (69 2 (:DEFINITION NAT-LISTP))
 (55 11 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (43 3 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (33 15 (:REWRITE DEFAULT-CDR))
 (33 1 (:DEFINITION NATP))
 (30 2 (:DEFINITION STRIP-CDRS))
 (28 28 (:REWRITE USE-ALL-CONSP-2))
 (28 28 (:REWRITE USE-ALL-CONSP))
 (22 22 (:TYPE-PRESCRIPTION ALL-CONSP))
 (22 11 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (22 2 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (19 1 (:REWRITE USE-ALL-<-FOR-CAR))
 (14 14 (:TYPE-PRESCRIPTION NAT-LISTP))
 (11 11 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (11 11 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (11 11 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (10 3 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (10 2 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (8 4 (:REWRITE USE-ALL-<))
 (6 6 (:TYPE-PRESCRIPTION MEMBERP))
 (6 4 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (6 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (5 4 (:REWRITE DEFAULT-<-1))
 (5 3 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE USE-ALL-<-2))
 (4 4 (:REWRITE NODE-REPLACEMENT-ALISTP-FORWARD-TO-ALISTP))
 (4 2 (:REWRITE USE-ALL-NATP))
 (4 2 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (4 2 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (3 2 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (2 2 (:REWRITE USE-ALL-NATP-2))
 (2 1 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (2 1 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (1 1 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 )
(DARGP-LESS-THAN-OF-CDR-OF-ASSOC-EQUAL-WHEN-NODE-REPLACEMENT-ALISTP
 (1318 40 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (1261 27 (:DEFINITION NAT-LISTP))
 (441 33 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (374 44 (:REWRITE USE-ALL-<-FOR-CAR))
 (318 150 (:REWRITE DEFAULT-CAR))
 (198 198 (:TYPE-PRESCRIPTION NAT-LISTP))
 (150 30 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (132 57 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (121 40 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (95 95 (:REWRITE USE-ALL-CONSP-2))
 (95 95 (:REWRITE USE-ALL-CONSP))
 (88 44 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (83 55 (:REWRITE DEFAULT-CDR))
 (80 40 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (76 39 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (72 58 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (70 57 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (68 54 (:REWRITE USE-ALL-<))
 (66 58 (:REWRITE ALL-<-TRANSITIVE))
 (64 54 (:REWRITE DEFAULT-<-2))
 (60 60 (:TYPE-PRESCRIPTION ALL-CONSP))
 (60 54 (:REWRITE DEFAULT-<-1))
 (60 30 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (58 58 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (55 40 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (54 54 (:REWRITE USE-ALL-<-2))
 (44 44 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (39 39 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (39 39 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (39 39 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (35 33 (:REWRITE USE-ALL-NATP))
 (33 33 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (33 33 (:REWRITE USE-ALL-NATP-2))
 (30 30 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (30 30 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (24 12 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (24 12 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (16 16 (:TYPE-PRESCRIPTION MEMBERP))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 14 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (14 14 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (14 7 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (12 12 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (12 12 (:REWRITE NODE-REPLACEMENT-ALISTP-FORWARD-TO-ALISTP))
 (12 12 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 (9 9 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (7 7 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (7 7 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (7 7 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (6 6 (:REWRITE CDR-CONS))
 (6 6 (:REWRITE CAR-CONS))
 (6 3 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 )
(DARGP-OF-CDR-OF-ASSOC-EQUAL-WHEN-NODE-REPLACEMENT-ALISTP
 (72 18 (:REWRITE DEFAULT-CAR))
 (60 4 (:DEFINITION STRIP-CARS))
 (57 2 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (54 1 (:DEFINITION NAT-LISTP))
 (45 9 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (34 2 (:DEFINITION ASSOC-EQUAL))
 (33 1 (:DEFINITION NATP))
 (31 13 (:REWRITE DEFAULT-CDR))
 (30 2 (:DEFINITION STRIP-CDRS))
 (22 22 (:REWRITE USE-ALL-CONSP-2))
 (22 22 (:REWRITE USE-ALL-CONSP))
 (22 2 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (22 2 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (19 1 (:REWRITE USE-ALL-<-FOR-CAR))
 (18 18 (:TYPE-PRESCRIPTION ALL-CONSP))
 (18 9 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (15 1 (:DEFINITION ALISTP))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (9 9 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (9 2 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (9 1 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (8 8 (:TYPE-PRESCRIPTION NAT-LISTP))
 (8 4 (:REWRITE USE-ALL-<))
 (6 4 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE ALL-<-TRANSITIVE))
 (6 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (5 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION MEMBERP))
 (4 4 (:REWRITE USE-ALL-<-2))
 (4 2 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 2 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (3 2 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE NODE-REPLACEMENT-ALISTP-FORWARD-TO-ALISTP))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2 1 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (2 1 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (2 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (2 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (2 1 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (1 1 (:REWRITE USE-ALL-NATP-2))
 (1 1 (:REWRITE USE-ALL-NATP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (1 1 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 )
(MYQUOTEP-OF-CDR-OF-ASSOC-EQUAL-WHEN-NODE-REPLACEMENT-ALISTP
 (148 40 (:REWRITE DEFAULT-CAR))
 (75 15 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (60 4 (:DEFINITION STRIP-CARS))
 (57 2 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (54 1 (:DEFINITION NAT-LISTP))
 (49 31 (:REWRITE DEFAULT-CDR))
 (41 41 (:REWRITE USE-ALL-CONSP-2))
 (41 41 (:REWRITE USE-ALL-CONSP))
 (33 1 (:DEFINITION NATP))
 (30 30 (:TYPE-PRESCRIPTION ALL-CONSP))
 (30 15 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (30 2 (:DEFINITION STRIP-CDRS))
 (22 2 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (22 2 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (19 1 (:REWRITE USE-ALL-<-FOR-CAR))
 (17 17 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (15 15 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (15 15 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (15 1 (:DEFINITION ALISTP))
 (9 2 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (9 1 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (8 8 (:TYPE-PRESCRIPTION NAT-LISTP))
 (6 2 (:REWRITE ALL-<-TRANSITIVE))
 (6 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (5 3 (:REWRITE USE-ALL-<))
 (4 4 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (4 4 (:REWRITE DARGP-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (4 4 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (4 3 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (4 2 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (3 3 (:REWRITE USE-ALL-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 2 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (3 2 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION MEMBERP))
 (2 2 (:REWRITE NODE-REPLACEMENT-ALISTP-FORWARD-TO-ALISTP))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2 1 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (2 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (2 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (2 1 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (1 1 (:REWRITE USE-ALL-NATP-2))
 (1 1 (:REWRITE USE-ALL-NATP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (1 1 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 )
(NATP-OF-CDR-OF-ASSOC-EQUAL-WHEN-NODE-REPLACEMENT-ALISTP
 (132 33 (:REWRITE DEFAULT-CAR))
 (70 14 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (60 4 (:DEFINITION STRIP-CARS))
 (57 2 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (54 1 (:DEFINITION NAT-LISTP))
 (40 22 (:REWRITE DEFAULT-CDR))
 (33 33 (:REWRITE USE-ALL-CONSP-2))
 (33 33 (:REWRITE USE-ALL-CONSP))
 (30 2 (:DEFINITION STRIP-CDRS))
 (28 28 (:TYPE-PRESCRIPTION ALL-CONSP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (22 2 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (22 2 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (19 1 (:REWRITE USE-ALL-<-FOR-CAR))
 (16 16 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (15 1 (:DEFINITION ALISTP))
 (14 14 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (14 14 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (9 2 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (9 1 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (8 8 (:TYPE-PRESCRIPTION NAT-LISTP))
 (6 4 (:REWRITE USE-ALL-<))
 (6 2 (:REWRITE ALL-<-TRANSITIVE))
 (6 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (5 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:TYPE-PRESCRIPTION MEMBERP))
 (4 4 (:REWRITE USE-ALL-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE USE-ALL-NATP))
 (4 2 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (4 2 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (3 3 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (3 3 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (3 2 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (3 2 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE USE-ALL-NATP-2))
 (2 2 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE NODE-REPLACEMENT-ALISTP-FORWARD-TO-ALISTP))
 (2 2 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2 1 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (2 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (2 1 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (2 1 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION MYQUOTEP))
 (1 1 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (1 1 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (1 1 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 )
(CONSP-OF-ASSOC-EQUAL-WHEN-NODE-REPLACEMENT-ALISTP)
(NODE-REPLACEMENT-ALISTP-OF-CONS-AND-CONS
 (180 6 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (172 4 (:DEFINITION NAT-LISTP))
 (114 32 (:REWRITE DEFAULT-CAR))
 (65 13 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (47 6 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (47 6 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (43 24 (:REWRITE DEFAULT-CDR))
 (35 35 (:REWRITE USE-ALL-CONSP-2))
 (35 35 (:REWRITE USE-ALL-CONSP))
 (32 32 (:TYPE-PRESCRIPTION STRIP-CARS))
 (29 3 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (28 28 (:TYPE-PRESCRIPTION NAT-LISTP))
 (26 26 (:TYPE-PRESCRIPTION ALL-CONSP))
 (26 13 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (24 3 (:REWRITE USE-ALL-<-FOR-CAR))
 (13 13 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (13 13 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (13 13 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (12 6 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (12 2 (:REWRITE BOUNDED-DARG-LISTP-WHEN-NOT-CONSP))
 (11 9 (:REWRITE USE-ALL-<))
 (11 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE USE-ALL-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 6 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (9 6 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (8 6 (:REWRITE USE-ALL-NATP))
 (7 7 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (7 7 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (6 6 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (6 6 (:REWRITE USE-ALL-NATP-2))
 (6 6 (:REWRITE NODE-REPLACEMENT-ALISTP-FORWARD-TO-ALISTP))
 (6 6 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (6 6 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (6 6 (:REWRITE ALL-<-TRANSITIVE))
 (6 3 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (6 3 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (6 3 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (6 3 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION MEMBERP))
 (4 2 (:REWRITE DARGP-LESS-THAN-WHEN-NATP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (3 3 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (3 3 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (3 3 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (3 3 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (3 3 (:REWRITE BOUNDED-DARG-LISTP-MONOTONE))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE NODE-REPLACEMENT-ALISTP-MONOTONE))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-QUOTEP-CHEAP))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-EQUAL-OF-CAR-AND-QUOTE))
 (2 2 (:REWRITE DARGP-LESS-THAN-WHEN-CONSP-CHEAP))
 (2 2 (:REWRITE DARGP-LESS-THAN-MONO))
 )
(ASSOC-IN-NODE-REPLACEMENT-ALIST)
