(ALL-RATIONALP-WHEN-RATIONAL-LISTP
 (25 11 (:REWRITE USE-ALL-RATIONALP))
 (14 14 (:TYPE-PRESCRIPTION MEMBERP))
 (14 11 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (13 13 (:REWRITE DEFAULT-CDR))
 (13 13 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE USE-ALL-RATIONALP-2))
 (11 11 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (3 3 (:REWRITE ALL-RATIONALP-OF-CDR))
 )
(RATIONAL-LISTP-OF-MV-NTH-0-OF-SPLIT-LIST-FAST-AUX
 (198 23 (:REWRITE ALL-RATIONALP-OF-CDR))
 (158 154 (:REWRITE DEFAULT-CDR))
 (109 92 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (101 95 (:REWRITE DEFAULT-CAR))
 (93 93 (:REWRITE USE-ALL-RATIONALP-2))
 (93 93 (:REWRITE USE-ALL-RATIONALP))
 (92 92 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (80 44 (:REWRITE DEFAULT-+-2))
 (44 44 (:REWRITE DEFAULT-+-1))
 (23 13 (:REWRITE DEFAULT-<-1))
 (19 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE USE-ALL-<=-2))
 (13 13 (:REWRITE USE-ALL-<=))
 (13 13 (:REWRITE USE-ALL-<-2))
 (13 13 (:REWRITE USE-ALL-<))
 )
(RATIONAL-LISTP-OF-MV-NTH-1-OF-SPLIT-LIST-FAST-AUX
 (257 169 (:REWRITE DEFAULT-CDR))
 (198 23 (:REWRITE ALL-RATIONALP-OF-CDR))
 (188 94 (:REWRITE DEFAULT-CAR))
 (177 92 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (128 68 (:REWRITE DEFAULT-+-2))
 (92 92 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (90 90 (:REWRITE USE-ALL-RATIONALP-2))
 (90 90 (:REWRITE USE-ALL-RATIONALP))
 (68 68 (:REWRITE DEFAULT-+-1))
 (55 29 (:REWRITE DEFAULT-<-1))
 (39 29 (:REWRITE DEFAULT-<-2))
 (32 16 (:REWRITE DEFAULT-*-2))
 (29 29 (:REWRITE USE-ALL-<-2))
 (29 29 (:REWRITE USE-ALL-<))
 (28 28 (:REWRITE USE-ALL-<=-2))
 (28 28 (:REWRITE USE-ALL-<=))
 (16 16 (:REWRITE DEFAULT-*-1))
 )
(RATIONAL-LISTP-OF-MV-NTH-0-OF-SPLIT-LIST-FAST
 (14 1 (:DEFINITION RATIONAL-LISTP))
 (10 2 (:DEFINITION LEN))
 (9 1 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 1 (:DEFINITION SPLIT-LIST-FAST-AUX))
 (4 2 (:REWRITE DEFAULT-+-2))
 (4 1 (:REWRITE ALL-RATIONALP-WHEN-RATIONAL-LISTP))
 (2 2 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE USE-ALL-RATIONALP-2))
 (1 1 (:REWRITE USE-ALL-RATIONALP))
 (1 1 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 )
(RATIONAL-LISTP-OF-MV-NTH-1-OF-SPLIT-LIST-FAST
 (14 1 (:DEFINITION RATIONAL-LISTP))
 (10 2 (:DEFINITION LEN))
 (9 1 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 1 (:DEFINITION SPLIT-LIST-FAST-AUX))
 (4 2 (:REWRITE DEFAULT-+-2))
 (4 1 (:REWRITE ALL-RATIONALP-WHEN-RATIONAL-LISTP))
 (2 2 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE USE-ALL-RATIONALP-2))
 (1 1 (:REWRITE USE-ALL-RATIONALP))
 (1 1 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 )
(NAT-LISTP-OF-MV-NTH-0-OF-SPLIT-LIST-FAST-AUX
 (868 78 (:REWRITE USE-ALL-<-FOR-CAR))
 (312 312 (:TYPE-PRESCRIPTION ALL-<))
 (208 23 (:REWRITE ALL-<-OF-CDR))
 (160 156 (:REWRITE DEFAULT-CDR))
 (156 78 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (143 103 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (121 103 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (107 101 (:REWRITE DEFAULT-CAR))
 (103 103 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (103 103 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (103 103 (:REWRITE ALL-<-TRANSITIVE))
 (101 91 (:REWRITE DEFAULT-<-1))
 (97 91 (:REWRITE DEFAULT-<-2))
 (91 91 (:REWRITE USE-ALL-<=-2))
 (91 91 (:REWRITE USE-ALL-<=))
 (91 91 (:REWRITE USE-ALL-<-2))
 (91 91 (:REWRITE USE-ALL-<))
 (80 44 (:REWRITE DEFAULT-+-2))
 (44 44 (:REWRITE DEFAULT-+-1))
 )
(NAT-LISTP-OF-MV-NTH-1-OF-SPLIT-LIST-FAST-AUX
 (932 75 (:REWRITE USE-ALL-<-FOR-CAR))
 (303 303 (:TYPE-PRESCRIPTION ALL-<))
 (259 171 (:REWRITE DEFAULT-CDR))
 (208 23 (:REWRITE ALL-<-OF-CDR))
 (206 100 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (194 100 (:REWRITE DEFAULT-CAR))
 (150 75 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (140 100 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (130 104 (:REWRITE DEFAULT-<-1))
 (128 68 (:REWRITE DEFAULT-+-2))
 (114 104 (:REWRITE DEFAULT-<-2))
 (104 104 (:REWRITE USE-ALL-<=-2))
 (104 104 (:REWRITE USE-ALL-<=))
 (104 104 (:REWRITE USE-ALL-<-2))
 (104 104 (:REWRITE USE-ALL-<))
 (100 100 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (100 100 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (100 100 (:REWRITE ALL-<-TRANSITIVE))
 (68 68 (:REWRITE DEFAULT-+-1))
 (32 16 (:REWRITE DEFAULT-*-2))
 (16 16 (:REWRITE DEFAULT-*-1))
 )
(NAT-LISTP-OF-MV-NTH-0-OF-SPLIT-LIST-FAST
 (20 1 (:DEFINITION NAT-LISTP))
 (17 1 (:DEFINITION NATP))
 (10 2 (:DEFINITION LEN))
 (8 1 (:REWRITE USE-ALL-<-FOR-CAR))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 1 (:DEFINITION SPLIT-LIST-FAST-AUX))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:TYPE-PRESCRIPTION ALL-<))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (1 1 (:REWRITE USE-ALL-<=-2))
 (1 1 (:REWRITE USE-ALL-<=))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (1 1 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (1 1 (:REWRITE ALL-<-TRANSITIVE))
 )
(NAT-LISTP-OF-MV-NTH-1-OF-SPLIT-LIST-FAST
 (20 1 (:DEFINITION NAT-LISTP))
 (17 1 (:DEFINITION NATP))
 (10 2 (:DEFINITION LEN))
 (8 1 (:REWRITE USE-ALL-<-FOR-CAR))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 1 (:DEFINITION SPLIT-LIST-FAST-AUX))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:TYPE-PRESCRIPTION ALL-<))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (1 1 (:REWRITE USE-ALL-<=-2))
 (1 1 (:REWRITE USE-ALL-<=))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (1 1 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (1 1 (:REWRITE ALL-<-TRANSITIVE))
 )
(ALL-<-OF-MV-NTH-0-OF-SPLIT-LIST-FAST-AUX
 (68 54 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (66 35 (:REWRITE DEFAULT-+-2))
 (57 39 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (54 54 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (46 46 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (46 46 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (45 13 (:REWRITE DEFAULT-<-1))
 (35 35 (:REWRITE DEFAULT-+-1))
 (24 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (21 13 (:REWRITE DEFAULT-<-2))
 (19 13 (:REWRITE USE-ALL-<))
 (18 2 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (13 13 (:REWRITE USE-ALL-<=-2))
 (13 13 (:REWRITE USE-ALL-<=))
 (13 13 (:REWRITE USE-ALL-<-2))
 (13 1 (:REWRITE ALL-RATIONALP-WHEN-RATIONAL-LISTP))
 (10 10 (:REWRITE USE-ALL-RATIONALP-2))
 (10 10 (:REWRITE USE-ALL-RATIONALP))
 (10 1 (:DEFINITION RATIONAL-LISTP))
 (7 7 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION MEMBERP))
 (6 4 (:REWRITE CONSP-OF-MV-NTH-0-OF-SPLIT-LIST-FAST-AUX))
 (5 5 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (3 3 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (2 2 (:REWRITE USE-ALL-<-FOR-CAR))
 (1 1 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 )
(ALL-<-OF-MV-NTH-1-OF-SPLIT-LIST-FAST-AUX
 (102 4 (:REWRITE CONSP-OF-MV-NTH-1-OF-SPLIT-LIST-FAST-AUX))
 (78 41 (:REWRITE DEFAULT-+-2))
 (57 47 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (53 17 (:REWRITE DEFAULT-<-1))
 (47 47 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (41 41 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (41 41 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (41 41 (:REWRITE DEFAULT-+-1))
 (29 17 (:REWRITE DEFAULT-<-2))
 (24 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (23 17 (:REWRITE USE-ALL-<))
 (18 2 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (17 17 (:REWRITE USE-ALL-<=-2))
 (17 17 (:REWRITE USE-ALL-<=))
 (17 17 (:REWRITE USE-ALL-<-2))
 (13 1 (:REWRITE ALL-RATIONALP-WHEN-RATIONAL-LISTP))
 (10 1 (:DEFINITION RATIONAL-LISTP))
 (8 8 (:REWRITE USE-ALL-RATIONALP-2))
 (8 8 (:REWRITE USE-ALL-RATIONALP))
 (8 4 (:REWRITE DEFAULT-*-2))
 (7 7 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION MEMBERP))
 (5 5 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (4 4 (:REWRITE DEFAULT-*-1))
 (3 3 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (2 2 (:REWRITE USE-ALL-<-FOR-CAR))
 (1 1 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 )
(ALL-<-OF-MV-NTH-0-OF-SPLIT-LIST-FAST
 (10 2 (:DEFINITION LEN))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 1 (:DEFINITION SPLIT-LIST-FAST-AUX))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (2 2 (:REWRITE ALL-<-TRANSITIVE))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 )
(ALL-<-OF-MV-NTH-1-OF-SPLIT-LIST-FAST
 (10 2 (:DEFINITION LEN))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 1 (:DEFINITION SPLIT-LIST-FAST-AUX))
 (4 2 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-SPLIT-LIST-FAST))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (2 2 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (2 2 (:REWRITE ALL-<-TRANSITIVE))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (1 1 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 )
(MERGE-SORT-<-AND-REMOVE-DUPS
 (49 19 (:REWRITE DEFAULT-CDR))
 (34 17 (:REWRITE DEFAULT-+-2))
 (32 4 (:REWRITE CONSP-OF-MV-NTH-0-OF-SPLIT-LIST-FAST))
 (17 17 (:REWRITE DEFAULT-+-1))
 (12 6 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-SPLIT-LIST-FAST))
 (10 6 (:REWRITE DEFAULT-<-2))
 (8 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-0-OF-SPLIT-LIST-FAST))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 6 (:REWRITE USE-ALL-<=-2))
 (6 6 (:REWRITE USE-ALL-<=))
 (6 6 (:REWRITE USE-ALL-<-2))
 (6 6 (:REWRITE USE-ALL-<))
 (4 4 (:REWRITE CONSP-OF-MV-NTH-1-OF-SPLIT-LIST-FAST))
 )
(RATIONAL-LISTP-OF-MERGE-SORT-<-AND-REMOVE-DUPS
 (108 11 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (48 12 (:REWRITE ALL-RATIONALP-WHEN-RATIONAL-LISTP))
 (24 24 (:TYPE-PRESCRIPTION ALL-RATIONALP))
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (11 11 (:REWRITE USE-ALL-RATIONALP-2))
 (11 11 (:REWRITE USE-ALL-RATIONALP))
 (9 1 (:REWRITE ALL-RATIONALP-OF-CDR))
 )
(TRUE-LISTP-OF-MERGE-SORT-<-AND-REMOVE-DUPS
 (18 18 (:REWRITE DEFAULT-CDR))
 )
(NAT-LISTP-OF-MERGE-SORT-<-AND-REMOVE-DUPS
 (96 11 (:REWRITE USE-ALL-<-FOR-CAR))
 (35 35 (:TYPE-PRESCRIPTION ALL-<))
 (22 11 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (18 18 (:REWRITE DEFAULT-CDR))
 (14 14 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (12 12 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (12 12 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (12 12 (:REWRITE ALL-<-TRANSITIVE))
 (11 11 (:REWRITE USE-ALL-<=-2))
 (11 11 (:REWRITE USE-ALL-<=))
 (11 11 (:REWRITE USE-ALL-<-2))
 (11 11 (:REWRITE USE-ALL-<))
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE DEFAULT-<-1))
 (8 1 (:REWRITE ALL-<-OF-CDR))
 )
(MERGE-SORT-<-AND-REMOVE-DUPS)
(SORTEDP-<=-OF-MERGE-SORT-<-AND-REMOVE-DUPS
 (10 10 (:REWRITE DEFAULT-CDR))
 )
(NO-DUPLICATESP-EQUAL-OF-MERGE-SORT-<-AND-REMOVE-DUPS
 (72 7 (:REWRITE USE-ALL-RATIONALP-FOR-CAR))
 (29 29 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE DEFAULT-CAR))
 (9 1 (:REWRITE ALL-RATIONALP-OF-CDR))
 (8 8 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP-CHEAP))
 (8 8 (:REWRITE ALL-RATIONALP-WHEN-NOT-CONSP))
 (7 7 (:REWRITE USE-ALL-RATIONALP-2))
 (7 7 (:REWRITE USE-ALL-RATIONALP))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(ALL-<-OF-MERGE-SORT-<-AND-REMOVE-DUPS
 (13 11 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (12 8 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (11 11 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (10 10 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (10 10 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (8 8 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE USE-ALL-RATIONALP-2))
 (1 1 (:REWRITE USE-ALL-RATIONALP))
 )
