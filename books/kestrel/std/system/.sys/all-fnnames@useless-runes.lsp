(TRUE-LISTP-OF-ALL-FNNAMES1-TYPE)
(SYMBOL-LISTP-OF-ALL-FNNAMES1
 (374 281 (:REWRITE DEFAULT-CAR))
 (296 261 (:REWRITE DEFAULT-CDR))
 (281 281 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (126 126 (:REWRITE CONSP-BY-LEN))
 (101 31 (:REWRITE LEN-WHEN-ATOM))
 (56 56 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (50 50 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (48 6 (:REWRITE SUBSETP-CAR-MEMBER))
 (35 11 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (34 34 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (12 12 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (12 6 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (12 6 (:REWRITE MEMBER-WHEN-ATOM))
 (6 6 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (6 6 (:REWRITE SUBSETP-TRANS2))
 (6 6 (:REWRITE SUBSETP-TRANS))
 (6 6 (:REWRITE SUBSETP-MEMBER . 4))
 (6 6 (:REWRITE SUBSETP-MEMBER . 3))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (6 6 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (6 6 (:REWRITE INTERSECTP-MEMBER . 3))
 (6 6 (:REWRITE INTERSECTP-MEMBER . 2))
 (5 5 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 )
(ALL-FNNAMES1-INCLUDES-ACC
 (136 10 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (112 52 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALL-FNNAMES1-TYPE))
 (105 38 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (90 90 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (51 10 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (38 38 (:REWRITE CONSP-BY-LEN))
 (35 25 (:REWRITE DEFAULT-CAR))
 (30 3 (:REWRITE SUBSETP-CAR-MEMBER))
 (25 25 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (18 10 (:REWRITE DEFAULT-CDR))
 (16 15 (:REWRITE SUBSETP-TRANS))
 (12 3 (:REWRITE MEMBER-WHEN-ATOM))
 (8 8 (:TYPE-PRESCRIPTION ADD-TO-SET-EQUAL))
 (4 4 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (3 3 (:REWRITE SUBSETP-MEMBER . 4))
 (3 3 (:REWRITE SUBSETP-MEMBER . 3))
 (3 3 (:REWRITE SUBSETP-MEMBER . 2))
 (3 3 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (3 3 (:REWRITE INTERSECTP-MEMBER . 3))
 (3 3 (:REWRITE INTERSECTP-MEMBER . 2))
 (2 2 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 )
(ALL-FNNAMES1-MONOTONIC-ACC-ASSERTION)
(ALL-FNNAMES1-MONOTONIC-ACC-ASSERTION-NECC
 (4 4 (:DEFINITION MV-NTH))
 )
(ALL-FNNAMES1-MONOTONIC-ACC-LEMMA
 (1376 584 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (1214 225 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (1079 87 (:REWRITE SUBSETP-CAR-MEMBER))
 (976 976 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (870 225 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (816 392 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALL-FNNAMES1-TYPE))
 (584 584 (:REWRITE CONSP-BY-LEN))
 (541 361 (:REWRITE DEFAULT-CAR))
 (438 294 (:REWRITE DEFAULT-CDR))
 (361 361 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (332 51 (:REWRITE MEMBER-WHEN-ATOM))
 (297 256 (:REWRITE SUBSETP-TRANS))
 (132 2 (:REWRITE SUBSETP-CONS-2))
 (126 126 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (79 79 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (71 53 (:REWRITE SUBSETP-MEMBER . 3))
 (57 57 (:REWRITE INTERSECTP-MEMBER . 3))
 (57 57 (:REWRITE INTERSECTP-MEMBER . 2))
 (36 36 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 )
(ALL-FNNAMES1-MONOTONIC-ACC
 (174 2 (:DEFINITION ALL-FNNAMES1))
 (102 2 (:DEFINITION ADD-TO-SET-EQUAL))
 (53 5 (:REWRITE SUBSETP-CAR-MEMBER))
 (38 19 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (37 3 (:REWRITE SUBSETP-MEMBER . 4))
 (22 12 (:REWRITE DEFAULT-CAR))
 (22 7 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (21 5 (:REWRITE SUBSETP-MEMBER . 2))
 (20 7 (:REWRITE SUBSETP-TRANS2))
 (19 19 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (19 19 (:REWRITE CONSP-BY-LEN))
 (18 10 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (12 3 (:REWRITE MEMBER-WHEN-ATOM))
 (10 7 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (8 8 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (7 7 (:REWRITE SUBSETP-TRANS))
 (5 5 (:REWRITE SUBSETP-MEMBER . 1))
 (5 5 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (4 4 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (3 3 (:REWRITE SUBSETP-MEMBER . 3))
 (3 3 (:REWRITE INTERSECTP-MEMBER . 3))
 (3 3 (:REWRITE INTERSECTP-MEMBER . 2))
 (2 2 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 )
