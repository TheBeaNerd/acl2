(EVAL-AXE-BIND-FREE-FUNCTION-APPLICATION-BASIC
 (9873 278 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (1538 769 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (1496 748 (:TYPE-PRESCRIPTION NATP-OF-LARGEST-NON-QUOTEP))
 (1456 13 (:LINEAR LARGEST-NON-QUOTEP-BOUND))
 (1289 19 (:REWRITE SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CDR-CHAIN))
 (1197 67 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-2-ALT))
 (1133 41 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (1091 28 (:DEFINITION NAT-LISTP))
 (1041 9 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (894 773 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (854 28 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (846 6 (:REWRITE <-OF-LARGEST-NON-QUOTEP))
 (773 773 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (773 773 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (773 773 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (769 769 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (769 769 (:TYPE-PRESCRIPTION ARRAY1P))
 (768 6 (:REWRITE ALL-DARGP-LESS-THAN-WHEN-ALL-<))
 (745 745 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (642 321 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-TYPE))
 (560 28 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (507 13 (:LINEAR LARGEST-NON-QUOTEP-BOUND-ALT))
 (480 6 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (457 12 (:REWRITE PERM-OF-UNION-EQUAL-WHEN-DISJOINT))
 (435 5 (:DEFINITION INTERSECTION-EQUAL))
 (432 172 (:REWRITE DEFAULT-CAR))
 (422 422 (:REWRITE DEFAULT-+-1))
 (377 13 (:DEFINITION NTH))
 (373 252 (:REWRITE DEFAULT-<-2))
 (369 369 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (345 30 (:REWRITE SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CAR-CHAIN))
 (342 114 (:REWRITE +-COMBINE-CONSTANTS))
 (322 322 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (322 322 (:REWRITE EQUAL-WHEN-BVLT))
 (322 322 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (322 322 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (322 322 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (322 322 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (322 322 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (322 322 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (322 322 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (322 322 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (322 322 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (282 252 (:REWRITE DEFAULT-<-1))
 (278 278 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (265 265 (:REWRITE USE-ALL-CONSP-2))
 (265 265 (:REWRITE USE-ALL-CONSP))
 (265 265 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (261 9 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (252 252 (:REWRITE USE-ALL-<-2))
 (252 252 (:REWRITE USE-ALL-<))
 (252 252 (:REWRITE <-WHEN-BVLT))
 (252 252 (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (249 3 (:REWRITE UNION-EQUAL-COMMUTATIVE-UNDER-PERM-WHEN-NO-DUPLICATESP))
 (242 2 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (228 12 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (221 27 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (216 19 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (204 12 (:LINEAR LEN-OF-CDR-LINEAR))
 (186 6 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (177 177 (:TYPE-PRESCRIPTION NAT-LISTP))
 (153 3 (:REWRITE ACL2-NUMBERP-OF-LOOKUP-EQUAL))
 (144 72 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (140 140 (:REWRITE DEFAULT-CDR))
 (134 67 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (132 132 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (132 132 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (130 130 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (121 121 (:TYPE-PRESCRIPTION ALL-CONSP))
 (114 114 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (112 52 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (106 52 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (104 52 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (98 67 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 (90 18 (:REWRITE ALL-CONSP-OF-CDR))
 (79 27 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (75 75 (:TYPE-PRESCRIPTION ALL-NATP))
 (72 72 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (72 72 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-AUX))
 (66 33 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-MYQUOTEP-CHEAP))
 (66 33 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-CONSP-CHEAP))
 (66 6 (:REWRITE ALL-DARGP-LESS-THAN-OF-0))
 (62 62 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (56 56 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (56 28 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (54 54 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (54 54 (:REWRITE USE-ALL-NATP-2))
 (54 54 (:REWRITE USE-ALL-NATP))
 (54 54 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (54 54 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (54 54 (:REWRITE NATP-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (54 27 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (54 6 (:REWRITE ALL-MYQUOTEP-WHEN-NOT-CONSP))
 (54 6 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (52 52 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (47 28 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (45 27 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (44 44 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (44 44 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (42 42 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (42 42 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (42 21 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (30 30 (:TYPE-PRESCRIPTION INTERSECTION-EQUAL))
 (30 12 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (28 28 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (27 27 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (27 27 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (27 27 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (25 25 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (24 24 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (24 24 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (18 18 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (18 9 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (18 9 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (13 13 (:LINEAR <-OF-LARGEST-NON-QUOTEP))
 (12 12 (:TYPE-PRESCRIPTION ALL-<))
 (12 12 (:REWRITE ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (12 12 (:REWRITE ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (12 6 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (9 9 (:REWRITE QUOTE-LEMMA-FOR-ALL-DARGP-LESS-THAN-GEN-ALT))
 (9 9 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (9 9 (:REWRITE ALL-DARGP-WHEN-ALL-DARGP-LESS-THAN))
 (9 9 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (9 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:TYPE-PRESCRIPTION ALL-DARGP-LESS-THAN))
 (6 6 (:REWRITE USE-ALL-<=-2))
 (6 6 (:REWRITE USE-ALL-<=))
 (6 6 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (6 6 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (6 6 (:REWRITE BOUND-WHEN-USB))
 (6 6 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (6 6 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (6 6 (:REWRITE ALL-<-TRANSITIVE))
 (5 5 (:REWRITE EQUAL-OF-LEN-AND-0))
 (3 3 (:REWRITE USE-ALL-RATIONALP-2))
 (3 3 (:REWRITE USE-ALL-RATIONALP))
 (3 3 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (3 3 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (2 2 (:REWRITE SUBSETP-EQUAL-SELF))
 )
(SYMBOL-ALISTP-OF-EVAL-AXE-BIND-FREE-FUNCTION-APPLICATION-BASIC
 (8347 793 (:REWRITE DEFAULT-CAR))
 (5744 124 (:DEFINITION NAT-LISTP))
 (4128 144 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (4040 144 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (2768 458 (:REWRITE DEFAULT-+-2))
 (2632 144 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (2400 128 (:REWRITE LEN-OF-NTH-WHEN-ALL-DARGP))
 (2040 40 (:REWRITE ACL2-NUMBERP-OF-LOOKUP-EQUAL))
 (2005 783 (:REWRITE DEFAULT-CDR))
 (1928 1786 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1786 1786 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (1786 1786 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (1786 1786 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (1603 99 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (1600 56 (:REWRITE DAG-EXPRP0-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (1504 16 (:REWRITE MYQUOTEP-OF-NTH-OF-DARGS))
 (1400 700 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (1396 28 (:REWRITE ALL-NATP-OF-CDR))
 (1246 1246 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-AUX))
 (1218 79 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (1120 560 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-TYPE))
 (1064 56 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (992 16 (:REWRITE ALL-DARGP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (952 56 (:LINEAR LEN-OF-CDR-LINEAR))
 (935 167 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (896 56 (:REWRITE DAG-EXPRP0-OF-AREF1-WHEN-BOUNDED-DAG-EXPRP-OF-AREF1))
 (856 214 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (768 768 (:TYPE-PRESCRIPTION NAT-LISTP))
 (768 24 (:REWRITE CONSP-OF-CDR-OF-NTH-OF-DARGS))
 (756 756 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (700 700 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (660 660 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (656 16 (:REWRITE ALL-DARGP-OF-DARGS-WHEN-DAG-EXPRP0))
 (589 314 (:REWRITE DEFAULT-<-2))
 (458 458 (:REWRITE USE-ALL-CONSP-2))
 (458 458 (:REWRITE USE-ALL-CONSP))
 (458 458 (:REWRITE DEFAULT-+-1))
 (458 458 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (448 224 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (448 224 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-SIMPLE))
 (432 126 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (428 214 (:TYPE-PRESCRIPTION ALEN1-TYPE))
 (416 416 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP))
 (396 102 (:REWRITE LEN-OF-AREF1-WHEN-QUOTEP-AND-PSEUDO-DAG-ARRAYP-AUX))
 (354 68 (:REWRITE ALL-CONSP-OF-CDR))
 (352 128 (:REWRITE LEN-OF-NTH-OF-DARGS))
 (339 339 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (334 334 (:TYPE-PRESCRIPTION ALL-CONSP))
 (314 314 (:REWRITE USE-ALL-<-2))
 (314 314 (:REWRITE USE-ALL-<))
 (314 314 (:REWRITE DEFAULT-<-1))
 (314 314 (:REWRITE <-WHEN-BVLT))
 (314 314 (:REWRITE <-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (307 285 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (307 285 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (304 16 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP))
 (297 99 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (288 288 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (288 288 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (288 144 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (265 69 (:REWRITE EQUAL-OF-LEN-AND-0))
 (264 56 (:REWRITE DAG-EXPRP0-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (240 40 (:REWRITE BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (224 224 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (224 224 (:TYPE-PRESCRIPTION DAG-EXPRP0))
 (224 224 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (214 214 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (214 214 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (214 214 (:TYPE-PRESCRIPTION ARRAY1P))
 (204 204 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (198 99 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (167 167 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (160 160 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (144 144 (:REWRITE USE-ALL-NATP-2))
 (144 144 (:REWRITE USE-ALL-NATP))
 (144 144 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (144 144 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (144 144 (:REWRITE NATP-WHEN-ALL-DARGP-LESS-THAN-GEN))
 (144 144 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (128 128 (:REWRITE LEN-OF-NTH-WHEN-ITEMS-HAVE-LEN))
 (128 128 (:REWRITE LEN-OF-NTH-WHEN-ALL-DARGP-LESS-THAN))
 (128 16 (:REWRITE NOT-CDDR-OF-NTH-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (128 16 (:REWRITE MYQUOTEP-OF-NTH-OF-DARGS-OF-AREF1))
 (126 126 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (120 40 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (112 14 (:REWRITE NOT-EQUAL-OF-CAR-AND-QUOTE-WHEN-LEN-WRONG-AND-PSEUDO-DAG-ARRAYP-AUX))
 (107 107 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (107 107 (:REWRITE EQUAL-WHEN-BVLT))
 (107 107 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (107 107 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (107 107 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (107 107 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (107 107 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (107 107 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (107 107 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (107 107 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (107 107 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (102 102 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (99 99 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (99 99 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (99 99 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (96 96 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (96 16 (:REWRITE ALL-DARGP-WHEN-NOT-CONSP-CHEAP))
 (80 80 (:TYPE-PRESCRIPTION BOUNDED-DAG-EXPRP))
 (80 40 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-MYQUOTEP-CHEAP))
 (80 24 (:REWRITE CONSP-OF-CDR-OF-NTH-OF-DARGS-OF-AREF1))
 (56 56 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (56 56 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (56 56 (:REWRITE DAG-EXPRP0-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (56 56 (:REWRITE DAG-EXPRP0-WHEN-BOUNDED-DAG-EXPRP))
 (44 44 (:TYPE-PRESCRIPTION SYMBOLP-OF-NTH-0-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (42 42 (:REWRITE CONSP-OF-CDR-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-AND-QUOTEP))
 (42 42 (:REWRITE CONSP-OF-CDR-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (40 40 (:REWRITE USE-ALL-RATIONALP-2))
 (40 40 (:REWRITE USE-ALL-RATIONALP))
 (40 40 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (40 40 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (40 40 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-SYMBOLP-CHEAP))
 (40 40 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-NOT-CONSP-CHEAP))
 (40 40 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (40 40 (:REWRITE BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-BETTER))
 (40 40 (:REWRITE BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-GEN))
 (40 40 (:REWRITE BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (40 40 (:REWRITE BOUNDED-DAG-EXPRP-MONOTONE))
 (40 40 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (40 40 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (32 16 (:REWRITE ALL-DARGP-WHEN-ALL-MYQUOTEP-CHEAP))
 (30 30 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (30 30 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (29 29 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (24 8 (:REWRITE CAR-OF-NTH-0-WHEN-PSEUDO-DAGP))
 (16 16 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (16 16 (:REWRITE NOT-CDDR-OF-NTH-WHEN-ALL-DARGP-LESS-THAN))
 (16 16 (:REWRITE ALL-DARGP-WHEN-ALL-DARGP-LESS-THAN))
 (16 16 (:REWRITE ALL-DARGP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (16 16 (:REWRITE ALL-DARGP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (14 14 (:REWRITE QUOTE-LEMMA-FOR-ALL-DARGP-LESS-THAN-GEN-ALT))
 (4 4 (:REWRITE NOT-CDR-OF-CDR-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (4 1 (:REWRITE +-COMBINE-CONSTANTS))
 (2 1 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 )
(TRUE-LISTP-OF-EVAL-AXE-BIND-FREE-FUNCTION-APPLICATION-BASIC)
