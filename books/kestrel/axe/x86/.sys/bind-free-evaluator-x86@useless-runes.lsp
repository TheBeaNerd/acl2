(EVAL-AXE-BIND-FREE-FUNCTION-APPLICATION-X86
 (8264 275 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (1558 779 (:REWRITE LEN-WHEN-DARGP-CHEAP))
 (1482 13 (:LINEAR LARGEST-NON-QUOTEP-BOUND))
 (1346 673 (:TYPE-PRESCRIPTION NATP-OF-LARGEST-NON-QUOTEP))
 (1179 19 (:REWRITE SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CDR-CHAIN))
 (1106 38 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (1105 67 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-2-ALT))
 (1050 6 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (916 25 (:DEFINITION NAT-LISTP))
 (898 779 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (876 6 (:REWRITE <-OF-LARGEST-NON-QUOTEP))
 (829 25 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (779 779 (:TYPE-PRESCRIPTION DARGP))
 (779 779 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (779 779 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (779 779 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (756 6 (:REWRITE BOUNDED-DARG-LISTP-WHEN-ALL-<))
 (688 688 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (576 576 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (576 25 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (494 13 (:LINEAR LARGEST-NON-QUOTEP-BOUND-ALT))
 (481 169 (:REWRITE DEFAULT-CAR))
 (480 6 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (425 425 (:REWRITE DEFAULT-+-1))
 (392 12 (:REWRITE PERM-OF-UNION-EQUAL-WHEN-DISJOINT))
 (390 13 (:DEFINITION NTH))
 (370 5 (:DEFINITION INTERSECTION-EQUAL))
 (349 240 (:REWRITE DEFAULT-<-2))
 (342 114 (:REWRITE +-COMBINE-CONSTANTS))
 (339 30 (:REWRITE SUBSETP-EQUAL-OF-FREE-VARS-IN-TERMS-OF-CAR-CHAIN))
 (300 12 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (276 12 (:LINEAR LEN-OF-CDR-LINEAR))
 (275 275 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (270 240 (:REWRITE DEFAULT-<-1))
 (253 253 (:REWRITE USE-ALL-CONSP-2))
 (253 253 (:REWRITE USE-ALL-CONSP))
 (253 253 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (240 240 (:REWRITE USE-ALL-<-2))
 (240 240 (:REWRITE USE-ALL-<))
 (240 240 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (225 9 (:REWRITE DARG-LISTP-WHEN-NOT-CONSP))
 (221 27 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (219 3 (:REWRITE UNION-EQUAL-COMMUTATIVE-UNDER-PERM-WHEN-NO-DUPLICATESP))
 (212 2 (:DEFINITION NO-DUPLICATESP-EQUAL))
 (207 19 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (174 6 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (156 156 (:TYPE-PRESCRIPTION NAT-LISTP))
 (137 137 (:REWRITE DEFAULT-CDR))
 (134 67 (:REWRITE SUBSETP-EQUAL-OF-CDR-ARG2-CHEAP))
 (133 27 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (130 130 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (121 121 (:TYPE-PRESCRIPTION ALL-CONSP))
 (120 120 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (120 120 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (114 114 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (104 52 (:REWRITE SUBSETP-EQUAL-WHEN-SUBSETP-EQUAL-OF-CDR-CHEAP))
 (104 52 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG2-CHEAP))
 (104 52 (:REWRITE SUBSETP-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (96 6 (:REWRITE BOUNDED-DARG-LISTP-OF-0))
 (94 67 (:REWRITE SUBSETP-EQUAL-TRANSITIVE-ALT))
 (90 18 (:REWRITE ALL-CONSP-OF-CDR))
 (88 88 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (69 69 (:TYPE-PRESCRIPTION ALL-NATP))
 (66 33 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-MYQUOTEP-CHEAP))
 (66 33 (:REWRITE LARGEST-NON-QUOTEP-WHEN-ALL-CONSP-CHEAP))
 (62 62 (:REWRITE MEMBER-EQUAL-WHEN-SUBSETP-EQUAL-2))
 (60 12 (:REWRITE ALL-MYQUOTEP-WHEN-NOT-CONSP))
 (54 54 (:TYPE-PRESCRIPTION FREE-VARS-IN-TERM))
 (54 27 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (54 18 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (54 6 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (51 51 (:REWRITE USE-ALL-NATP-2))
 (51 51 (:REWRITE USE-ALL-NATP))
 (51 51 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (50 25 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (48 48 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (44 44 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (44 44 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (44 25 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (42 42 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (42 42 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (42 21 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (30 30 (:TYPE-PRESCRIPTION INTERSECTION-EQUAL))
 (28 28 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (27 27 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (27 27 (:REWRITE FREE-VARS-IN-TERM-WHEN-NOT-CONSP-CHEAP))
 (27 27 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (27 27 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (25 25 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (24 24 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (24 24 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (24 12 (:REWRITE UNION-EQUAL-WHEN-NOT-CONSP-ARG1-CHEAP))
 (18 18 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (18 9 (:REWRITE DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (13 13 (:LINEAR <-OF-LARGEST-NON-QUOTEP))
 (12 12 (:TYPE-PRESCRIPTION BOUNDED-DARG-LISTP))
 (12 12 (:TYPE-PRESCRIPTION ALL-<))
 (12 12 (:REWRITE ALISTP-WHEN-PSEUDO-DAGP-AUX))
 (12 12 (:REWRITE ALISTP-WHEN-BOUNDED-NATP-ALISTP))
 (12 6 (:REWRITE BOUNDED-DARG-LISTP-WHEN-BOUNDED-DARG-LISTP-OF-CDR-CHEAP))
 (12 6 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (9 9 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (9 9 (:REWRITE DARG-LISTP-WHEN-BOUNDED-DARG-LISTP))
 (9 9 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (9 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE USE-ALL-<=-2))
 (6 6 (:REWRITE USE-ALL-<=))
 (6 6 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (6 6 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (6 6 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (6 6 (:REWRITE ALL-<-TRANSITIVE))
 (5 5 (:REWRITE EQUAL-OF-LEN-AND-0))
 (3 3 (:REWRITE USE-ALL-RATIONALP-2))
 (3 3 (:REWRITE USE-ALL-RATIONALP))
 (3 3 (:REWRITE NATP-OF-+-WHEN-NEGATIVE-CONSTANT))
 (2 2 (:REWRITE SUBSETP-EQUAL-SELF))
 )
(SYMBOL-ALISTP-OF-EVAL-AXE-BIND-FREE-FUNCTION-APPLICATION-X86
 (8805 737 (:REWRITE DEFAULT-CAR))
 (3812 104 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (3588 84 (:DEFINITION NAT-LISTP))
 (3532 104 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (3492 1746 (:REWRITE LEN-WHEN-DARGP-CHEAP))
 (2584 104 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (2133 743 (:REWRITE DEFAULT-CDR))
 (1848 1746 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1746 1746 (:TYPE-PRESCRIPTION DARGP))
 (1746 1746 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (1746 1746 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (1746 1746 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (1627 99 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (1400 700 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1))
 (1400 56 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (1312 128 (:REWRITE LEN-OF-NTH-WHEN-DARG-LISTP))
 (1304 28 (:REWRITE ALL-NATP-OF-CDR))
 (1288 56 (:LINEAR LEN-OF-CDR-LINEAR))
 (1230 1230 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP-AUX))
 (1191 79 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (959 167 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (816 56 (:REWRITE DAG-EXPRP-OF-AREF1-WHEN-BOUNDED-DAG-EXPRP-OF-AREF1))
 (756 756 (:TYPE-PRESCRIPTION TYPE-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (720 506 (:REWRITE DEFAULT-+-2))
 (700 700 (:TYPE-PRESCRIPTION SYMBOLP-OF-CAR-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (624 16 (:REWRITE MYQUOTEP-OF-NTH-OF-DARGS))
 (624 16 (:REWRITE DARG-LISTP-OF-DARGS-WHEN-DAG-EXPRP))
 (576 12 (:DEFINITION INTEGER-LENGTH))
 (545 310 (:REWRITE DEFAULT-<-2))
 (516 12 (:DEFINITION FLOOR))
 (506 506 (:REWRITE DEFAULT-+-1))
 (501 99 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (488 488 (:TYPE-PRESCRIPTION NAT-LISTP))
 (432 126 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (418 418 (:REWRITE USE-ALL-CONSP-2))
 (418 418 (:REWRITE USE-ALL-CONSP))
 (418 418 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (416 208 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (416 208 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX-SIMPLE))
 (400 400 (:TYPE-PRESCRIPTION PSEUDO-DAG-ARRAYP))
 (396 198 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (396 102 (:REWRITE LEN-OF-AREF1-WHEN-QUOTEP-AND-PSEUDO-DAG-ARRAYP-AUX))
 (354 68 (:REWRITE ALL-CONSP-OF-CDR))
 (352 128 (:REWRITE LEN-OF-NTH-OF-DARGS))
 (350 350 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (334 334 (:TYPE-PRESCRIPTION ALL-CONSP))
 (328 56 (:REWRITE DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (328 24 (:REWRITE CONSP-OF-CDR-OF-NTH-OF-DARGS))
 (324 12 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (310 310 (:REWRITE USE-ALL-<-2))
 (310 310 (:REWRITE USE-ALL-<))
 (310 310 (:REWRITE DEFAULT-<-1))
 (310 310 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (272 272 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (272 272 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (267 245 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (267 245 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (265 69 (:REWRITE EQUAL-OF-LEN-AND-0))
 (264 56 (:REWRITE DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (240 40 (:REWRITE BOUNDED-DAG-EXPRP-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (224 224 (:TYPE-PRESCRIPTION DAG-EXPRP))
 (224 224 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (208 208 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (208 104 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (204 204 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (204 68 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (198 198 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (198 99 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (192 16 (:REWRITE DARG-LISTP-WHEN-NOT-CONSP))
 (167 167 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (144 16 (:REWRITE DARG-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-SIMPLE))
 (128 128 (:REWRITE LEN-OF-NTH-WHEN-BOUNDED-DARG-LISTP))
 (128 16 (:REWRITE NOT-CDDR-OF-NTH-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (128 16 (:REWRITE MYQUOTEP-OF-NTH-OF-DARGS-OF-AREF1))
 (126 126 (:REWRITE PSEUDO-DAG-ARRAYP-AUX-MONOTONE))
 (120 40 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (112 14 (:REWRITE NOT-EQUAL-OF-CAR-AND-QUOTE-WHEN-LEN-WRONG-AND-PSEUDO-DAG-ARRAYP-AUX))
 (108 12 (:DEFINITION NFIX))
 (104 104 (:REWRITE USE-ALL-NATP-2))
 (104 104 (:REWRITE USE-ALL-NATP))
 (104 104 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (104 104 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (102 102 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (100 100 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (99 99 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (99 99 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (99 99 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (96 96 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 (80 80 (:TYPE-PRESCRIPTION BOUNDED-DAG-EXPRP))
 (80 40 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-MYQUOTEP-CHEAP))
 (80 24 (:REWRITE CONSP-OF-CDR-OF-NTH-OF-DARGS-OF-AREF1))
 (56 56 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (56 56 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (56 56 (:REWRITE DAG-EXPRP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (56 56 (:REWRITE DAG-EXPRP-WHEN-BOUNDED-DAG-EXPRP))
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
 (36 36 (:REWRITE USE-ALL-<=-2))
 (36 36 (:REWRITE USE-ALL-<=))
 (36 12 (:REWRITE COMMUTATIVITY-OF-+))
 (36 12 (:REWRITE COMMUTATIVITY-OF-*))
 (32 16 (:REWRITE DARG-LISTP-WHEN-ALL-MYQUOTEP-CHEAP))
 (30 30 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (30 30 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (29 29 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (24 24 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (24 24 (:REWRITE DEFAULT-*-2))
 (24 24 (:REWRITE DEFAULT-*-1))
 (24 8 (:REWRITE CAR-OF-NTH-0-WHEN-PSEUDO-DAGP))
 (16 16 (:TYPE-PRESCRIPTION ALL-MYQUOTEP))
 (16 16 (:REWRITE NOT-CDDR-OF-NTH-WHEN-BOUNDED-DARG-LISTP))
 (16 16 (:REWRITE DARG-LISTP-WHEN-BOUNDED-DARG-LISTP))
 (16 16 (:REWRITE DARG-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP-AUX))
 (16 16 (:REWRITE DARG-LISTP-OF-DARGS-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (14 14 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (12 12 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (12 12 (:TYPE-PRESCRIPTION INTEGER-LENGTH))
 (12 12 (:REWRITE ZIP-OPEN))
 (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:REWRITE DEFAULT-NUMERATOR))
 (12 12 (:REWRITE DEFAULT-DENOMINATOR))
 (12 12 (:DEFINITION IFIX))
 (4 4 (:REWRITE NOT-CDR-OF-CDR-OF-AREF1-WHEN-PSEUDO-DAG-ARRAYP))
 (4 1 (:REWRITE +-COMBINE-CONSTANTS))
 (2 1 (:REWRITE SYMBOL-ALISTP-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 )
(TRUE-LISTP-OF-EVAL-AXE-BIND-FREE-FUNCTION-APPLICATION-X86)
