(CHECK-PROPERTY
 (99 46 (:REWRITE DEFAULT-+-2))
 (65 46 (:REWRITE DEFAULT-+-1))
 (40 4 (:DEFINITION LENGTH))
 (36 36 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (35 23 (:REWRITE DEFAULT-CDR))
 (32 8 (:REWRITE COMMUTATIVITY-OF-+))
 (32 8 (:DEFINITION INTEGER-ABS))
 (30 3 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
 (28 4 (:DEFINITION LEN))
 (18 3 (:DEFINITION MEMBER-EQUAL))
 (17 12 (:REWRITE DEFAULT-<-2))
 (16 12 (:REWRITE DEFAULT-<-1))
 (15 15 (:REWRITE FOLD-CONSTS-IN-+))
 (13 13 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE DEFAULT-REALPART))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-IMAGPART))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 (3 3 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (3 3 (:REWRITE MEMBER-SELF))
 (2 2 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(ALIST-EQUIV-IMPLIES-EQUAL-CHECK-PROPERTY-3
 (1028 24 (:DEFINITION FAST-ALIST-FORK))
 (830 14 (:DEFINITION AIG-EVAL-ALIST))
 (526 56 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (478 6 (:REWRITE AIG-EVAL-APPEND-WHEN-NOT-INTERSECTING-ALIST-KEYS))
 (446 446 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (370 24 (:DEFINITION AIG-EVAL))
 (364 6 (:DEFINITION AIG-VARS))
 (306 12 (:REWRITE HONS-ASSOC-EQUAL-HSHRINK-ALIST))
 (270 6 (:REWRITE SET::UNION-UNDER-SET-EQUIV))
 (260 60 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
 (258 238 (:REWRITE DEFAULT-CAR))
 (258 58 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (229 197 (:REWRITE DEFAULT-CDR))
 (228 2 (:REWRITE HONS-ASSOC-EQUAL-AIG-EVAL-ALIST))
 (196 10 (:DEFINITION BINARY-APPEND))
 (176 20 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (162 30 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
 (116 116 (:TYPE-PRESCRIPTION ALISTP))
 (114 56 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (112 112 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (108 108 (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
 (90 90 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
 (90 58 (:REWRITE ALISTP-WHEN-ATOM))
 (88 56 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (78 40 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (60 60 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
 (60 12 (:REWRITE SET::SFIX-SET-IDENTITY))
 (36 12 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (36 6 (:REWRITE INTERSECTP-EQUAL-NON-CONS-1))
 (36 6 (:REWRITE INTERSECTP-EQUAL-NON-CONS))
 (24 24 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (18 6 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (16 16 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 12 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (12 12 (:REWRITE SETP-AIG-VARS))
 (10 2 (:REWRITE ALISTP-OF-CDR))
 (6 6 (:REWRITE INTERSECTP-MEMBER . 1))
 (6 6 (:REWRITE SET::INSERT-UNDER-SET-EQUIV))
 )
(ALIST-EQUIV-IMPLIES-EQUAL-CHECK-PROPERTY-1
 (4374 65 (:DEFINITION FAST-ALIST-FORK))
 (3298 49 (:DEFINITION AIG-EVAL-ALIST))
 (3065 38 (:REWRITE AIG-EVAL-APPEND-WHEN-NOT-INTERSECTING-ALIST-KEYS))
 (2418 32 (:REWRITE HONS-ASSOC-EQUAL-HSHRINK-ALIST))
 (2337 38 (:DEFINITION AIG-VARS))
 (2169 19 (:REWRITE HONS-ASSOC-EQUAL-AIG-EVAL-ALIST))
 (1710 38 (:REWRITE SET::UNION-UNDER-SET-EQUIV))
 (1610 1610 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (1490 93 (:DEFINITION AIG-EVAL))
 (1484 163 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (1238 262 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
 (973 57 (:DEFINITION BINARY-APPEND))
 (848 818 (:REWRITE DEFAULT-CAR))
 (806 114 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (771 723 (:REWRITE DEFAULT-CDR))
 (769 131 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
 (705 171 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (684 684 (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
 (393 393 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
 (380 76 (:REWRITE SET::SFIX-SET-IDENTITY))
 (345 163 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (342 342 (:TYPE-PRESCRIPTION ALISTP))
 (332 135 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (320 320 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (262 262 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
 (228 76 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (228 38 (:REWRITE INTERSECTP-EQUAL-NON-CONS-1))
 (228 38 (:REWRITE INTERSECTP-EQUAL-NON-CONS))
 (225 171 (:REWRITE ALISTP-WHEN-ATOM))
 (214 160 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (205 205 (:TYPE-PRESCRIPTION AIG-EVAL))
 (152 152 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (152 152 (:TYPE-PRESCRIPTION AIG-EVAL-ALIST))
 (120 38 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (114 114 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (76 76 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (76 76 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (76 76 (:REWRITE SETP-AIG-VARS))
 (70 70 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 (55 11 (:REWRITE ALISTP-OF-CDR))
 (38 38 (:REWRITE INTERSECTP-MEMBER . 1))
 (38 38 (:REWRITE SET::INSERT-UNDER-SET-EQUIV))
 (11 11 (:TYPE-PRESCRIPTION FAST-ALIST-FORK))
 )
(CHECK-PROPERTY-STRONG
 (79 1 (:REWRITE AIG-EVAL-APPEND-WHEN-NOT-INTERSECTING-ALIST-KEYS))
 (59 1 (:DEFINITION AIG-VARS))
 (45 1 (:REWRITE SET::UNION-UNDER-SET-EQUIV))
 (38 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (37 2 (:DEFINITION BINARY-APPEND))
 (32 32 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
 (16 4 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
 (16 2 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (15 1 (:REWRITE INTERSECTP-EQUAL-COMMUTE))
 (15 1 (:DEFINITION AIG-EVAL))
 (11 11 (:REWRITE DEFAULT-CDR))
 (10 2 (:REWRITE SET::SFIX-SET-IDENTITY))
 (10 2 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
 (8 4 (:REWRITE DEFAULT-+-2))
 (8 2 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (7 7 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
 (6 2 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (6 1 (:REWRITE INTERSECTP-EQUAL-NON-CONS-1))
 (6 1 (:REWRITE INTERSECTP-EQUAL-NON-CONS))
 (4 4 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 4 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (3 1 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (2 2 (:REWRITE SETP-AIG-VARS))
 (2 2 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE ALISTP-WHEN-ATOM))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 1))
 (1 1 (:REWRITE SET::INSERT-UNDER-SET-EQUIV))
 )
(CHECK-AG-PROPERTY)
(CHECK-AG-PROPERTY-NECC)
(CHECK-AG-PROPERTY-IMPLIES-CHECK-PROPERTY-STRONG
 (5953 75 (:REWRITE AIG-EVAL-APPEND-WHEN-NOT-INTERSECTING-ALIST-KEYS))
 (4801 58 (:DEFINITION AIG-EVAL-ALIST))
 (4498 75 (:DEFINITION AIG-VARS))
 (3375 75 (:REWRITE SET::UNION-UNDER-SET-EQUIV))
 (2424 2424 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2420 133 (:DEFINITION BINARY-APPEND))
 (2148 251 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (2124 26 (:REWRITE HONS-ASSOC-EQUAL-HSHRINK-ALIST))
 (1917 17 (:REWRITE HONS-ASSOC-EQUAL-AIG-EVAL-ALIST))
 (1770 406 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
 (1350 1350 (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
 (1101 203 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
 (1056 264 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (750 150 (:REWRITE SET::SFIX-SET-IDENTITY))
 (609 609 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
 (528 528 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (528 528 (:TYPE-PRESCRIPTION ALISTP))
 (517 251 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (450 150 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (450 75 (:REWRITE INTERSECTP-EQUAL-NON-CONS-1))
 (450 75 (:REWRITE INTERSECTP-EQUAL-NON-CONS))
 (406 406 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
 (360 24 (:REWRITE INTERSECTP-EQUAL-COMMUTE))
 (300 300 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (287 116 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (264 264 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (264 264 (:REWRITE ALISTP-WHEN-ATOM))
 (231 75 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (225 225 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (189 189 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (150 150 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (150 150 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (150 150 (:REWRITE SETP-AIG-VARS))
 (144 144 (:TYPE-PRESCRIPTION AIG-EVAL-ALIST))
 (112 14 (:REWRITE ALISTP-OF-CDR))
 (75 75 (:REWRITE INTERSECTP-MEMBER . 1))
 (75 75 (:REWRITE SET::INSERT-UNDER-SET-EQUIV))
 (60 60 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 (11 11 (:TYPE-PRESCRIPTION FAST-ALIST-FORK))
 )
(UNSAT-P)
(UNSAT-P-NECC)
(AIG-EVAL-WHEN-VARS-SUBSET-OF-FIRST-KEYS
 (850 100 (:REWRITE SUBSETP-TRANS2))
 (650 650 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (421 96 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (378 37 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (280 20 (:DEFINITION BINARY-APPEND))
 (247 96 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (192 40 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (156 40 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (150 150 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (126 9 (:DEFINITION MEMBER-EQUAL))
 (118 110 (:REWRITE DEFAULT-CDR))
 (108 38 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (100 100 (:REWRITE SUBSETP-TRANS))
 (87 29 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (77 77 (:REWRITE DEFAULT-CAR))
 (72 24 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (67 12 (:REWRITE INTERSECTP-EQUAL-NON-CONS))
 (60 2 (:REWRITE INTERSECTP-EQUAL-APPEND2))
 (48 48 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (45 45 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (36 18 (:REWRITE SUBSETP-CAR-MEMBER))
 (25 25 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 (18 18 (:REWRITE SUBSETP-MEMBER . 2))
 (18 18 (:REWRITE SUBSETP-MEMBER . 1))
 (9 9 (:REWRITE INTERSECTP-MEMBER . 1))
 (6 1 (:REWRITE INTERSECTP-EQUAL-CONS-SECOND))
 )
(INVAR-HOLDS-AFTER-APPLY-UPDATES1
 (649 11 (:DEFINITION AIG-VARS))
 (495 11 (:REWRITE SET::UNION-UNDER-SET-EQUIV))
 (375 7 (:REWRITE AIG-EVAL-APPEND-WHEN-NOT-INTERSECTING-ALIST-KEYS))
 (222 14 (:DEFINITION BINARY-APPEND))
 (194 194 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (192 192 (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
 (172 28 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (120 28 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (120 2 (:REWRITE AIG-VARS-AIG-NOT))
 (110 22 (:REWRITE SET::SFIX-SET-IDENTITY))
 (88 22 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
 (66 22 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (55 11 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
 (49 9 (:REWRITE SUBSETP-TRANS))
 (44 44 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (43 8 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (36 36 (:REWRITE DEFAULT-CDR))
 (36 36 (:REWRITE DEFAULT-CAR))
 (33 33 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
 (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (30 2 (:REWRITE INTERSECTP-EQUAL-COMMUTE))
 (28 8 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (25 5 (:REWRITE INTERSECTP-EQUAL-NON-CONS-1))
 (25 5 (:REWRITE INTERSECTP-EQUAL-NON-CONS))
 (22 22 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (22 22 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
 (22 22 (:REWRITE SETP-AIG-VARS))
 (19 11 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (11 11 (:REWRITE SET::INSERT-UNDER-SET-EQUIV))
 (10 10 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (10 2 (:REWRITE CONSP-OF-APPEND))
 (8 4 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (5 5 (:TYPE-PRESCRIPTION AIG-EVAL-ALIST))
 (5 5 (:REWRITE INTERSECTP-MEMBER . 1))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (2 2 (:REWRITE UNSAT-P-NECC))
 )
(INVAR-HOLDS-AFTER-APPLY-UPDATES
 (118 2 (:DEFINITION AIG-VARS))
 (90 2 (:REWRITE SET::UNION-UNDER-SET-EQUIV))
 (56 4 (:DEFINITION BINARY-APPEND))
 (52 52 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
 (36 8 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (33 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (20 4 (:REWRITE SET::SFIX-SET-IDENTITY))
 (18 3 (:REWRITE SUBSETP-TRANS))
 (16 4 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
 (12 4 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (12 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (12 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (10 2 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
 (8 8 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (6 6 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
 (6 2 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (5 5 (:TYPE-PRESCRIPTION AIG-EVAL-ALIST))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
 (4 4 (:REWRITE SETP-AIG-VARS))
 (3 3 (:REWRITE UNSAT-P-NECC))
 (2 2 (:REWRITE SET::INSERT-UNDER-SET-EQUIV))
 )
(PROP-HOLDS-WHEN-INVAR-HOLDS
 (590 10 (:DEFINITION AIG-VARS))
 (450 10 (:REWRITE SET::UNION-UNDER-SET-EQUIV))
 (379 7 (:REWRITE AIG-EVAL-WHEN-VARS-SUBSET-OF-FIRST-KEYS))
 (377 7 (:REWRITE AIG-EVAL-APPEND-WHEN-NOT-INTERSECTING-ALIST-KEYS))
 (182 12 (:DEFINITION BINARY-APPEND))
 (174 174 (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
 (156 156 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (132 24 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (120 2 (:REWRITE AIG-VARS-AIG-NOT))
 (102 24 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (100 20 (:REWRITE SET::SFIX-SET-IDENTITY))
 (80 20 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
 (60 20 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (50 10 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
 (50 4 (:REWRITE INTERSECTP-EQUAL-COMMUTE))
 (40 40 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (32 32 (:REWRITE DEFAULT-CDR))
 (32 32 (:REWRITE DEFAULT-CAR))
 (30 30 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
 (25 5 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (25 5 (:REWRITE INTERSECTP-EQUAL-NON-CONS-1))
 (25 5 (:REWRITE INTERSECTP-EQUAL-NON-CONS))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (20 20 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (20 20 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
 (20 20 (:REWRITE SETP-AIG-VARS))
 (20 5 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (16 10 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (10 10 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (10 10 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (10 10 (:REWRITE SET::INSERT-UNDER-SET-EQUIV))
 (5 5 (:REWRITE SUBSETP-TRANS2))
 (5 5 (:REWRITE SUBSETP-TRANS))
 (5 5 (:REWRITE INTERSECTP-MEMBER . 1))
 (2 2 (:REWRITE UNSAT-P-NECC))
 )
(INDUCTIVE-INVARIANT-IMPL-CHECK-PROPERTY
 (1145 19 (:DEFINITION AIG-VARS))
 (1009 12 (:DEFINITION FAST-ALIST-FORK))
 (969 9 (:DEFINITION AIG-EVAL-ALIST))
 (855 19 (:REWRITE SET::UNION-UNDER-SET-EQUIV))
 (636 6 (:REWRITE HONS-ASSOC-EQUAL-HSHRINK-ALIST))
 (591 3 (:REWRITE HONS-ASSOC-EQUAL-AIG-EVAL-ALIST))
 (565 7 (:REWRITE AIG-EVAL-WHEN-VARS-SUBSET-OF-FIRST-KEYS))
 (544 7 (:REWRITE AIG-EVAL-APPEND-WHEN-NOT-INTERSECTING-ALIST-KEYS))
 (540 540 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (429 24 (:DEFINITION BINARY-APPEND))
 (382 48 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (356 36 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (342 342 (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
 (316 70 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
 (273 16 (:DEFINITION AIG-EVAL))
 (203 189 (:REWRITE DEFAULT-CAR))
 (196 35 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
 (190 170 (:REWRITE DEFAULT-CDR))
 (190 38 (:REWRITE SET::SFIX-SET-IDENTITY))
 (171 39 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (114 38 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (105 105 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
 (78 78 (:TYPE-PRESCRIPTION ALISTP))
 (76 76 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (74 36 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (72 72 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (72 12 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (72 12 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (70 70 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
 (63 39 (:REWRITE ALISTP-WHEN-ATOM))
 (60 36 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (57 57 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (57 24 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (45 45 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (43 19 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (42 7 (:REWRITE INTERSECTP-EQUAL-NON-CONS-1))
 (42 7 (:REWRITE INTERSECTP-EQUAL-NON-CONS))
 (38 38 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (38 38 (:REWRITE SETP-AIG-VARS))
 (28 13 (:REWRITE SUBSETP-TRANS))
 (22 22 (:TYPE-PRESCRIPTION AIG-EVAL-ALIST))
 (19 19 (:REWRITE SET::INSERT-UNDER-SET-EQUIV))
 (15 3 (:REWRITE ALISTP-OF-CDR))
 (14 14 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (14 14 (:REWRITE UNSAT-P-NECC))
 (12 12 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 (7 7 (:REWRITE INTERSECTP-MEMBER . 1))
 )
(INDUCTIVE-INVARIANT-IMPL-CHECK-AG-PROPERTY
 (1180 20 (:DEFINITION AIG-VARS))
 (900 20 (:REWRITE SET::UNION-UNDER-SET-EQUIV))
 (620 12 (:REWRITE AIG-EVAL-APPEND-WHEN-NOT-INTERSECTING-ALIST-KEYS))
 (447 31 (:DEFINITION BINARY-APPEND))
 (442 442 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (424 106 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
 (360 360 (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
 (306 62 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (265 53 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
 (255 62 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (200 40 (:REWRITE SET::SFIX-SET-IDENTITY))
 (188 23 (:REWRITE SUBSETP-TRANS))
 (159 159 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
 (149 149 (:REWRITE DEFAULT-CAR))
 (146 146 (:REWRITE DEFAULT-CDR))
 (120 40 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (120 20 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (120 8 (:REWRITE INTERSECTP-EQUAL-COMMUTE))
 (111 3 (:DEFINITION AIG-EVAL-ALIST))
 (106 106 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
 (84 84 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (80 80 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (80 20 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (51 51 (:REWRITE PROP-HOLDS-WHEN-INVAR-HOLDS))
 (48 8 (:REWRITE INTERSECTP-EQUAL-NON-CONS-1))
 (48 8 (:REWRITE INTERSECTP-EQUAL-NON-CONS))
 (44 20 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (40 40 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (40 40 (:REWRITE SETP-AIG-VARS))
 (24 3 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (20 20 (:REWRITE SET::INSERT-UNDER-SET-EQUIV))
 (16 16 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (15 15 (:TYPE-PRESCRIPTION AIG-EVAL-ALIST))
 (12 3 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (8 8 (:REWRITE INTERSECTP-MEMBER . 1))
 (7 7 (:REWRITE UNSAT-P-NECC))
 (6 6 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (6 6 (:TYPE-PRESCRIPTION ALISTP))
 (6 3 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (4 4 (:REWRITE CHECK-AG-PROPERTY-NECC))
 (3 3 (:TYPE-PRESCRIPTION ATOM-LISTP))
 (3 3 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE ALISTP-WHEN-ATOM))
 )
(INDUCTIVE-INVARIANT-IMPL-CHECK-PROPERTY-STRONG
 (1180 20 (:DEFINITION AIG-VARS))
 (900 20 (:REWRITE SET::UNION-UNDER-SET-EQUIV))
 (620 12 (:REWRITE AIG-EVAL-APPEND-WHEN-NOT-INTERSECTING-ALIST-KEYS))
 (447 31 (:DEFINITION BINARY-APPEND))
 (442 442 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (424 106 (:REWRITE AIG-ATOM-P-WHEN-AIG-VAR-P))
 (360 360 (:TYPE-PRESCRIPTION TRUE-LISTP-AIG-VARS))
 (306 62 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (265 53 (:REWRITE AIG-VAR-P-WHEN-AIG-ATOM-P))
 (255 62 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (200 40 (:REWRITE SET::SFIX-SET-IDENTITY))
 (188 23 (:REWRITE SUBSETP-TRANS))
 (159 159 (:TYPE-PRESCRIPTION AIG-VAR-P$INLINE))
 (149 149 (:REWRITE DEFAULT-CAR))
 (146 146 (:REWRITE DEFAULT-CDR))
 (120 40 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (120 20 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (120 8 (:REWRITE INTERSECTP-EQUAL-COMMUTE))
 (111 3 (:DEFINITION AIG-EVAL-ALIST))
 (106 106 (:TYPE-PRESCRIPTION AIG-ATOM-P$INLINE))
 (84 84 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (80 80 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (80 20 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (51 51 (:REWRITE PROP-HOLDS-WHEN-INVAR-HOLDS))
 (48 8 (:REWRITE INTERSECTP-EQUAL-NON-CONS-1))
 (48 8 (:REWRITE INTERSECTP-EQUAL-NON-CONS))
 (44 20 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (40 40 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (40 40 (:REWRITE SETP-AIG-VARS))
 (24 3 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (20 20 (:REWRITE SET::INSERT-UNDER-SET-EQUIV))
 (16 16 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (15 15 (:TYPE-PRESCRIPTION AIG-EVAL-ALIST))
 (12 3 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (8 8 (:REWRITE INTERSECTP-MEMBER . 1))
 (7 7 (:REWRITE UNSAT-P-NECC))
 (6 6 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (6 6 (:TYPE-PRESCRIPTION ALISTP))
 (6 3 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (3 3 (:TYPE-PRESCRIPTION ATOM-LISTP))
 (3 3 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE ALISTP-WHEN-ATOM))
 )
