(SV::FLAG-LEMMA-FOR-SVEX-VARS-OF-NON-NETWORK-OF-NETEVAL-ORDERING-COMPILE
 (968 44 (:DEFINITION MEMBER-EQUAL))
 (203 29 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (193 169 (:REWRITE DEFAULT-CAR))
 (186 186 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (168 168 (:TYPE-PRESCRIPTION SV::SVEX-KIND$INLINE))
 (154 154 (:REWRITE SUBSETP-TRANS2))
 (154 154 (:REWRITE SUBSETP-TRANS))
 (145 123 (:REWRITE DEFAULT-CDR))
 (144 144 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (144 144 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (112 56 (:REWRITE SV::SVEX-VARS-WHEN-VAR))
 (112 56 (:REWRITE SV::SVEX-VARS-WHEN-QUOTE))
 (112 56 (:REWRITE SV::SVEX-VARS-WHEN-CALL))
 (109 109 (:REWRITE SUBSETP-MEMBER . 2))
 (109 3 (:REWRITE SV::VARS-OF-SVEX-COMPOSE))
 (105 105 (:REWRITE SUBSETP-MEMBER . 4))
 (105 105 (:REWRITE INTERSECTP-MEMBER . 3))
 (105 105 (:REWRITE INTERSECTP-MEMBER . 2))
 (54 54 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-SUBSETP-EQUAL))
 (50 3 (:REWRITE SUBSETP-OF-CONS))
 (44 44 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (40 4 (:REWRITE SV::NETEVAL-SIGORDERING-FIX-WHEN-NETEVAL-SIGORDERING-P))
 (30 15 (:REWRITE SV::CONSP-CAR-OF-NETEVAL-ORDERING-FIX))
 (28 16 (:REWRITE SV::NETEVAL-ORDERING-COMPILE-WHEN-ATOM-FIX))
 (27 27 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-NOT-CONSP))
 (25 16 (:REWRITE DEFAULT-+-1))
 (24 4 (:REWRITE SV::NETEVAL-SIGORDERING-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-NETEVAL-ORDERING-P))
 (23 16 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (18 18 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (8 8 (:TYPE-PRESCRIPTION SV::NETEVAL-SIGORDERING-P))
 (8 7 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVEX-FIX-UNDER-MAYBE-SVEX-EQUIV))
 (7 7 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE SV::SVEX-COMPOSE-LOOKUP-WHEN-NOT-SVEX-LOOKUP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(SV::SVEX-VARS-OF-NON-NETWORK-OF-NETEVAL-ORDERING-COMPILE)
(SV::SVEX-VARS-OF-NON-NETWORK-OF-NETEVAL-SIGORDERING-COMPILE)
(SV::SVEX-VARS-OF-NON-NETWORK-OF-NETEVAL-ORDERING-OR-NULL-COMPILE)
(SV::SVEX-LOOKUP-OF-NETEVAL-ORDERING-COMPILE-UNDER-IFF
 (30 3 (:REWRITE SV::NETEVAL-SIGORDERING-FIX-WHEN-NETEVAL-SIGORDERING-P))
 (30 3 (:DEFINITION HONS-ASSOC-EQUAL))
 (18 3 (:REWRITE SV::NETEVAL-SIGORDERING-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-NETEVAL-ORDERING-P))
 (18 3 (:REWRITE SV::NETEVAL-ORDERING-FIX-WHEN-NETEVAL-ORDERING-P))
 (15 3 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (12 12 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-P))
 (12 12 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (12 12 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-SUBSETP-EQUAL))
 (12 12 (:REWRITE DEFAULT-CAR))
 (12 10 (:REWRITE DEFAULT-CDR))
 (6 6 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (6 6 (:TYPE-PRESCRIPTION SV::SVAR-FIX$INLINE))
 (6 6 (:TYPE-PRESCRIPTION SV::NETEVAL-SIGORDERING-P))
 (6 6 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-NOT-CONSP))
 (6 3 (:DEFINITION HONS-EQUAL))
 (2 1 (:REWRITE SV::NETEVAL-ORDERING-COMPILE-WHEN-ATOM-FIX))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 )
(SV::NOT-VAR-OF-LOOKUP-WHEN-NOT-VAR-OF-REDUCE
 (1446 50 (:DEFINITION MEMBER-EQUAL))
 (286 38 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (252 180 (:REWRITE DEFAULT-CAR))
 (242 149 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (228 30 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (220 152 (:REWRITE DEFAULT-CDR))
 (208 148 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (168 22 (:REWRITE SV::SVARLIST-FIX-WHEN-SVARLIST-P))
 (165 165 (:REWRITE SUBSETP-TRANS2))
 (165 165 (:REWRITE SUBSETP-TRANS))
 (162 6 (:REWRITE SUBSETP-OF-CONS))
 (156 52 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (128 16 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-NETEVAL-ORDERING-P))
 (110 110 (:REWRITE SUBSETP-MEMBER . 2))
 (104 104 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (103 103 (:REWRITE SUBSETP-MEMBER . 4))
 (103 103 (:REWRITE INTERSECTP-MEMBER . 3))
 (103 103 (:REWRITE INTERSECTP-MEMBER . 2))
 (102 102 (:TYPE-PRESCRIPTION SV::SVEX-KIND$INLINE))
 (100 20 (:DEFINITION BINARY-APPEND))
 (96 16 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ENV-P))
 (96 12 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (88 88 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (87 87 (:TYPE-PRESCRIPTION SV::SVARLIST-P))
 (80 80 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (68 34 (:REWRITE SV::SVEX-VARS-WHEN-VAR))
 (68 34 (:REWRITE SV::SVEX-VARS-WHEN-QUOTE))
 (68 34 (:REWRITE SV::SVEX-VARS-WHEN-CALL))
 (64 16 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (64 16 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (60 10 (:REWRITE SV::SVARLIST-P-OF-CDR-WHEN-SVARLIST-P))
 (56 56 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (50 50 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (45 44 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (40 40 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (32 32 (:TYPE-PRESCRIPTION SV::SVEX-ENV-P))
 (32 32 (:TYPE-PRESCRIPTION SV::SVAR-BOOLMASKS-P))
 (32 32 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-P))
 (32 32 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-SUBSETP-EQUAL))
 (16 16 (:TYPE-PRESCRIPTION SV::SVEX-ALIST-P))
 (16 16 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (16 16 (:REWRITE SV::SVEX-ALIST-P-OF-SVEX-ALIST-REDUCE))
 (16 16 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (16 16 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-NOT-CONSP))
 (11 11 (:REWRITE-QUOTED-CONSTANT SV::SVEX-ALIST-FIX-UNDER-SVEX-ALIST-EQUIV))
 (8 4 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (4 4 (:REWRITE SV::SVARLIST-FIX-UNDER-IFF))
 (2 2 (:REWRITE CONSP-OF-APPEND))
 )
(SV::FLAG-LEMMA-FOR-VARS-OF-SVEX-COMPOSE-NETEVAL-ORDERING-COMPILE
 (12359 312 (:DEFINITION MEMBER-EQUAL))
 (4713 519 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (3768 41 (:REWRITE SV::VARS-OF-SVEXLIST-COMPOSE))
 (3251 2440 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (3088 33 (:REWRITE SV::VARS-OF-SVEX-COMPOSE))
 (3067 2528 (:REWRITE SUBSETP-TRANS))
 (2929 2431 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2588 2528 (:REWRITE SUBSETP-TRANS2))
 (1293 49 (:REWRITE SUBSETP-INTERSECTION-EQUAL))
 (888 24 (:DEFINITION INTERSECTION-EQUAL))
 (887 887 (:REWRITE DEFAULT-CAR))
 (803 78 (:REWRITE SV::NETEVAL-SIGORDERING-FIX-WHEN-NETEVAL-SIGORDERING-P))
 (795 795 (:REWRITE SUBSETP-MEMBER . 2))
 (738 738 (:REWRITE DEFAULT-CDR))
 (726 726 (:TYPE-PRESCRIPTION SV::SVEXLIST-COMPOSE))
 (630 630 (:REWRITE SUBSETP-MEMBER . 4))
 (630 630 (:REWRITE INTERSECTP-MEMBER . 3))
 (630 630 (:REWRITE INTERSECTP-MEMBER . 2))
 (468 78 (:REWRITE SV::NETEVAL-SIGORDERING-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-NETEVAL-ORDERING-P))
 (428 16 (:REWRITE SUBSETP-APPEND1))
 (354 354 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (309 15 (:REWRITE SUBSETP-OF-CONS))
 (306 153 (:REWRITE SV::NETEVAL-ORDERING-COMPILE-WHEN-ATOM-FIX))
 (225 225 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-FIX$INLINE))
 (212 212 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-SUBSETP-EQUAL))
 (192 64 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (177 177 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (168 28 (:REWRITE SV::NETEVAL-ORDERING-FIX-WHEN-NETEVAL-ORDERING-P))
 (156 156 (:TYPE-PRESCRIPTION SV::NETEVAL-SIGORDERING-P))
 (147 147 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (130 130 (:TYPE-PRESCRIPTION SV::SVEX-COMPOSE))
 (112 112 (:TYPE-PRESCRIPTION SV::SVEX-CALL->ARGS$INLINE))
 (106 106 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-NOT-CONSP))
 (96 24 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (42 42 (:TYPE-PRESCRIPTION INTERSECTION-EQUAL))
 (30 9 (:DEFINITION ATOM))
 (20 4 (:DEFINITION BINARY-APPEND))
 (12 2 (:REWRITE SUBSETP-CONS-2))
 (8 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (8 8 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (2 2 (:REWRITE-QUOTED-CONSTANT SV::SVEXLIST-FIX-UNDER-SVEXLIST-EQUIV))
 )
(SV::VARS-OF-SVEX-COMPOSE-NETEVAL-ORDERING-COMPILE)
(SV::VARS-OF-SVEXLIST-COMPOSE-NETEVAL-ORDERING-COMPILE)
(SV::SVEX-ALIST-REDUCE-OF-NIL
 (4 4 (:REWRITE-QUOTED-CONSTANT SV::SVEX-ALIST-FIX-UNDER-SVEX-ALIST-EQUIV))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(SV::SVEX-ALIST-VARS-OF-SVEX-ALIST-REDUCE-CONS
 (2041 69 (:DEFINITION MEMBER-EQUAL))
 (705 67 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (678 582 (:REWRITE DEFAULT-CAR))
 (597 199 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (580 475 (:REWRITE SUBSETP-TRANS2))
 (501 430 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (475 475 (:REWRITE SUBSETP-TRANS))
 (466 402 (:REWRITE DEFAULT-CDR))
 (465 28 (:REWRITE SUBSETP-APPEND1))
 (455 65 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (435 87 (:DEFINITION BINARY-APPEND))
 (429 429 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (418 64 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (398 398 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (397 55 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-NETEVAL-ORDERING-P))
 (312 8 (:REWRITE SV::NOT-VAR-OF-LOOKUP-WHEN-NOT-VAR-OF-REDUCE))
 (309 309 (:TYPE-PRESCRIPTION SV::SVEX-KIND$INLINE))
 (287 55 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ENV-P))
 (231 231 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (220 55 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-BOOLMASKS-P))
 (206 103 (:REWRITE SV::SVEX-VARS-WHEN-VAR))
 (206 103 (:REWRITE SV::SVEX-VARS-WHEN-QUOTE))
 (206 103 (:REWRITE SV::SVEX-VARS-WHEN-CALL))
 (185 55 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVEX-ALIST-P))
 (174 174 (:REWRITE SUBSETP-MEMBER . 4))
 (174 174 (:REWRITE INTERSECTP-MEMBER . 3))
 (174 174 (:REWRITE INTERSECTP-MEMBER . 2))
 (174 174 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (173 173 (:REWRITE SUBSETP-MEMBER . 2))
 (160 160 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (110 110 (:TYPE-PRESCRIPTION SV::SVEX-ENV-P))
 (110 110 (:TYPE-PRESCRIPTION SV::SVAR-BOOLMASKS-P))
 (110 110 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-P))
 (110 110 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-SUBSETP-EQUAL))
 (100 10 (:REWRITE SV::SVEX-FIX-WHEN-SVEX-P))
 (81 80 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (78 12 (:REWRITE SV::SVARLIST-FIX-WHEN-SVARLIST-P))
 (69 69 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (57 57 (:TYPE-PRESCRIPTION SV::SVEX-ALIST-P))
 (56 56 (:REWRITE SV::CONSP-OF-SVARLIST-FIX))
 (55 55 (:REWRITE SV::SVEX-ENV-P-WHEN-NOT-CONSP))
 (55 55 (:REWRITE SV::SVAR-BOOLMASKS-P-WHEN-NOT-CONSP))
 (55 55 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-NOT-CONSP))
 (53 53 (:REWRITE SV::SVEX-ALIST-P-OF-SVEX-ALIST-REDUCE))
 (50 10 (:REWRITE SV::SVEX-P-WHEN-MAYBE-SVEX-P))
 (40 20 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (30 30 (:TYPE-PRESCRIPTION SV::SVEX-P))
 (24 4 (:REWRITE SV::SVARLIST-P-OF-CDR-WHEN-SVARLIST-P))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (20 20 (:TYPE-PRESCRIPTION SV::MAYBE-SVEX-P))
 (20 20 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (20 20 (:REWRITE SV::SVEX-P-WHEN-MEMBER-EQUAL-OF-SVEXLIST-P))
 (20 10 (:REWRITE SV::MAYBE-SVEX-P-WHEN-SVEX-P))
 (19 19 (:REWRITE-QUOTED-CONSTANT SV::SVEX-ALIST-FIX-UNDER-SVEX-ALIST-EQUIV))
 (12 2 (:REWRITE SV::SVARLIST-P-OF-CAR-WHEN-SVARLIST-LIST-P))
 (12 2 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-MAP-P))
 (12 2 (:REWRITE SV::SVAR-P-OF-CAAR-WHEN-SVAR-ALIST-P))
 (10 10 (:REWRITE CONSP-OF-APPEND))
 (8 8 (:REWRITE SV::SVARLIST-FIX-UNDER-IFF))
 (4 4 (:TYPE-PRESCRIPTION SV::SVARLIST-LIST-P))
 (4 4 (:TYPE-PRESCRIPTION SV::SVAR-MAP-P))
 (4 4 (:TYPE-PRESCRIPTION SV::SVAR-ALIST-P))
 (4 4 (:REWRITE SV::SVEX-ALIST-P-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE SV::SVAR-MAP-P-WHEN-SUBSETP-EQUAL))
 (4 4 (:REWRITE SV::SVAR-ALIST-P-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE SV::SVEX-ALIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SV::SVARLIST-LIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SV::SVAR-MAP-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SV::SVAR-ALIST-P-WHEN-NOT-CONSP))
 )
(SV::FLAG-LEMMA-FOR-MEMBER-SVEX-ALIST-VARS-OF-NETEVAL-ORDERING-COMPILE
 (2126 66 (:DEFINITION MEMBER-EQUAL))
 (658 91 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (575 169 (:REWRITE SUBSETP-MEMBER . 1))
 (500 430 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (496 430 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (488 455 (:REWRITE SUBSETP-TRANS))
 (455 455 (:REWRITE SUBSETP-TRANS2))
 (209 155 (:REWRITE MEMBER-WHEN-ATOM))
 (183 183 (:REWRITE SUBSETP-MEMBER . 4))
 (183 183 (:REWRITE INTERSECTP-MEMBER . 3))
 (183 183 (:REWRITE INTERSECTP-MEMBER . 2))
 (169 169 (:REWRITE SUBSETP-MEMBER . 2))
 (156 136 (:REWRITE DEFAULT-CAR))
 (148 13 (:REWRITE SUBSETP-CAR-MEMBER))
 (132 132 (:TYPE-PRESCRIPTION SV::SVEX-KIND$INLINE))
 (112 104 (:REWRITE DEFAULT-CDR))
 (88 44 (:REWRITE SV::SVEX-VARS-WHEN-VAR))
 (88 44 (:REWRITE SV::SVEX-VARS-WHEN-QUOTE))
 (88 44 (:REWRITE SV::SVEX-VARS-WHEN-CALL))
 (84 84 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (81 3 (:REWRITE SUBSETP-INTERSECTION-EQUAL))
 (77 7 (:REWRITE ALIST-KEYS-MEMBER-HONS-ASSOC-EQUAL))
 (76 4 (:DEFINITION INTERSECTION-EQUAL))
 (70 7 (:DEFINITION HONS-ASSOC-EQUAL))
 (60 3 (:REWRITE SUBSETP-OF-CONS))
 (56 1 (:REWRITE SV::VARS-OF-SVEX-COMPOSE))
 (38 19 (:REWRITE SV::CONSP-CAR-OF-NETEVAL-ORDERING-FIX))
 (32 32 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-SUBSETP-EQUAL))
 (25 16 (:REWRITE DEFAULT-+-1))
 (23 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-NOT-CONSP))
 (16 10 (:REWRITE SV::SVEX-VARS-OF-NON-NETWORK-OF-NETEVAL-SIGORDERING-COMPILE))
 (13 4 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (8 7 (:REWRITE DEFAULT-<-1))
 (7 7 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:DEFINITION HONS-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (6 2 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (4 4 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (4 4 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (3 3 (:TYPE-PRESCRIPTION INTERSECTION-EQUAL))
 (3 3 (:REWRITE SV::RETURN-TYPE-OF-SVEX-VARS.VARS))
 (2 2 (:REWRITE-QUOTED-CONSTANT SV::SVEX-ALIST-FIX-UNDER-SVEX-ALIST-EQUIV))
 (1 1 (:REWRITE SV::SVEX-COMPOSE-LOOKUP-WHEN-SVEX-LOOKUP))
 (1 1 (:REWRITE SV::SVEX-COMPOSE-LOOKUP-WHEN-NOT-SVEX-LOOKUP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE SV::NOT-VAR-OF-LOOKUP-WHEN-NOT-VAR-OF-REDUCE))
 )
(SV::MEMBER-SVEX-ALIST-VARS-OF-NETEVAL-ORDERING-COMPILE)
(SV::MEMBER-SVEX-ALIST-VARS-OF-NETEVAL-SIGORDERING-COMPILE)
(SV::MEMBER-SVEX-ALIST-VARS-OF-NETEVAL-ORDERING-OR-NULL-COMPILE)
(SV::SVEX-LOOKUP-WHEN-NOT-MEMBER-SVEX-ALIST-KEYS
 (5 1 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (4 4 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (4 1 (:REWRITE MEMBER-WHEN-ATOM))
 (3 3 (:TYPE-PRESCRIPTION SV::SVEX-ALIST-KEYS))
 (2 2 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (1 1 (:REWRITE SUBSETP-MEMBER . 4))
 (1 1 (:REWRITE SUBSETP-MEMBER . 3))
 (1 1 (:REWRITE SUBSETP-MEMBER . 2))
 (1 1 (:REWRITE SUBSETP-MEMBER . 1))
 (1 1 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 3))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 2))
 )
(SV::SVEX-ALIST-REDUCE-SUPERSET-UNDER-SVEX-ALIST-EVAL-EQUIV
 (280 2 (:REWRITE MEMBER-OF-INTERSECTION-EQUAL))
 (212 2 (:REWRITE SV::SVEX-ALIST-KEYS-OF-SVEX-ALIST-REDUCE))
 (198 2 (:DEFINITION INTERSECTION-EQUAL))
 (135 5 (:DEFINITION MEMBER-EQUAL))
 (132 132 (:TYPE-PRESCRIPTION SV::SVARLIST-FIX$INLINE))
 (98 58 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (85 15 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (76 28 (:REWRITE SUBSETP-MEMBER . 1))
 (64 22 (:REWRITE MEMBER-WHEN-ATOM))
 (56 6 (:REWRITE SUBSETP-CAR-MEMBER))
 (45 45 (:TYPE-PRESCRIPTION SV::SVEX-ALIST-KEYS))
 (44 9 (:REWRITE SV::SVARLIST-FIX-WHEN-SVARLIST-P))
 (43 43 (:REWRITE SV::CONSP-OF-SVARLIST-FIX))
 (42 6 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (38 11 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (38 11 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (36 9 (:REWRITE DEFAULT-CDR))
 (30 30 (:TYPE-PRESCRIPTION SV::SVARLIST-P))
 (30 9 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE INTERSECTP-MEMBER . 3))
 (26 26 (:REWRITE INTERSECTP-MEMBER . 2))
 (25 25 (:REWRITE SUBSETP-MEMBER . 3))
 (23 13 (:REWRITE SUBSETP-TRANS2))
 (22 22 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (21 21 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (16 16 (:REWRITE SV::SVARLIST-P-OF-SVARLIST-FIX))
 (14 14 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (13 13 (:REWRITE SUBSETP-TRANS))
 (10 10 (:TYPE-PRESCRIPTION SV::SVAR-FIX$INLINE))
 (7 7 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVEX-FIX-UNDER-MAYBE-SVEX-EQUIV))
 (2 2 (:REWRITE SV::SVARLIST-FIX-UNDER-IFF))
 (2 2 (:REWRITE SUBSETP-REFL))
 )
(SV::SVEX-ALIST-NOT-DEPENDS-ON-NETEVAL-ORDERING-COMPILE-WHEN-KEYS-SUBSET-OF-NETWORK
 (13 2 (:REWRITE SUBSETP-TRANS))
 (6 1 (:REWRITE SV::NETEVAL-ORDERING-FIX-WHEN-NETEVAL-ORDERING-P))
 (5 1 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (4 2 (:REWRITE SV::NETEVAL-ORDERING-COMPILE-WHEN-ATOM-FIX))
 (4 1 (:REWRITE SV::SVEX-ALIST-DEPENDS-ON-WHEN-ATOM))
 (4 1 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (4 1 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (4 1 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (3 3 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-COMPILE))
 (2 2 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (2 2 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-P))
 (2 2 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (2 2 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-NOT-CONSP))
 )
(SV::SVEX-LOOKUP-OF-SVARLIST-X-SUBST-IFF
 (1384 43 (:DEFINITION MEMBER-EQUAL))
 (870 17 (:REWRITE SV::SVEX-LOOKUP-OF-SVARLIST-X-SUBST))
 (453 61 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (378 46 (:REWRITE SV::SVARLIST-FIX-WHEN-SVARLIST-P))
 (256 90 (:REWRITE SUBSETP-MEMBER . 1))
 (202 73 (:REWRITE DEFAULT-CDR))
 (196 67 (:REWRITE DEFAULT-CAR))
 (178 178 (:REWRITE SV::SVARLIST-P-WHEN-SUBSETP-EQUAL))
 (156 20 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (140 41 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (138 23 (:REWRITE SV::SVARLIST-P-OF-CDR-WHEN-SVARLIST-P))
 (122 122 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (122 41 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (118 118 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (100 10 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (90 90 (:REWRITE SUBSETP-MEMBER . 2))
 (90 89 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 (88 88 (:REWRITE SUBSETP-MEMBER . 4))
 (88 88 (:REWRITE INTERSECTP-MEMBER . 3))
 (88 88 (:REWRITE INTERSECTP-MEMBER . 2))
 (81 3 (:REWRITE SUBSETP-OF-CONS))
 (49 49 (:REWRITE SUBSETP-TRANS2))
 (49 49 (:REWRITE SUBSETP-TRANS))
 (43 43 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (19 19 (:REWRITE SV::SVARLIST-FIX-UNDER-IFF))
 (16 16 (:REWRITE-QUOTED-CONSTANT SV::SVEX-FIX-UNDER-SVEX-EQUIV))
 (16 16 (:REWRITE-QUOTED-CONSTANT SV::MAYBE-SVEX-FIX-UNDER-MAYBE-SVEX-EQUIV))
 (15 15 (:REWRITE-QUOTED-CONSTANT SV::SVEX-ALIST-FIX-UNDER-SVEX-ALIST-EQUIV))
 )
(SV::SVEX-ALIST-DEPENDS-ON-OF-SVEX-ALIST-COMPOSE-STRONG-SPLIT
 (186 6 (:REWRITE SV::SVEX-ALIST-NOT-DEPENDS-ON-WHEN-NOT-MEMBER-VARS))
 (90 6 (:DEFINITION MEMBER-EQUAL))
 (30 30 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (30 6 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (12 12 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (12 12 (:TYPE-PRESCRIPTION SV::SVAR-FIX$INLINE))
 (12 12 (:REWRITE SV::SVAR-P-WHEN-MEMBER-EQUAL-OF-SVARLIST-P))
 (12 12 (:REWRITE SUBSETP-MEMBER . 4))
 (12 12 (:REWRITE SUBSETP-MEMBER . 3))
 (12 12 (:REWRITE SUBSETP-MEMBER . 2))
 (12 12 (:REWRITE SUBSETP-MEMBER . 1))
 (12 12 (:REWRITE MEMBER-WHEN-ATOM))
 (12 12 (:REWRITE INTERSECTP-MEMBER . 3))
 (12 12 (:REWRITE INTERSECTP-MEMBER . 2))
 (6 6 (:REWRITE SV::SVEX-ALIST-DEPENDS-ON-WHEN-ATOM))
 (6 6 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 )
(SV::SVEX-ALIST-NOT-DEPENDS-ON-NETEVAL-ORDERING-COMPILE-X-SUBST
 (453 32 (:REWRITE SUBSETP-MEMBER . 2))
 (412 9 (:REWRITE ALIST-KEYS-MEMBER-HONS-ASSOC-EQUAL))
 (403 9 (:REWRITE SV::HONS-ASSOC-EQUAL-OF-NETEVAL-ORDERING-FIX))
 (208 18 (:DEFINITION HONS-ASSOC-EQUAL))
 (202 10 (:DEFINITION MEMBER-EQUAL))
 (172 2 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (99 9 (:REWRITE SV::NETEVAL-SIGORDERING-FIX-WHEN-NETEVAL-SIGORDERING-P))
 (90 90 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (77 77 (:REWRITE DEFAULT-CAR))
 (68 32 (:REWRITE SUBSETP-MEMBER . 1))
 (68 26 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (60 28 (:REWRITE SUBSETP-TRANS2))
 (59 59 (:REWRITE DEFAULT-CDR))
 (58 18 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (54 9 (:REWRITE SV::NETEVAL-SIGORDERING-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-NETEVAL-ORDERING-P))
 (48 48 (:TYPE-PRESCRIPTION SV::SVAR-FIX$INLINE))
 (44 26 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (38 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (34 10 (:REWRITE SV::SVEX-ALIST-DEPENDS-ON-WHEN-ATOM))
 (34 4 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (32 32 (:REWRITE SUBSETP-MEMBER . 4))
 (32 32 (:REWRITE INTERSECTP-MEMBER . 3))
 (32 32 (:REWRITE INTERSECTP-MEMBER . 2))
 (32 18 (:DEFINITION HONS-EQUAL))
 (28 28 (:REWRITE SUBSETP-TRANS))
 (24 24 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-P))
 (24 24 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-SUBSETP-EQUAL))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (20 20 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (19 19 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (18 18 (:TYPE-PRESCRIPTION SV::NETEVAL-SIGORDERING-P))
 (18 3 (:REWRITE SV::NETEVAL-ORDERING-FIX-WHEN-NETEVAL-ORDERING-P))
 (15 15 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-COMPILE))
 (12 12 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-NOT-CONSP))
 (12 4 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (12 3 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (9 9 (:TYPE-PRESCRIPTION SV::SVARLIST-X-SUBST))
 (9 9 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (9 9 (:TYPE-PRESCRIPTION SV::NETEVAL-SIGORDERING-FIX$INLINE))
 (9 9 (:TYPE-PRESCRIPTION SV::CONSP-OF-NETEVAL-SIGORDERING-FIX))
 (8 4 (:REWRITE SV::NETEVAL-ORDERING-COMPILE-WHEN-ATOM-FIX))
 )
(SV::SVEX-ALIST-NOT-DEPENDS-ON-NETEVAL-ORDERING-COMPILE-X-SUBST-FREE
 (258 3 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (243 12 (:REWRITE SUBSETP-MEMBER . 2))
 (226 5 (:REWRITE ALIST-KEYS-MEMBER-HONS-ASSOC-EQUAL))
 (221 5 (:REWRITE SV::HONS-ASSOC-EQUAL-OF-NETEVAL-ORDERING-FIX))
 (108 10 (:DEFINITION HONS-ASSOC-EQUAL))
 (57 3 (:REWRITE SUBSETP-CAR-MEMBER))
 (55 5 (:REWRITE SV::NETEVAL-SIGORDERING-FIX-WHEN-NETEVAL-SIGORDERING-P))
 (54 14 (:REWRITE SUBSETP-TRANS2))
 (50 50 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (49 13 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (48 12 (:REWRITE SUBSETP-MEMBER . 1))
 (43 43 (:REWRITE DEFAULT-CAR))
 (36 36 (:TYPE-PRESCRIPTION SV::SVEX-ALIST-KEYS))
 (33 33 (:REWRITE DEFAULT-CDR))
 (30 5 (:REWRITE SV::NETEVAL-SIGORDERING-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-NETEVAL-ORDERING-P))
 (27 2 (:DEFINITION MEMBER-EQUAL))
 (24 9 (:REWRITE MEMBER-WHEN-ATOM))
 (22 13 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (21 21 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (18 6 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (15 3 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (14 14 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-P))
 (14 14 (:REWRITE SUBSETP-TRANS))
 (14 14 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-SUBSETP-EQUAL))
 (14 10 (:DEFINITION HONS-EQUAL))
 (13 13 (:REWRITE SUBSETP-MEMBER . 4))
 (13 13 (:REWRITE INTERSECTP-MEMBER . 3))
 (13 13 (:REWRITE INTERSECTP-MEMBER . 2))
 (12 12 (:TYPE-PRESCRIPTION SV::SVAR-FIX$INLINE))
 (12 2 (:REWRITE SV::NETEVAL-ORDERING-FIX-WHEN-NETEVAL-ORDERING-P))
 (10 10 (:TYPE-PRESCRIPTION SV::NETEVAL-SIGORDERING-P))
 (8 2 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (7 7 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (7 7 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-NOT-CONSP))
 (6 6 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (5 5 (:TYPE-PRESCRIPTION SV::NETEVAL-SIGORDERING-FIX$INLINE))
 (5 5 (:TYPE-PRESCRIPTION SV::CONSP-OF-NETEVAL-SIGORDERING-FIX))
 (4 2 (:REWRITE SV::NETEVAL-ORDERING-COMPILE-WHEN-ATOM-FIX))
 (3 3 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 )
(SV::REWRITE-SVEX-ALIST-KEYS-WHEN-EVAL-EQUIV)
(SV::SVEX-ALIST-NOT-DEPENDS-ON-OF-NETEVALCOMP
 (258 3 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (243 12 (:REWRITE SUBSETP-MEMBER . 2))
 (226 5 (:REWRITE ALIST-KEYS-MEMBER-HONS-ASSOC-EQUAL))
 (221 5 (:REWRITE SV::HONS-ASSOC-EQUAL-OF-NETEVAL-ORDERING-FIX))
 (108 10 (:DEFINITION HONS-ASSOC-EQUAL))
 (57 3 (:REWRITE SUBSETP-CAR-MEMBER))
 (55 5 (:REWRITE SV::NETEVAL-SIGORDERING-FIX-WHEN-NETEVAL-SIGORDERING-P))
 (53 13 (:REWRITE SUBSETP-TRANS2))
 (50 50 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (48 12 (:REWRITE SUBSETP-MEMBER . 1))
 (45 12 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (43 43 (:REWRITE DEFAULT-CAR))
 (33 33 (:TYPE-PRESCRIPTION SV::SVEX-ALIST-KEYS))
 (33 33 (:REWRITE DEFAULT-CDR))
 (30 5 (:REWRITE SV::NETEVAL-SIGORDERING-P-OF-CDR-OF-HONS-ASSOC-EQUAL-WHEN-NETEVAL-ORDERING-P))
 (27 2 (:DEFINITION MEMBER-EQUAL))
 (24 9 (:REWRITE MEMBER-WHEN-ATOM))
 (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
 (18 12 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (18 6 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (15 3 (:REWRITE SV::SVAR-FIX-WHEN-SVAR-P))
 (14 10 (:DEFINITION HONS-EQUAL))
 (13 13 (:REWRITE SUBSETP-TRANS))
 (13 13 (:REWRITE SUBSETP-MEMBER . 4))
 (13 13 (:REWRITE INTERSECTP-MEMBER . 3))
 (13 13 (:REWRITE INTERSECTP-MEMBER . 2))
 (12 12 (:TYPE-PRESCRIPTION SV::SVAR-FIX$INLINE))
 (12 12 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-P))
 (12 12 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-SUBSETP-EQUAL))
 (10 10 (:TYPE-PRESCRIPTION SV::NETEVAL-SIGORDERING-P))
 (7 7 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (6 6 (:TYPE-PRESCRIPTION SV::SVAR-P))
 (6 6 (:REWRITE SV::NETEVAL-ORDERING-P-WHEN-NOT-CONSP))
 (6 1 (:REWRITE SV::NETEVAL-ORDERING-FIX-WHEN-NETEVAL-ORDERING-P))
 (5 5 (:TYPE-PRESCRIPTION SV::NETEVAL-SIGORDERING-FIX$INLINE))
 (5 5 (:TYPE-PRESCRIPTION SV::CONSP-OF-NETEVAL-SIGORDERING-FIX))
 (4 4 (:TYPE-PRESCRIPTION SV::NETEVAL-ORDERING-FIX$INLINE))
 (4 1 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 (3 3 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (2 1 (:REWRITE SV::NETEVAL-ORDERING-COMPILE-WHEN-ATOM-FIX))
 )
(SV::SVEX-ALIST-DEPENDENCIES-OF-NETEVALCOMP
 (488 8 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (232 16 (:REWRITE SUBSETP-CAR-MEMBER))
 (225 35 (:REWRITE SUBSETP-MEMBER . 2))
 (129 39 (:REWRITE SUBSETP-TRANS2))
 (117 117 (:TYPE-PRESCRIPTION SV::SVEX-ALIST-KEYS))
 (116 35 (:REWRITE SUBSETP-MEMBER . 1))
 (112 37 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (56 20 (:REWRITE MEMBER-WHEN-ATOM))
 (49 37 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (49 4 (:DEFINITION MEMBER-EQUAL))
 (48 16 (:REWRITE SV::SVAR-P-OF-CAR-WHEN-SVARLIST-P))
 (39 39 (:REWRITE SUBSETP-TRANS))
 (26 26 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (25 25 (:REWRITE SUBSETP-MEMBER . 4))
 (25 25 (:REWRITE INTERSECTP-MEMBER . 3))
 (25 25 (:REWRITE INTERSECTP-MEMBER . 2))
 (25 1 (:REWRITE SV::SVEX-ALIST-NOT-DEPENDS-ON-WHEN-NOT-MEMBER-VARS))
 (20 20 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE SV::REWRITE-SVEX-ALIST-KEYS-WHEN-EVAL-EQUIV))
 (3 3 (:TYPE-PRESCRIPTION SV::SVEX-ALIST-DEPENDENCIES))
 (3 3 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (1 1 (:REWRITE SV::SVEX-ALIST-NOT-DEPENDS-ON-NETEVAL-ORDERING-COMPILE-X-SUBST-FREE))
 (1 1 (:REWRITE SV::SVEX-ALIST-DEPENDS-ON-WHEN-ATOM))
 )
