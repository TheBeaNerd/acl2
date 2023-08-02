(SBYTE16-LISTP)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(SBYTE16-LISTP-OF-CONS)
(SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP)
(SBYTE16-LISTP-WHEN-NOT-CONSP)
(SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP)
(TRUE-LISTP-WHEN-SBYTE16-LISTP-COMPOUND-RECOGNIZER)
(SBYTE16-LISTP-OF-LIST-FIX)
(SBYTE16-LISTP-OF-SFIX)
(SBYTE16-LISTP-OF-INSERT)
(SBYTE16-LISTP-OF-DELETE)
(SBYTE16-LISTP-OF-MERGESORT)
(SBYTE16-LISTP-OF-UNION)
(SBYTE16-LISTP-OF-INTERSECT-1)
(SBYTE16-LISTP-OF-INTERSECT-2)
(SBYTE16-LISTP-OF-DIFFERENCE)
(SBYTE16-LISTP-OF-DUPLICATED-MEMBERS)
(SBYTE16-LISTP-OF-REV)
(SBYTE16-LISTP-OF-APPEND)
(SBYTE16-LISTP-OF-RCONS)
(SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP)
(SBYTE16-LISTP-WHEN-SUBSETP-EQUAL)
(SBYTE16-LISTP-OF-SET-DIFFERENCE-EQUAL)
(SBYTE16-LISTP-OF-INTERSECTION-EQUAL-1)
(SBYTE16-LISTP-OF-INTERSECTION-EQUAL-2)
(SBYTE16-LISTP-OF-UNION-EQUAL)
(SBYTE16-LISTP-OF-TAKE)
(SBYTE16-LISTP-OF-REPEAT)
(SBYTE16P-OF-NTH-WHEN-SBYTE16-LISTP)
(SBYTE16-LISTP-OF-UPDATE-NTH)
(SBYTE16-LISTP-OF-BUTLAST)
(SBYTE16-LISTP-OF-NTHCDR)
(SBYTE16-LISTP-OF-LAST)
(SBYTE16-LISTP-OF-REMOVE)
(SBYTE16-LISTP-OF-REVAPPEND)
(SBYTE16-LIST-FIX$INLINE)
(SBYTE16-LISTP-OF-SBYTE16-LIST-FIX
 (30 1 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (22 2 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (18 10 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (15 1 (:DEFINITION SBYTE16-LISTP))
 (12 6 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (12 5 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION SBYTE16P))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2 2 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 (2 1 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 )
(SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP
 (32 4 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (28 24 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (13 3 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (9 6 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 )
(SBYTE16-LIST-FIX$INLINE
 (8 8 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (6 1 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (4 4 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (2 2 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 )
(SBYTE16-LIST-EQUIV$INLINE)
(SBYTE16-LIST-EQUIV-IS-AN-EQUIVALENCE)
(SBYTE16-LIST-EQUIV-IMPLIES-EQUAL-SBYTE16-LIST-FIX-1)
(SBYTE16-LIST-FIX-UNDER-SBYTE16-LIST-EQUIV)
(EQUAL-OF-SBYTE16-LIST-FIX-1-FORWARD-TO-SBYTE16-LIST-EQUIV)
(EQUAL-OF-SBYTE16-LIST-FIX-2-FORWARD-TO-SBYTE16-LIST-EQUIV)
(SBYTE16-LIST-EQUIV-OF-SBYTE16-LIST-FIX-1-FORWARD)
(SBYTE16-LIST-EQUIV-OF-SBYTE16-LIST-FIX-2-FORWARD)
(CAR-OF-SBYTE16-LIST-FIX-X-UNDER-SBYTE16-EQUIV
 (33 3 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (18 3 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (18 2 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (12 12 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (12 12 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION SBYTE16P))
 (6 6 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (6 6 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (6 1 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (3 3 (:TYPE-PRESCRIPTION SBYTE16-LIST-FIX$INLINE))
 )
(CAR-SBYTE16-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-SBYTE16-EQUIV)
(CDR-OF-SBYTE16-LIST-FIX-X-UNDER-SBYTE16-LIST-EQUIV
 (41 3 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (22 2 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (20 20 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (12 2 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SBYTE16P))
 (4 4 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 )
(CDR-SBYTE16-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-SBYTE16-LIST-EQUIV)
(CONS-OF-SBYTE16-FIX-X-UNDER-SBYTE16-LIST-EQUIV
 (34 4 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (17 2 (:REWRITE SBYTE16-LISTP-OF-CONS))
 (10 10 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (8 8 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (6 6 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (5 5 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 )
(CONS-SBYTE16-EQUIV-CONGRUENCE-ON-X-UNDER-SBYTE16-LIST-EQUIV)
(CONS-OF-SBYTE16-LIST-FIX-Y-UNDER-SBYTE16-LIST-EQUIV
 (20 2 (:REWRITE SBYTE16-LISTP-OF-CONS))
 (8 8 (:TYPE-PRESCRIPTION SBYTE16P))
 (8 8 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (8 8 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (6 2 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (5 4 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 )
(CONS-SBYTE16-LIST-EQUIV-CONGRUENCE-ON-Y-UNDER-SBYTE16-LIST-EQUIV)
(CONSP-OF-SBYTE16-LIST-FIX
 (18 2 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (11 1 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (8 8 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (8 8 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (6 1 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (4 4 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION SBYTE16P))
 (2 2 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 )
(SBYTE16-LIST-FIX-UNDER-IFF
 (18 2 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (11 1 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (8 8 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (8 8 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (6 1 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (4 4 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION SBYTE16P))
 (2 2 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 )
(SBYTE16-LIST-FIX-OF-CONS
 (21 3 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (9 1 (:REWRITE SBYTE16-LISTP-OF-CONS))
 (6 6 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (6 2 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (4 4 (:TYPE-PRESCRIPTION SBYTE16P))
 (4 4 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (4 4 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (3 3 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 )
(LEN-OF-SBYTE16-LIST-FIX
 (35 4 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (14 14 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (13 13 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (12 2 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (11 1 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (7 7 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (6 1 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SBYTE16P))
 (2 2 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (1 1 (:REWRITE FTY::EQUAL-OF-LEN))
 )
(SBYTE16-LIST-FIX-OF-APPEND
 (114 10 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (58 2 (:REWRITE SBYTE16-LISTP-OF-APPEND))
 (40 36 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (29 29 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (24 2 (:REWRITE SBYTE16-LISTP-OF-LIST-FIX))
 (22 16 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (14 4 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (12 2 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (6 1 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION SBYTE16P))
 (2 2 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 )
(SBYTE16-LIST-FIX-OF-REPEAT
 (20 2 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (16 4 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (12 2 (:REWRITE SBYTE16-LISTP-OF-REPEAT))
 (10 10 (:TYPE-PRESCRIPTION SBYTE16P))
 (10 10 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (1 1 (:REWRITE-QUOTED-CONSTANT SBYTE16-LIST-FIX-UNDER-SBYTE16-LIST-EQUIV))
 )
(LIST-EQUIV-REFINES-SBYTE16-LIST-EQUIV
 (146 14 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (112 8 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (88 18 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (72 72 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (72 8 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (70 70 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (36 36 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (16 16 (:TYPE-PRESCRIPTION SBYTE16P))
 (16 16 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(NTH-OF-SBYTE16-LIST-FIX
 (222 16 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (180 18 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (124 24 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (112 11 (:REWRITE SBYTE16P-OF-NTH-WHEN-SBYTE16-LISTP))
 (106 106 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (53 53 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (32 32 (:TYPE-PRESCRIPTION SBYTE16P))
 (32 32 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (30 5 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (29 22 (:REWRITE DEFAULT-+-2))
 (24 18 (:REWRITE DEFAULT-CDR))
 (22 22 (:REWRITE DEFAULT-+-1))
 (19 7 (:REWRITE ZP-OPEN))
 (18 14 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE CONSP-OF-SBYTE16-LIST-FIX))
 (14 14 (:REWRITE DEFAULT-<-1))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (10 4 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE-QUOTED-CONSTANT SBYTE16-FIX-UNDER-SBYTE16-EQUIV))
 )
(SBYTE16-LIST-EQUIV-IMPLIES-SBYTE16-LIST-EQUIV-APPEND-1
 (269 32 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (205 17 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (128 128 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (126 126 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (120 17 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (117 22 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (64 64 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (34 34 (:TYPE-PRESCRIPTION SBYTE16P))
 (34 34 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(SBYTE16-LIST-EQUIV-IMPLIES-SBYTE16-LIST-EQUIV-APPEND-2
 (393 46 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (322 26 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (204 39 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (192 26 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (190 190 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (189 189 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (95 95 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (52 52 (:TYPE-PRESCRIPTION SBYTE16P))
 (52 52 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (4 4 (:REWRITE CONSP-OF-SBYTE16-LIST-FIX))
 )
(SBYTE16-LIST-EQUIV-IMPLIES-SBYTE16-LIST-EQUIV-NTHCDR-2
 (298 20 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (208 39 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (198 198 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (198 20 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (40 40 (:TYPE-PRESCRIPTION SBYTE16P))
 (40 40 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 )
(SBYTE16-LIST-EQUIV-IMPLIES-SBYTE16-LIST-EQUIV-TAKE-2
 (553 38 (:REWRITE SBYTE16-LIST-FIX-WHEN-SBYTE16-LISTP))
 (432 28 (:REWRITE SBYTE16-FIX-WHEN-SBYTE16P))
 (304 51 (:REWRITE SBYTE16-LISTP-OF-CDR-WHEN-SBYTE16-LISTP))
 (296 26 (:REWRITE SBYTE16P-OF-CAR-WHEN-SBYTE16-LISTP))
 (236 236 (:TYPE-PRESCRIPTION SBYTE16-LISTP))
 (236 236 (:REWRITE SBYTE16-LISTP-WHEN-SUBSETP-EQUAL))
 (229 24 (:REWRITE SBYTE16-LISTP-OF-TAKE))
 (136 118 (:REWRITE SBYTE16-LISTP-WHEN-NOT-CONSP))
 (66 66 (:TYPE-PRESCRIPTION SBYTE16P))
 (66 66 (:REWRITE SBYTE16P-WHEN-MEMBER-EQUAL-OF-SBYTE16-LISTP))
 (18 18 (:TYPE-PRESCRIPTION NFIX))
 (12 12 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE-QUOTED-CONSTANT SBYTE16-LIST-FIX-UNDER-SBYTE16-LIST-EQUIV))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(SBYTE16-LISTP-FORWARD-SIGNED-BYTE-LISTP)
(SBYTE16-LISTP-REWRITE-SIGNED-BYTE-LISTP)
(SIGNED-BYTE-LISTP-REWRITE-SBYTE16-LISTP)
(TRUE-LISTP-WHEN-SBYTE16-LISTP-REWRITE
 (2 2 (:DEFINITION TRUE-LISTP))
 )
(SBYTE16-LIST-FIX-OF-TAKE)
(SBYTE16-LIST-FIX-OF-RCONS)
