(C::VALUE-STRUCT-READ-AUX
 (4 4 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 )
(C::VALUE-RESULTP-OF-VALUE-STRUCT-READ-AUX
 (66 11 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (36 9 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (33 11 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (22 22 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (20 20 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (18 18 (:TYPE-PRESCRIPTION C::IDENTP))
 (9 9 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::LEMMA
 (179 5 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (120 120 (:TYPE-PRESCRIPTION C::TYPE-KIND$INLINE))
 (36 6 (:REWRITE C::CDR-OF-MEMBER-TYPES-OF-MEMBER-VALUES))
 (33 2 (:REWRITE C::TYPE-OPTIONP-WHEN-TYPEP))
 (30 12 (:REWRITE C::CAR-OF-MEMBER-TYPES-OF-MEMBER-VALUES))
 (25 25 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-VOID))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-USHORT))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-ULONG))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-ULLONG))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-UINT))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-UCHAR))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-SSHORT))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-SLONG))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-SLLONG))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-SINT))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-SCHAR))
 (20 10 (:REWRITE C::TYPE-FIX-WHEN-CHAR))
 (7 7 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (7 7 (:REWRITE-QUOTED-CONSTANT C::MEMBER-TYPE-LIST-FIX-UNDER-MEMBER-TYPE-LIST-EQUIV))
 (6 6 (:REWRITE C::CONSP-OF-MEMBER-TYPES-OF-MEMBER-VALUES))
 (5 5 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (2 2 (:REWRITE C::TYPE-OPTIONP-WHEN-IN-TYPE-OPTION-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE C::TYPE-OPTIONP-OF-MEMBER-TYPE-LOOKUP))
 )
(C::VALUE-STRUCT-READ-AUX-WHEN-MEMBER-TYPE-LOOKUP
 (34 2 (:DEFINITION C::VALUE-STRUCT-READ-AUX))
 (16 4 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (8 8 (:TYPE-PRESCRIPTION C::MEMBER-VALUE->NAME$INLINE))
 (8 8 (:TYPE-PRESCRIPTION C::IDENTP))
 (8 8 (:TYPE-PRESCRIPTION C::IDENT-FIX$INLINE))
 (7 1 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (4 4 (:REWRITE C::MEMBER-TYPES-OF-MEMBER-VALUES-WHEN-NOT-CONSP))
 (4 4 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (1 1 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (1 1 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE C::TYPE-OPTIONP-OF-MEMBER-TYPE-LOOKUP))
 )
(C::VALUE-STRUCT-READ-AUX-OF-IDENT-FIX-NAME
 (11 11 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::VALUE-STRUCT-READ-AUX-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::VALUE-STRUCT-READ-AUX-OF-MEMBER-VALUE-LIST-FIX-MEMBERS
 (468 120 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (241 33 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (232 232 (:TYPE-PRESCRIPTION C::IDENTP))
 (116 116 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (82 82 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (48 8 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (41 41 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 )
(C::VALUE-STRUCT-READ-AUX-MEMBER-VALUE-LIST-EQUIV-CONGRUENCE-ON-MEMBERS)
(C::VALUE-STRUCT-READ)
(C::VALUE-RESULTP-OF-VALUE-STRUCT-READ)
(C::VALUE-STRUCT-READ-OF-IDENT-FIX-NAME)
(C::VALUE-STRUCT-READ-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::VALUE-STRUCT-READ-OF-VALUE-FIX-STRUCT)
(C::VALUE-STRUCT-READ-VALUE-EQUIV-CONGRUENCE-ON-STRUCT)
(C::VALUE-STRUCT-WRITE-AUX
 (36 1 (:DEFINITION C::VALUE-STRUCT-WRITE-AUX))
 (7 1 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (7 1 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (6 6 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (3 1 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (3 1 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (2 2 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (1 1 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (1 1 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 )
(C::MEMBER-VALUE-LIST-RESULTP-OF-VALUE-STRUCT-WRITE-AUX
 (37 10 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (34 1 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (20 1 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (19 1 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (18 18 (:TYPE-PRESCRIPTION C::IDENTP))
 (14 14 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (14 1 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (10 7 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (10 1 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (9 9 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (5 1 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::VALUEP))
 (3 1 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (2 2 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (2 2 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (2 2 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (2 2 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (2 2 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (2 1 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 )
(C::MEMBER-VALUE-LISTP-OF-VALUE-STRUCT-WRITE-AUX
 (530 20 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (448 15 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (356 41 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (294 20 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (232 58 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (176 40 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (140 14 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (130 25 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (116 116 (:TYPE-PRESCRIPTION C::IDENTP))
 (104 52 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (104 8 (:REWRITE SUBSETP-CAR-MEMBER))
 (92 83 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (58 58 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (55 55 (:REWRITE SUBSETP-TRANS2))
 (55 55 (:REWRITE SUBSETP-TRANS))
 (55 52 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (50 50 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (45 15 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (40 40 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (30 30 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (19 19 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (9 9 (:REWRITE SUBSETP-MEMBER . 2))
 (9 9 (:REWRITE SUBSETP-MEMBER . 1))
 (9 1 (:REWRITE SUBSETP-OF-CONS))
 )
(C::MEMBER-VALUE-LIST->NAME-LIST-OF-STRUCT-WRITE-AUX
 (340 85 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (287 19 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (246 14 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (240 40 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (192 19 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (180 18 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (170 170 (:TYPE-PRESCRIPTION C::IDENTP))
 (146 146 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (85 85 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (73 73 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (66 66 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (54 18 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (38 38 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (38 38 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (36 36 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (1 1 (:TYPE-PRESCRIPTION C::MEMBER-VALUE-LIST-FIX$INLINE))
 )
(C::VALUE-STRUCT-READ-AUX-OF-VALUE-STRUCT-WRITE-AUX
 (615 156 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (360 24 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (306 306 (:TYPE-PRESCRIPTION C::IDENTP))
 (300 17 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (294 49 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (240 24 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (180 180 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (153 153 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (94 32 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (90 90 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (80 80 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (62 62 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (48 48 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (48 48 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION C::MEMBER-VALUE-LIST-FIX$INLINE))
 )
(C::LEMMA
 (694 28 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (620 26 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (503 62 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (364 10 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (354 26 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (204 204 (:TYPE-PRESCRIPTION C::TYPE-KIND$INLINE))
 (188 52 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (172 28 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (164 33 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (160 126 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (154 28 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (124 62 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (104 8 (:REWRITE SUBSETP-CAR-MEMBER))
 (102 102 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (93 31 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (89 25 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (74 62 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (72 4 (:REWRITE C::TYPE-OPTIONP-WHEN-TYPEP))
 (66 66 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (66 66 (:REWRITE SUBSETP-TRANS2))
 (66 66 (:REWRITE SUBSETP-TRANS))
 (62 62 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (58 58 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (52 52 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-VOID))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-USHORT))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-ULONG))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-ULLONG))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-UINT))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-UCHAR))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-SSHORT))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-SLONG))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-SLLONG))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-SINT))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-SCHAR))
 (34 17 (:REWRITE C::TYPE-FIX-WHEN-CHAR))
 (23 2 (:REWRITE SUBSETP-OF-CONS))
 (21 21 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (14 14 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (14 14 (:REWRITE-QUOTED-CONSTANT C::MEMBER-TYPE-LIST-FIX-UNDER-MEMBER-TYPE-LIST-EQUIV))
 (10 10 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (10 10 (:REWRITE SUBSETP-MEMBER . 2))
 (10 10 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE C::TYPE-OPTIONP-WHEN-IN-TYPE-OPTION-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE C::TYPE-OPTIONP-OF-MEMBER-TYPE-LOOKUP))
 (1 1 (:REWRITE C::CONSP-OF-MEMBER-VALUE-LIST-FIX))
 )
(C::VALUE-STRUCT-WRITE-AUX-WHEN-MEMBER-TYPE-LOOKUP
 (67 1 (:DEFINITION C::VALUE-STRUCT-WRITE-AUX))
 (15 3 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (12 3 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (12 1 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (11 1 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (10 1 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (9 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (7 1 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (6 6 (:TYPE-PRESCRIPTION C::IDENTP))
 (6 6 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (6 6 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (6 1 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (5 5 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:TYPE-PRESCRIPTION C::MEMBER-VALUE->NAME$INLINE))
 (4 4 (:TYPE-PRESCRIPTION C::IDENT-FIX$INLINE))
 (4 4 (:REWRITE C::MEMBER-TYPES-OF-MEMBER-VALUES-WHEN-NOT-CONSP))
 (3 3 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (3 1 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (2 2 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (2 2 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (2 2 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (1 1 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE C::TYPE-OPTIONP-OF-MEMBER-TYPE-LOOKUP))
 )
(C::VALUE-STRUCT-WRITE-AUX-OF-IDENT-FIX-NAME
 (60 4 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (56 4 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (48 8 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (40 4 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (36 4 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (32 32 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (23 23 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (20 4 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (16 16 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (12 4 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (8 8 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (8 8 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (8 8 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (8 8 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (8 4 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 )
(C::VALUE-STRUCT-WRITE-AUX-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::VALUE-STRUCT-WRITE-AUX-OF-VALUE-FIX-VAL
 (82 22 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (60 4 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (56 10 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (56 4 (:REWRITE C::MEMBER-VALUE-FIX-WHEN-MEMBER-VALUEP))
 (48 8 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (40 40 (:TYPE-PRESCRIPTION C::IDENTP))
 (36 4 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (32 32 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (26 10 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (20 20 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (20 20 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (16 16 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (14 14 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (12 4 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (8 8 (:TYPE-PRESCRIPTION C::MEMBER-VALUEP))
 (8 8 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (8 8 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 )
(C::VALUE-STRUCT-WRITE-AUX-VALUE-EQUIV-CONGRUENCE-ON-VAL)
(C::VALUE-STRUCT-WRITE-AUX-OF-MEMBER-VALUE-LIST-FIX-MEMBERS
 (7723 736 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (6481 956 (:REWRITE C::MEMBER-VALUE-LISTP-OF-CDR-WHEN-MEMBER-VALUE-LISTP))
 (4095 323 (:REWRITE C::MEMBER-VALUEP-OF-CAR-WHEN-MEMBER-VALUE-LISTP))
 (3567 903 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (3498 3498 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (2971 298 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (1776 1776 (:TYPE-PRESCRIPTION C::IDENTP))
 (1749 1749 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 (1485 297 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (890 298 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (888 888 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (668 668 (:REWRITE C::MEMBER-VALUEP-WHEN-MEMBER-EQUAL-OF-MEMBER-VALUE-LISTP))
 (594 594 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (594 594 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (594 297 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (592 592 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (164 164 (:REWRITE C::RETURN-TYPE-OF-MEMBER-VALUE-LIST-FIX.NEWX))
 )
(C::VALUE-STRUCT-WRITE-AUX-MEMBER-VALUE-LIST-EQUIV-CONGRUENCE-ON-MEMBERS)
(C::VALUE-STRUCT-WRITE)
(C::VALUE-RESULTP-OF-VALUE-STRUCT-WRITE)
(C::VALUE-KIND-OF-VALUE-STRUCT-WRITE)
(C::VALUEP-OF-VALUE-STRUCT-WRITE
 (32 4 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (26 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (8 8 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 )
(C::VALUE-STRUCT-READ-OF-VALUE-STRUCT-WRITE
 (39 6 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (37 10 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (30 3 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (20 2 (:REWRITE C::MEMBER-VALUE-LIST-FIX-WHEN-MEMBER-VALUE-LISTP))
 (18 18 (:TYPE-PRESCRIPTION C::IDENTP))
 (12 12 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (9 9 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (9 9 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (7 3 (:REWRITE C::REMOVE-FLEXIBLE-ARRAY-MEMBER-WHEN-ABSENT))
 (4 4 (:TYPE-PRESCRIPTION C::MEMBER-VALUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION C::FLEXIBLE-ARRAY-MEMBER-P))
 (4 4 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-SUBSETP-EQUAL))
 (4 2 (:REWRITE C::MEMBER-VALUE-LISTP-WHEN-NOT-CONSP))
 )
(C::VALUE-STRUCT-WRITE-OF-IDENT-FIX-NAME)
(C::VALUE-STRUCT-WRITE-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::VALUE-STRUCT-WRITE-OF-VALUE-FIX-VAL)
(C::VALUE-STRUCT-WRITE-VALUE-EQUIV-CONGRUENCE-ON-VAL)
(C::VALUE-STRUCT-WRITE-OF-VALUE-FIX-STRUCT
 (10 1 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (5 1 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (2 2 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (2 2 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (2 1 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 )
(C::VALUE-STRUCT-WRITE-VALUE-EQUIV-CONGRUENCE-ON-STRUCT)
