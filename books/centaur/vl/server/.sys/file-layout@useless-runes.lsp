(TMP-DEFTYPES-STRINGP-OF-STR-FIX$INLINE)
(TMP-DEFTYPES-NATP-OF-NFIX)
(TMP-DEFTYPES-NFIX-WHEN-NATP
 (32 3 (:REWRITE VL::NATP-WHEN-POSP))
 (14 1 (:REWRITE NATP-POSP))
 (13 1 (:REWRITE POSP-RW))
 (12 2 (:REWRITE VL::INTEGERP-WHEN-NATP))
 (7 3 (:REWRITE NATP-RW))
 (6 6 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (6 6 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 4 (:TYPE-PRESCRIPTION POSP))
 (4 4 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (2 2 (:REWRITE VL::POSP-WHEN-MEMBER-EQUAL-OF-POS-LISTP))
 (2 2 (:LINEAR LISTPOS-COMPLETE))
 )
(VL::VL-ZIPINFO-P
 (296 22 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (230 22 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (230 22 (:REWRITE ALISTP-WHEN-ATOM))
 (127 23 (:REWRITE DEFAULT-CAR))
 (110 110 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (102 102 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (56 10 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (56 8 (:REWRITE STRIP-CARS-WHEN-ATOM))
 (44 44 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (36 5 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (33 33 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 2))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 1))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (33 33 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (33 33 (:REWRITE CONSP-BY-LEN))
 (32 4 (:REWRITE VL::CONSP-OF-CAR-WHEN-VL-COMMENTMAP-P))
 (30 30 (:REWRITE DEFAULT-CDR))
 (27 27 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (27 27 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (24 24 (:REWRITE VL::ALISTP-WHEN-ALL-HAVE-LEN))
 (23 23 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (20 20 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (20 10 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (20 10 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (12 12 (:TYPE-PRESCRIPTION VL::VL-COMMENTMAP-P))
 (10 10 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (10 10 (:TYPE-PRESCRIPTION CONS-LISTP))
 (10 10 (:TYPE-PRESCRIPTION ATOM-LISTP))
 (10 5 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (8 8 (:REWRITE VL::VL-COMMENTMAP-P-WHEN-SUBSETP-EQUAL))
 (8 8 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (8 4 (:REWRITE VL::VL-COMMENTMAP-P-OF-CDR-WHEN-VL-COMMENTMAP-P))
 (8 2 (:REWRITE STRIP-CARS-UNDER-IFF))
 (5 5 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (5 5 (:REWRITE SET::IN-SET))
 (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (4 4 (:REWRITE VL::VL-COMMENTMAP-P-WHEN-NOT-CONSP))
 )
(VL::CONSP-WHEN-VL-ZIPINFO-P)
(VL::TAG-WHEN-VL-ZIPINFO-P)
(VL::VL-ZIPINFO-P-WHEN-WRONG-TAG)
(VL::VL-ZIPINFO-FIX$INLINE)
(VL::VL-ZIPINFO-P-OF-VL-ZIPINFO-FIX
 (28 28 (:REWRITE STR-FIX-WHEN-STRINGP))
 (20 12 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(VL::VL-ZIPINFO-FIX$INLINE
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(VL::VL-ZIPINFO-EQUIV$INLINE)
(VL::VL-ZIPINFO-EQUIV-IS-AN-EQUIVALENCE)
(VL::VL-ZIPINFO-EQUIV-IMPLIES-EQUAL-VL-ZIPINFO-FIX-1)
(VL::VL-ZIPINFO-FIX-UNDER-VL-ZIPINFO-EQUIV)
(VL::EQUAL-OF-VL-ZIPINFO-FIX-1-FORWARD-TO-VL-ZIPINFO-EQUIV)
(VL::EQUAL-OF-VL-ZIPINFO-FIX-2-FORWARD-TO-VL-ZIPINFO-EQUIV)
(VL::VL-ZIPINFO-EQUIV-OF-VL-ZIPINFO-FIX-1-FORWARD)
(VL::VL-ZIPINFO-EQUIV-OF-VL-ZIPINFO-FIX-2-FORWARD)
(VL::TAG-OF-VL-ZIPINFO-FIX)
(VL::VL-ZIPINFO->FILENAME$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(VL::STRINGP-OF-VL-ZIPINFO->FILENAME)
(VL::VL-ZIPINFO->FILENAME$INLINE-OF-VL-ZIPINFO-FIX-X
 (9 3 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-FIX$INLINE))
 (3 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO->FILENAME$INLINE-VL-ZIPINFO-EQUIV-CONGRUENCE-ON-X)
(VL::VL-ZIPINFO->NAME$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(VL::STRINGP-OF-VL-ZIPINFO->NAME)
(VL::VL-ZIPINFO->NAME$INLINE-OF-VL-ZIPINFO-FIX-X
 (9 3 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-FIX$INLINE))
 (3 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO->NAME$INLINE-VL-ZIPINFO-EQUIV-CONGRUENCE-ON-X)
(VL::VL-ZIPINFO->SYNTAX$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(VL::STRINGP-OF-VL-ZIPINFO->SYNTAX)
(VL::VL-ZIPINFO->SYNTAX$INLINE-OF-VL-ZIPINFO-FIX-X
 (9 3 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-FIX$INLINE))
 (3 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO->SYNTAX$INLINE-VL-ZIPINFO-EQUIV-CONGRUENCE-ON-X)
(VL::VL-ZIPINFO->DATE$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(VL::STRINGP-OF-VL-ZIPINFO->DATE)
(VL::VL-ZIPINFO->DATE$INLINE-OF-VL-ZIPINFO-FIX-X
 (9 3 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-FIX$INLINE))
 (3 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO->DATE$INLINE-VL-ZIPINFO-EQUIV-CONGRUENCE-ON-X)
(VL::VL-ZIPINFO->LTIME$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(VL::NATP-OF-VL-ZIPINFO->LTIME)
(VL::VL-ZIPINFO->LTIME$INLINE-OF-VL-ZIPINFO-FIX-X
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (9 3 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-FIX$INLINE))
 (4 4 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(VL::VL-ZIPINFO->LTIME$INLINE-VL-ZIPINFO-EQUIV-CONGRUENCE-ON-X)
(VL::VL-ZIPINFO)
(VL::VL-ZIPINFO-P-OF-VL-ZIPINFO
 (25 25 (:REWRITE STR-FIX-WHEN-STRINGP))
 (17 11 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 )
(VL::VL-ZIPINFO->FILENAME-OF-VL-ZIPINFO
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO))
 )
(VL::VL-ZIPINFO->NAME-OF-VL-ZIPINFO
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO))
 )
(VL::VL-ZIPINFO->SYNTAX-OF-VL-ZIPINFO
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO))
 )
(VL::VL-ZIPINFO->DATE-OF-VL-ZIPINFO
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO))
 )
(VL::VL-ZIPINFO->LTIME-OF-VL-ZIPINFO
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO))
 )
(VL::VL-ZIPINFO-OF-FIELDS
 (3 1 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (2 2 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO
 (3 1 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (2 2 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::EQUAL-OF-VL-ZIPINFO
 (120 120 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(VL::VL-ZIPINFO-OF-STR-FIX-FILENAME
 (4 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO-STREQV-CONGRUENCE-ON-FILENAME)
(VL::VL-ZIPINFO-OF-STR-FIX-NAME
 (4 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO-STREQV-CONGRUENCE-ON-NAME)
(VL::VL-ZIPINFO-OF-STR-FIX-SYNTAX
 (4 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO-STREQV-CONGRUENCE-ON-SYNTAX)
(VL::VL-ZIPINFO-OF-STR-FIX-DATE
 (4 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO-STREQV-CONGRUENCE-ON-DATE)
(VL::VL-ZIPINFO-OF-NFIX-LTIME
 (8 8 (:REWRITE STR-FIX-WHEN-STRINGP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(VL::VL-ZIPINFO-NAT-EQUIV-CONGRUENCE-ON-LTIME)
(VL::VL-ZIPINFO-FIX-REDEF)
(VL::TAG-OF-VL-ZIPINFO)
(VL::VL-ZIPINFOLIST-P)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(VL::VL-ZIPINFOLIST-P-OF-CONS)
(VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P)
(VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP)
(VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P)
(VL::VL-ZIPINFOLIST-P-OF-APPEND)
(VL::VL-ZIPINFOLIST-P-OF-LIST-FIX)
(VL::VL-ZIPINFOLIST-P-OF-SFIX)
(VL::VL-ZIPINFOLIST-P-OF-INSERT)
(VL::VL-ZIPINFOLIST-P-OF-DELETE)
(VL::VL-ZIPINFOLIST-P-OF-MERGESORT)
(VL::VL-ZIPINFOLIST-P-OF-UNION)
(VL::VL-ZIPINFOLIST-P-OF-INTERSECT-1)
(VL::VL-ZIPINFOLIST-P-OF-INTERSECT-2)
(VL::VL-ZIPINFOLIST-P-OF-DIFFERENCE)
(VL::VL-ZIPINFOLIST-P-OF-DUPLICATED-MEMBERS)
(VL::VL-ZIPINFOLIST-P-OF-REV)
(VL::VL-ZIPINFOLIST-P-OF-RCONS)
(VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P)
(VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL)
(VL::VL-ZIPINFOLIST-P-SET-EQUIV-CONGRUENCE)
(VL::VL-ZIPINFOLIST-P-OF-SET-DIFFERENCE-EQUAL)
(VL::VL-ZIPINFOLIST-P-OF-INTERSECTION-EQUAL-1)
(VL::VL-ZIPINFOLIST-P-OF-INTERSECTION-EQUAL-2)
(VL::VL-ZIPINFOLIST-P-OF-UNION-EQUAL)
(VL::VL-ZIPINFOLIST-P-OF-TAKE)
(VL::VL-ZIPINFOLIST-P-OF-REPEAT)
(VL::VL-ZIPINFO-P-OF-NTH-WHEN-VL-ZIPINFOLIST-P)
(VL::VL-ZIPINFOLIST-P-OF-UPDATE-NTH)
(VL::VL-ZIPINFOLIST-P-OF-BUTLAST)
(VL::VL-ZIPINFOLIST-P-OF-NTHCDR)
(VL::VL-ZIPINFOLIST-P-OF-LAST)
(VL::VL-ZIPINFOLIST-P-OF-REMOVE)
(VL::VL-ZIPINFOLIST-P-OF-REVAPPEND)
(VL::VL-ZIPINFOLIST-FIX$INLINE)
(VL::VL-ZIPINFOLIST-P-OF-VL-ZIPINFOLIST-FIX
 (30 1 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (22 2 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (20 12 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (15 1 (:DEFINITION VL::VL-ZIPINFOLIST-P))
 (12 6 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (4 4 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (2 2 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 (2 1 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 )
(VL::VL-ZIPINFOLIST-FIX-WHEN-VL-ZIPINFOLIST-P
 (32 4 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (28 24 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (13 3 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (9 6 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (1 1 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 )
(VL::VL-ZIPINFOLIST-FIX$INLINE
 (40 5 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (29 4 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (24 20 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (13 10 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (10 10 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (1 1 (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (2 2 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 )
(VL::VL-ZIPINFOLIST-EQUIV$INLINE)
(VL::VL-ZIPINFOLIST-EQUIV-IS-AN-EQUIVALENCE)
(VL::VL-ZIPINFOLIST-EQUIV-IMPLIES-EQUAL-VL-ZIPINFOLIST-FIX-1)
(VL::VL-ZIPINFOLIST-FIX-UNDER-VL-ZIPINFOLIST-EQUIV)
(VL::EQUAL-OF-VL-ZIPINFOLIST-FIX-1-FORWARD-TO-VL-ZIPINFOLIST-EQUIV)
(VL::EQUAL-OF-VL-ZIPINFOLIST-FIX-2-FORWARD-TO-VL-ZIPINFOLIST-EQUIV)
(VL::VL-ZIPINFOLIST-EQUIV-OF-VL-ZIPINFOLIST-FIX-1-FORWARD)
(VL::VL-ZIPINFOLIST-EQUIV-OF-VL-ZIPINFOLIST-FIX-2-FORWARD)
(VL::CAR-OF-VL-ZIPINFOLIST-FIX-X-UNDER-VL-ZIPINFO-EQUIV
 (33 3 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (18 3 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (18 2 (:REWRITE VL::VL-ZIPINFOLIST-FIX-WHEN-VL-ZIPINFOLIST-P))
 (12 12 (:TYPE-PRESCRIPTION VL::VL-ZIPINFOLIST-P))
 (12 12 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (7 7 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (6 6 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 (6 6 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (6 1 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 )
(VL::CAR-VL-ZIPINFOLIST-EQUIV-CONGRUENCE-ON-X-UNDER-VL-ZIPINFO-EQUIV)
(VL::CDR-OF-VL-ZIPINFOLIST-FIX-X-UNDER-VL-ZIPINFOLIST-EQUIV
 (54 5 (:REWRITE VL::VL-ZIPINFOLIST-FIX-WHEN-VL-ZIPINFOLIST-P))
 (35 3 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (22 2 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (18 18 (:TYPE-PRESCRIPTION VL::VL-ZIPINFOLIST-P))
 (18 18 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (12 2 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (9 9 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 (4 4 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (4 4 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 )
(VL::CDR-VL-ZIPINFOLIST-EQUIV-CONGRUENCE-ON-X-UNDER-VL-ZIPINFOLIST-EQUIV)
(VL::CONS-OF-VL-ZIPINFO-FIX-X-UNDER-VL-ZIPINFOLIST-EQUIV
 (34 4 (:REWRITE VL::VL-ZIPINFOLIST-FIX-WHEN-VL-ZIPINFOLIST-P))
 (17 2 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CONS))
 (10 10 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (8 8 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (6 6 (:TYPE-PRESCRIPTION VL::VL-ZIPINFOLIST-P))
 (5 5 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 )
(VL::CONS-VL-ZIPINFO-EQUIV-CONGRUENCE-ON-X-UNDER-VL-ZIPINFOLIST-EQUIV)
(VL::CONS-OF-VL-ZIPINFOLIST-FIX-Y-UNDER-VL-ZIPINFOLIST-EQUIV
 (19 2 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CONS))
 (8 8 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (8 8 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (8 8 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (6 2 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (4 4 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 )
(VL::CONS-VL-ZIPINFOLIST-EQUIV-CONGRUENCE-ON-Y-UNDER-VL-ZIPINFOLIST-EQUIV)
(VL::CONSP-OF-VL-ZIPINFOLIST-FIX
 (18 2 (:REWRITE VL::VL-ZIPINFOLIST-FIX-WHEN-VL-ZIPINFOLIST-P))
 (11 1 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (8 8 (:TYPE-PRESCRIPTION VL::VL-ZIPINFOLIST-P))
 (8 8 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (6 1 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (4 4 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 (2 2 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (2 2 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 )
(VL::VL-ZIPINFOLIST-FIX-OF-CONS
 (21 3 (:REWRITE VL::VL-ZIPINFOLIST-FIX-WHEN-VL-ZIPINFOLIST-P))
 (9 1 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CONS))
 (6 6 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (6 2 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (4 4 (:TYPE-PRESCRIPTION VL::VL-ZIPINFOLIST-P))
 (4 4 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (4 4 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (3 3 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 )
(VL::LEN-OF-VL-ZIPINFOLIST-FIX
 (14 14 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (12 2 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (11 1 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (6 1 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (2 2 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (2 2 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (1 1 (:REWRITE FTY::EQUAL-OF-LEN))
 )
(VL::VL-ZIPINFOLIST-FIX-OF-APPEND
 (49 49 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (36 32 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (36 2 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-APPEND))
 (14 4 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (12 2 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (6 1 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (2 2 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 )
(VL::VL-ZIPINFOLIST-FIX-OF-REPEAT
 (16 4 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (16 2 (:REWRITE VL::VL-ZIPINFOLIST-FIX-WHEN-VL-ZIPINFOLIST-P))
 (12 2 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-REPEAT))
 (10 10 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (10 10 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (2 2 (:TYPE-PRESCRIPTION VL::VL-ZIPINFOLIST-P))
 (1 1 (:REWRITE-QUOTED-CONSTANT VL::VL-ZIPINFOLIST-FIX-UNDER-VL-ZIPINFOLIST-EQUIV))
 )
(VL::NTH-OF-VL-ZIPINFOLIST-FIX
 (396 33 (:REWRITE LEN-WHEN-ATOM))
 (205 15 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (198 4 (:REWRITE NTH-WITH-LARGE-INDEX))
 (169 169 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (118 23 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (103 4 (:REWRITE NTH-WHEN-TOO-LARGE-CHEAP))
 (102 102 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (102 4 (:REWRITE NTH-WHEN-ATOM))
 (102 4 (:REWRITE VL::NTH-OF-ATOM))
 (100 10 (:REWRITE VL::VL-ZIPINFO-P-OF-NTH-WHEN-VL-ZIPINFOLIST-P))
 (90 18 (:REWRITE VL::CONSP-OF-VL-ZIPINFOLIST-FIX))
 (78 6 (:REWRITE VL::NATP-WHEN-POSP))
 (77 11 (:REWRITE ZP-OPEN))
 (60 60 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (60 60 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (60 30 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (56 40 (:REWRITE DEFAULT-<-1))
 (51 40 (:REWRITE DEFAULT-<-2))
 (50 14 (:REWRITE VL::|(< c2 (+ c1 a))|))
 (43 4 (:REWRITE VL::NTH-WHEN-ZP))
 (43 4 (:REWRITE NTH-WHEN-ZP))
 (42 42 (:META CANCEL_PLUS-LESSP-CORRECT))
 (32 4 (:REWRITE POSP-RW))
 (30 30 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (30 30 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 2))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 1))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (30 30 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (30 30 (:REWRITE CONSP-BY-LEN))
 (30 5 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (27 27 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (20 20 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (20 20 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (20 20 (:LINEAR LEN-WHEN-PREFIXP))
 (20 17 (:REWRITE DEFAULT-CDR))
 (16 16 (:TYPE-PRESCRIPTION NATP))
 (15 12 (:REWRITE DEFAULT-+-2))
 (13 2 (:REWRITE VL::INTEGERP-WHEN-NATP))
 (12 12 (:REWRITE NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (12 12 (:REWRITE DEFAULT-+-1))
 (12 4 (:REWRITE NATP-POSP))
 (11 2 (:REWRITE NATP-RW))
 (10 10 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (10 10 (:LINEAR INDEX-OF-<-LEN))
 (10 10 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (8 8 (:TYPE-PRESCRIPTION POSP))
 (8 8 (:REWRITE VL::POSP-WHEN-MEMBER-EQUAL-OF-POS-LISTP))
 (8 4 (:REWRITE POSP-NATP))
 (8 2 (:REWRITE <-+-NEGATIVE-0-1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (6 1 (:REWRITE SET::DOUBLE-CONTAINMENT))
 (5 5 (:REWRITE CONSP-OF-CDDR-BY-LEN))
 (5 5 (:LINEAR LISTPOS-COMPLETE))
 (4 4 (:REWRITE VL::NATP-WHEN-MEMBER-EQUAL-OF-NAT-LISTP))
 (4 4 (:REWRITE INTEGERP-WHEN-MEMBER-EQUAL-OF-INTEGER-LISTP))
 (3 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:REWRITE NTH-WHEN-PREFIXP))
 (2 2 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (2 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (1 1 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (1 1 (:REWRITE SET::IN-SET))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(VL::VL-ZIPINFOLIST-EQUIV-IMPLIES-VL-ZIPINFOLIST-EQUIV-APPEND-1
 (205 17 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (128 128 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (120 17 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (117 22 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (79 79 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (34 34 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (34 34 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(VL::VL-ZIPINFOLIST-EQUIV-IMPLIES-VL-ZIPINFOLIST-EQUIV-APPEND-2
 (322 26 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (204 39 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (192 192 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (192 26 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (79 79 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (52 52 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (52 52 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (4 4 (:REWRITE VL::CONSP-OF-VL-ZIPINFOLIST-FIX))
 )
(VL::VL-ZIPINFOLIST-EQUIV-IMPLIES-VL-ZIPINFOLIST-EQUIV-NTHCDR-2
 (298 20 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (208 39 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (198 20 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (194 194 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (40 40 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (40 40 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 )
(VL::VL-ZIPINFOLIST-EQUIV-IMPLIES-VL-ZIPINFOLIST-EQUIV-TAKE-2
 (502 38 (:REWRITE VL::VL-ZIPINFOLIST-FIX-WHEN-VL-ZIPINFOLIST-P))
 (426 28 (:REWRITE VL::VL-ZIPINFO-FIX-WHEN-VL-ZIPINFO-P))
 (298 51 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-CDR-WHEN-VL-ZIPINFOLIST-P))
 (290 26 (:REWRITE VL::VL-ZIPINFO-P-OF-CAR-WHEN-VL-ZIPINFOLIST-P))
 (234 234 (:TYPE-PRESCRIPTION VL::VL-ZIPINFOLIST-P))
 (234 234 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (215 23 (:REWRITE VL::VL-ZIPINFOLIST-P-OF-TAKE))
 (135 117 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 (64 64 (:TYPE-PRESCRIPTION VL::VL-ZIPINFO-P))
 (64 64 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (15 15 (:TYPE-PRESCRIPTION NFIX))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE-QUOTED-CONSTANT VL::VL-ZIPINFOLIST-FIX-UNDER-VL-ZIPINFOLIST-EQUIV))
 (1 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(VL::VL-SCAN-FOR-ZIPINFOS-AUX-FN
 (1065 4 (:REWRITE VL::STRINGP-WHEN-TRUE-LISTP))
 (666 12 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (657 6 (:DEFINITION TRUE-LIST-LISTP))
 (321 13 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (130 13 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (109 13 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (90 13 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (90 12 (:REWRITE VL::TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (81 6 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (78 13 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (71 8 (:REWRITE VL::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (66 12 (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (52 52 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (52 52 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (42 6 (:REWRITE VL::CONSP-OF-CAR-WHEN-VL-COMMENTMAP-P))
 (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (36 9 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (31 8 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (30 30 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-SUBSETP-EQUAL))
 (27 3 (:REWRITE ALISTP-OF-CDR))
 (26 26 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (26 26 (:REWRITE VL::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (26 13 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (24 1 (:REWRITE MEMBER-WHEN-ATOM))
 (21 21 (:REWRITE DEFAULT-CDR))
 (18 18 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (18 18 (:TYPE-PRESCRIPTION ALISTP))
 (18 9 (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (18 3 (:REWRITE VL::TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (17 1 (:DEFINITION VL::VL-SCAN-FOR-ZIPINFOS-AUX-FN))
 (16 16 (:REWRITE VL::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (15 15 (:REWRITE VL::TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (15 15 (:REWRITE DEFAULT-CAR))
 (15 15 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (15 8 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (14 14 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (14 14 (:REWRITE VL::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (14 14 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (14 7 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (14 7 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LIST*P))
 (14 7 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LIST*P))
 (14 7 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LIST*P))
 (13 13 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (13 13 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (13 13 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (13 13 (:REWRITE SET::IN-SET))
 (12 12 (:REWRITE VL::VL-COMMENTMAP-P-WHEN-SUBSETP-EQUAL))
 (12 6 (:REWRITE VL::SYMBOL-LISTP-OF-CAR-WHEN-SYMBOL-LIST-LISTP))
 (12 6 (:REWRITE VL::STRING-LISTP-OF-CAR-WHEN-STRING-LIST-LISTP))
 (12 6 (:REWRITE CONSP-OF-CAR-WHEN-CONS-LISTP))
 (12 6 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (12 5 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (10 10 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (9 9 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 2))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 1))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (9 9 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (9 9 (:REWRITE CONSP-BY-LEN))
 (9 9 (:REWRITE ALISTP-WHEN-ATOM))
 (9 9 (:REWRITE VL::ALISTP-WHEN-ALL-HAVE-LEN))
 (8 8 (:REWRITE VL::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (8 8 (:REWRITE FN-CHECK-DEF-FORMALS))
 (7 7 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (7 7 (:REWRITE VL::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (7 7 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (7 7 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE VL::VL-COMMENTMAP-P-WHEN-NOT-CONSP))
 (6 3 (:REWRITE VL::VL-COMMENTMAP-P-OF-CDR-WHEN-VL-COMMENTMAP-P))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (5 5 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (3 3 (:REWRITE-QUOTED-CONSTANT VL::MAYBE-STRING-FIX-UNDER-MAYBE-STRING-EQUIV))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 (1 1 (:REWRITE SUBSETP-MEMBER . 4))
 (1 1 (:REWRITE SUBSETP-MEMBER . 3))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 3))
 (1 1 (:REWRITE INTERSECTP-MEMBER . 2))
 )
(VL::VL-ZIPINFOLIST-P-OF-VL-SCAN-FOR-ZIPINFOS-AUX.INFOS
 (145 7 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 (37 1 (:REWRITE SUBSETP-OF-CONS))
 (24 8 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (22 22 (:REWRITE DEFAULT-CAR))
 (22 22 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (20 20 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (20 20 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (20 10 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (19 3 (:REWRITE VL::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (18 18 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (14 2 (:REWRITE VL::VL-ZIPINFO-P-WHEN-MEMBER-EQUAL-OF-VL-ZIPINFOLIST-P))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 2))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 1))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (10 10 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (10 10 (:REWRITE CONSP-BY-LEN))
 (9 9 (:REWRITE-QUOTED-CONSTANT VL::MAYBE-STRING-FIX-UNDER-MAYBE-STRING-EQUIV))
 (8 8 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (8 8 (:REWRITE SUBSETP-TRANS2))
 (8 8 (:REWRITE SUBSETP-TRANS))
 (3 3 (:REWRITE SUBSETP-MEMBER . 2))
 (3 3 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(VL::STATE-P1-OF-VL-SCAN-FOR-ZIPINFOS-AUX.STATE
 (20 20 (:REWRITE DEFAULT-CAR))
 (20 20 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (7 7 (:REWRITE-QUOTED-CONSTANT VL::MAYBE-STRING-FIX-UNDER-MAYBE-STRING-EQUIV))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (6 3 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 2))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 1))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (3 3 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (3 3 (:REWRITE CONSP-BY-LEN))
 )
(VL::VL-SCAN-FOR-ZIPINFOS-FN)
(VL::VL-ZIPINFOLIST-P-OF-VL-SCAN-FOR-ZIPINFOS.INFOS
 (24 1 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE VL::VL-ZIPINFOLIST-P-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 1 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IFDEF-USE-MAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FUNCTION-SPECIALIZATION-MAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEFINES-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEF-USE-MAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (1 1 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (1 1 (:REWRITE CONSP-BY-LEN))
 )
(VL::STATE-P1-OF-VL-SCAN-FOR-ZIPINFOS.STATE
 (12 4 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (8 2 (:DEFINITION STATE-P))
 (4 4 (:TYPE-PRESCRIPTION STATE-P))
 )
