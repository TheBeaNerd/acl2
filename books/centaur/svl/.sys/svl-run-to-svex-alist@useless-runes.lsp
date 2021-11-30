(SVL::ASSOC-EQUAL-OPENER-WHEN-NOT-EQUAL)
(SVL::ASSOC-EQUAL-OPENER-WHEN-EQUAL)
(SVL::ALIST-TERM-TO-ENTRY-LIST
 (198 58 (:REWRITE DEFAULT-+-2))
 (176 1 (:REWRITE O<=-O-FINP-DEF))
 (116 2 (:LINEAR ACL2-COUNT-OF-SUM))
 (94 58 (:REWRITE DEFAULT-+-1))
 (56 6 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (38 6 (:DEFINITION INTEGER-LISTP))
 (36 6 (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (20 2 (:DEFINITION LENGTH))
 (18 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (18 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (18 6 (:DEFINITION RATIONAL-LISTP))
 (17 1 (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
 (16 8 (:DEFINITION APPLY$-BADGEP))
 (16 4 (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (16 4 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (16 4 (:DEFINITION INTEGER-ABS))
 (12 3 (:REWRITE O-P-O-INFP-CAR))
 (12 2 (:DEFINITION LEN))
 (9 5 (:REWRITE DEFAULT-<-2))
 (8 8 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (8 8 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (7 5 (:REWRITE DEFAULT-<-1))
 (7 1 (:REWRITE AC-<))
 (6 6 (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (6 6 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 2 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (3 3 (:REWRITE O-P-DEF-O-FINP-1))
 (3 3 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-3))
 (3 1 (:REWRITE O-INFP-O-FINP-O<=))
 (2 2 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (2 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (2 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (2 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (2 2 (:REWRITE DEFAULT-REALPART))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-IMAGPART))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE STR::CONSP-OF-EXPLODE))
 (2 2 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-2))
 (2 2 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-0))
 (1 1 (:REWRITE |a < b & b < c  =>  a < c|))
 (1 1 (:LINEAR MEMBER-EQUAL-ACL2-COUNT-SMALLER-1))
 )
(SVL::VALID-RW-STEP-LIMIT)
(SVL::RP-STATEP-OF-NOT-SIMPLIFIED-ACTION
 (686 3 (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
 (677 1 (:DEFINITION TRUE-LISTP))
 (541 2 (:DEFINITION RP::RP-TERM-LISTP))
 (513 4 (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
 (504 4 (:DEFINITION QUOTEP))
 (497 3 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (495 1 (:DEFINITION APPLY$-BADGEP))
 (305 4 (:DEFINITION SUBSETP-EQUAL))
 (224 30 (:DEFINITION MEMBER-EQUAL))
 (186 10 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (143 4 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (140 16 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (132 1 (:DEFINITION RP::RP-TERMP))
 (89 5 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (73 4 (:DEFINITION NAT-LISTP))
 (63 5 (:REWRITE NATP-WHEN-GTE-0))
 (60 60 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (52 52 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (49 1 (:DEFINITION RP::FALIST-CONSISTENT))
 (48 48 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (44 6 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (42 12 (:REWRITE O-P-O-INFP-CAR))
 (42 1 (:DEFINITION RP::FALIST-CONSISTENT-AUX))
 (39 39 (:TYPE-PRESCRIPTION RP::RP-TERMP))
 (32 32 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (30 30 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (28 28 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (27 7 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (26 4 (:DEFINITION INTEGER-LISTP))
 (24 24 (:TYPE-PRESCRIPTION NAT-LISTP))
 (24 3 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (23 23 (:REWRITE NTH-WHEN-PREFIXP))
 (19 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (18 18 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (17 17 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (17 17 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (16 16 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (16 2 (:REWRITE NATP-WHEN-INTEGERP))
 (15 15 (:DEFINITION NTH))
 (15 5 (:REWRITE RP::RP-TERMP-IS-IF-LEMMA))
 (14 1 (:DEFINITION SYMBOL-LISTP))
 (13 13 (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
 (12 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (12 5 (:REWRITE RP::IS-IF-RP-TERMP))
 (12 4 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (10 10 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (10 10 (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (10 10 (:REWRITE O-P-DEF-O-FINP-1))
 (9 9 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
 (9 9 (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
 (8 8 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (8 3 (:REWRITE RP::RP-TERMP-CADR))
 (7 7 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (7 3 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (6 6 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (6 6 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (6 3 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (6 3 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (6 3 (:REWRITE DEFAULT-+-2))
 (6 3 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
 (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (4 4 (:TYPE-PRESCRIPTION QUOTEP))
 (4 4 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (4 2 (:REWRITE RP::RP-TERMP-IMPLIES-SYMBOL-CAR-TERM))
 (4 2 (:REWRITE RP::RP-TERMP-CADDR))
 (4 2 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
 (4 2 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (4 2 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (4 1 (:REWRITE RP::VALID-RP-STATE-SYNTAXP-IMPLIES-RP-STATEP))
 (4 1 (:DEFINITION ALL-NILS))
 (3 3 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (3 3 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (3 3 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (3 3 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (3 3 (:REWRITE SET::IN-SET))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION RP::VALID-RP-STATE-SYNTAXP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (2 2 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (2 2 (:LINEAR LEN-WHEN-PREFIXP))
 (2 1 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 (1 1 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
 (1 1 (:LINEAR BOUNDS-POSITION-EQUAL))
 (1 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (1 1 (:DEFINITION UPDATE-NTH))
 )
(SVL::RW-SVL-RUN-TO-SVEX-ALIST-FN)
(SVL::TRUE-LISTP-OF-UNQUOTE-ALL
 (3776 17 (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
 (3046 12 (:DEFINITION RP::RP-TERM-LISTP))
 (2893 21 (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
 (2809 15 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (2799 5 (:DEFINITION APPLY$-BADGEP))
 (1813 20 (:DEFINITION SUBSETP-EQUAL))
 (1408 150 (:DEFINITION MEMBER-EQUAL))
 (1056 50 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (880 80 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (719 21 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (660 5 (:DEFINITION RP::RP-TERMP))
 (472 25 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (374 20 (:DEFINITION NAT-LISTP))
 (366 99 (:REWRITE O-P-O-INFP-CAR))
 (333 25 (:REWRITE NATP-WHEN-GTE-0))
 (300 300 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (260 260 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (245 5 (:DEFINITION RP::FALIST-CONSISTENT))
 (240 240 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (238 30 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (210 5 (:DEFINITION RP::FALIST-CONSISTENT-AUX))
 (201 201 (:TYPE-PRESCRIPTION RP::RP-TERMP))
 (178 178 (:TYPE-PRESCRIPTION O-P))
 (160 160 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (153 35 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (150 150 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (140 140 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (136 17 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (130 20 (:DEFINITION INTEGER-LISTP))
 (120 120 (:TYPE-PRESCRIPTION NAT-LISTP))
 (95 10 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (90 90 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (89 89 (:REWRITE O-P-DEF-O-FINP-1))
 (80 80 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (80 10 (:REWRITE NATP-WHEN-INTEGERP))
 (78 20 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (75 25 (:REWRITE RP::RP-TERMP-IS-IF-LEMMA))
 (71 71 (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
 (70 5 (:DEFINITION SYMBOL-LISTP))
 (65 65 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (60 30 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (60 25 (:REWRITE RP::IS-IF-RP-TERMP))
 (57 57 (:TYPE-PRESCRIPTION QUOTEP))
 (50 50 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (50 50 (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (46 46 (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
 (45 45 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
 (40 40 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (40 15 (:REWRITE RP::RP-TERMP-CADR))
 (35 35 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (35 35 (:TYPE-PRESCRIPTION LEN))
 (34 34 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (34 17 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (34 17 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (30 30 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (30 30 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (30 15 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (30 10 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (30 5 (:DEFINITION LEN))
 (25 25 (:TYPE-PRESCRIPTION ALL-NILS))
 (20 10 (:REWRITE RP::RP-TERMP-IMPLIES-SYMBOL-CAR-TERM))
 (20 10 (:REWRITE RP::RP-TERMP-CADDR))
 (20 10 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
 (20 10 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (20 10 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (20 5 (:DEFINITION ALL-NILS))
 (17 17 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (17 17 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (17 17 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (17 17 (:REWRITE SET::IN-SET))
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (10 10 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (10 10 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (10 10 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (10 10 (:REWRITE FN-CHECK-DEF-FORMALS))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (10 10 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (10 10 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (10 10 (:LINEAR LEN-WHEN-PREFIXP))
 (10 5 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (10 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 5 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
 (5 5 (:LINEAR BOUNDS-POSITION-EQUAL))
 (5 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
 )
(SVL::TRUE-LISTP-OF-ALIST-TERM-TO-ENTRY-LIST
 (2418 9 (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
 (2391 3 (:DEFINITION TRUE-LISTP))
 (1983 6 (:DEFINITION RP::RP-TERM-LISTP))
 (1899 12 (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
 (1872 12 (:DEFINITION QUOTEP))
 (1851 9 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (1845 3 (:DEFINITION APPLY$-BADGEP))
 (1235 12 (:DEFINITION SUBSETP-EQUAL))
 (992 90 (:DEFINITION MEMBER-EQUAL))
 (698 30 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (620 48 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (454 118 (:REWRITE O-P-O-INFP-CAR))
 (429 12 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (396 3 (:DEFINITION RP::RP-TERMP))
 (297 15 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (229 12 (:DEFINITION NAT-LISTP))
 (209 15 (:REWRITE NATP-WHEN-GTE-0))
 (180 180 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (156 156 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (152 18 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (147 3 (:DEFINITION RP::FALIST-CONSISTENT))
 (144 144 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (126 3 (:DEFINITION RP::FALIST-CONSISTENT-AUX))
 (112 112 (:REWRITE O-P-DEF-O-FINP-1))
 (101 21 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (96 96 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (90 90 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (84 84 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (78 12 (:DEFINITION INTEGER-LISTP))
 (72 9 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (57 6 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (56 12 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (48 48 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (48 6 (:REWRITE NATP-WHEN-INTEGERP))
 (45 15 (:REWRITE RP::RP-TERMP-IS-IF-LEMMA))
 (42 3 (:DEFINITION SYMBOL-LISTP))
 (39 39 (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
 (36 18 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (36 15 (:REWRITE RP::IS-IF-RP-TERMP))
 (30 30 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (30 30 (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (27 27 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX))
 (27 27 (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
 (24 24 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (24 9 (:REWRITE RP::RP-TERMP-CADR))
 (21 21 (:TYPE-PRESCRIPTION LEN))
 (18 18 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (18 18 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (18 18 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (18 9 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (18 9 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (18 9 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (18 6 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (18 3 (:DEFINITION LEN))
 (15 15 (:TYPE-PRESCRIPTION ALL-NILS))
 (15 15 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (12 12 (:TYPE-PRESCRIPTION QUOTEP))
 (12 6 (:REWRITE RP::RP-TERMP-IMPLIES-SYMBOL-CAR-TERM))
 (12 6 (:REWRITE RP::RP-TERMP-CADDR))
 (12 6 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
 (12 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (12 6 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (12 3 (:DEFINITION ALL-NILS))
 (9 9 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (9 9 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (9 9 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (9 9 (:REWRITE SET::IN-SET))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (6 6 (:REWRITE FN-CHECK-DEF-FORMALS))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (6 6 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (6 6 (:LINEAR LEN-WHEN-PREFIXP))
 (6 3 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 3 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
 (3 3 (:LINEAR BOUNDS-POSITION-EQUAL))
 (3 3 (:DEFINITION WEAK-APPLY$-BADGE-P))
 )
(SVL::UNSIGNED-BYTE-P-58-OF-RW-STEP-LIMIT
 (4 1 (:REWRITE RP::VALID-RP-STATE-SYNTAXP-IMPLIES-RP-STATEP))
 (2 2 (:TYPE-PRESCRIPTION RP::VALID-RP-STATE-SYNTAXP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 )
(SVL::RW-SVL-RUN-TO-SVEX-ALIST-FN
 (76401 6 (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
 (76383 2 (:DEFINITION TRUE-LISTP))
 (76027 77 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (76027 6 (:DEFINITION APPLY$-BADGEP))
 (67796 37 (:DEFINITION RP::RP-RW))
 (67522 8 (:DEFINITION SUBSETP-EQUAL))
 (67378 62 (:DEFINITION MEMBER-EQUAL))
 (61697 37 (:DEFINITION RP::RP-EX-COUNTERPART))
 (50505 259 (:REWRITE RP::RP-TERMP-RP-RW-RULE))
 (42100 32 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (29646 20 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (17871 259 (:REWRITE RP::VALID-RP-STATE-SYNTAXP-WHEN-RULES-ARE-RETRIEVED))
 (16058 259 (:DEFINITION RP::CONTEXT-SYNTAXP))
 (10586 146 (:REWRITE ZP-OPEN))
 (9156 109 (:DEFINITION RP::RP-RW-SUBTERMS))
 (7728 115 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (7717 7717 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (7717 7717 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (7717 7717 (:REWRITE NTH-WHEN-PREFIXP))
 (7717 7717 (:DEFINITION NTH))
 (6553 297 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (5371 78 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (4800 48 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (4516 115 (:REWRITE NATP-WHEN-GTE-0))
 (4306 1861 (:REWRITE RP::VALID-RP-STATE-SYNTAXP-IMPLIES-RP-STATEP))
 (3034 2101 (:REWRITE DEFAULT-+-2))
 (2882 76 (:DEFINITION NAT-LISTP))
 (2436 74 (:DEFINITION RP::RP-CHECK-CONTEXT))
 (2101 2101 (:REWRITE DEFAULT-+-1))
 (1955 74 (:DEFINITION RP::RP-EQUAL))
 (1861 1861 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 (1770 148 (:DEFINITION RP::EX-FROM-RP))
 (1616 419 (:REWRITE O-P-O-INFP-CAR))
 (1520 151 (:REWRITE RP::NOT-INCLUDE-RP))
 (1108 150 (:DEFINITION RP::INCLUDE-FNC))
 (933 933 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (931 931 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (894 148 (:DEFINITION INTEGER-LISTP))
 (849 37 (:REWRITE RP::RP-EQUAL-IS-SYMMETRIC))
 (842 404 (:REWRITE DEFAULT-<-2))
 (815 815 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-VALID-RP-STATE-SYNTAXP))
 (600 297 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (584 146 (:REWRITE ZP-WHEN-INTEGERP))
 (555 555 (:REWRITE CDR-CONS))
 (492 109 (:REWRITE NATP-WHEN-INTEGERP))
 (488 260 (:DEFINITION RP::UNQUOTE-ALL))
 (444 444 (:REWRITE CAR-CONS))
 (443 443 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (438 146 (:REWRITE ZP-WHEN-GT-0))
 (404 404 (:REWRITE DEFAULT-<-1))
 (399 399 (:REWRITE O-P-DEF-O-FINP-1))
 (386 386 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (376 39 (:REWRITE RP::IS-IF-RP-TERMP))
 (372 372 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
 (368 22 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (342 268 (:DEFINITION ASSOC-EQUAL))
 (338 23 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (315 21 (:REWRITE RP::RP-TERMP-CADR))
 (306 306 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (305 15 (:DEFINITION SYMBOL-LISTP))
 (292 146 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (259 259 (:TYPE-PRESCRIPTION RP::RULE-LIST-SYNTAXP))
 (259 259 (:TYPE-PRESCRIPTION LOGICP))
 (259 259 (:REWRITE WITNESS-EV-META-EXTRACT-FNCALL))
 (259 259 (:REWRITE RP::RP-EVL-META-EXTRACT-FNCALL))
 (259 259 (:REWRITE MX-EV-META-EXTRACT-FNCALL))
 (259 259 (:REWRITE MEXTRACT-FNCALL))
 (259 259 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (259 259 (:DEFINITION RP::MAGIC-EV-FNCALL-WRAPPER))
 (222 222 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
 (222 37 (:DEFINITION RP::QUOTE-LISTP))
 (152 152 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (146 146 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (146 146 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (141 141 (:TYPE-PRESCRIPTION RP::IS-HIDE))
 (130 130 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (126 4 (:REWRITE SYMBOL-LISTP-CDR-ASSOC-EQUAL))
 (119 41 (:REWRITE RP::RP-TERMP-IS-IF-LEMMA))
 (117 117 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (114 4 (:DEFINITION SYMBOL-LIST-LISTP))
 (108 108 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (106 106 (:TYPE-PRESCRIPTION NATP))
 (104 4 (:REWRITE MEMBER-EQUAL-STRIP-CARS-ASSOC-EQUAL))
 (96 96 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (84 84 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (78 17 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (76 76 (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
 (74 74 (:REWRITE RP::RP-EQUAL-REFLEXIVE))
 (64 64 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (62 62 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (56 56 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (52 4 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (50 34 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (48 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (42 2 (:DEFINITION ALISTP))
 (37 37 (:TYPE-PRESCRIPTION RP::QUOTE-LISTP))
 (37 37 (:TYPE-PRESCRIPTION RP::DISABLED-EXC-RULES-BOUNDP))
 (37 37 (:REWRITE RP::RP-EQUAL-SUBTERMS-REFLEXIVE))
 (34 34 (:REWRITE FN-CHECK-DEF-FORMALS))
 (26 26 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (22 22 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-LIST-LISTP))
 (20 20 (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (20 20 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (20 20 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (20 20 (:LINEAR LEN-WHEN-PREFIXP))
 (20 4 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (20 4 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (18 2 (:REWRITE RP::RP-TERMP-CADDDR))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 6 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (12 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (10 10 (:TYPE-PRESCRIPTION ALL-NILS))
 (10 10 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
 (10 10 (:LINEAR BOUNDS-POSITION-EQUAL))
 (8 8 (:TYPE-PRESCRIPTION STRIP-CARS))
 (8 8 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (8 8 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (8 4 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (8 4 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (8 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (8 4 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (8 2 (:DEFINITION ALL-NILS))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (6 6 (:REWRITE SET::IN-SET))
 (6 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (2 2 (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(SVL::SVL-RUN-TO-SVEX-ALIST-CREATE-ENV-AUX)
(SVL::GET-VARS-FROM-PORT-BINDS)
(SVL::SVL-RUN-TO-SVEX-ALIST-FN-CREATE-ENV)
(SVL::SVL-RUN-TO-SVEX-ALIST-CREATE-HYP)
(SVL::SVL-RUN->SVEX-ALIST-AUX-FN)
