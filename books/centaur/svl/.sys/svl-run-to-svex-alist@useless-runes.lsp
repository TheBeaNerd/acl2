(SVL::ASSOC-EQUAL-OPENER-WHEN-NOT-EQUAL
 (8 8 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 )
(SVL::ASSOC-EQUAL-OPENER-WHEN-EQUAL
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(SVL::ALIST-TERM-TO-ENTRY-LIST
 (134 40 (:REWRITE DEFAULT-+-2))
 (70 6 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (66 40 (:REWRITE DEFAULT-+-1))
 (50 44 (:REWRITE DEFAULT-CDR))
 (50 6 (:DEFINITION INTEGER-LISTP))
 (46 6 (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (38 38 (:REWRITE DEFAULT-CAR))
 (32 2 (:DEFINITION LENGTH))
 (26 6 (:DEFINITION RATIONAL-LISTP))
 (24 8 (:DEFINITION APPLY$-BADGEP))
 (24 2 (:DEFINITION LEN))
 (22 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (22 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (22 4 (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (22 4 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (16 8 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (16 4 (:DEFINITION INTEGER-ABS))
 (9 5 (:REWRITE DEFAULT-<-2))
 (8 8 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (8 4 (:REWRITE STR::CONSP-OF-EXPLODE))
 (7 5 (:REWRITE DEFAULT-<-1))
 (6 6 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (6 6 (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (6 6 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 (4 4 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (4 2 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (2 2 (:REWRITE INTEGERP==>NUMERATOR-=-X))
 (2 2 (:REWRITE INTEGERP==>DENOMINATOR-=-1))
 (2 2 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (2 2 (:REWRITE DEFAULT-REALPART))
 (2 2 (:REWRITE DEFAULT-NUMERATOR))
 (2 2 (:REWRITE DEFAULT-IMAGPART))
 (2 2 (:REWRITE DEFAULT-DENOMINATOR))
 )
(SVL::VALID-RW-STEP-LIMIT)
(SVL::RP-STATEP-OF-NOT-SIMPLIFIED-ACTION
 (637 3 (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
 (636 1 (:DEFINITION TRUE-LISTP))
 (506 7 (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
 (491 7 (:DEFINITION QUOTEP))
 (465 3 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (463 1 (:DEFINITION APPLY$-BADGEP))
 (211 1 (:DEFINITION SUBSETP-EQUAL))
 (196 14 (:DEFINITION MEMBER-EQUAL))
 (158 158 (:REWRITE DEFAULT-CDR))
 (128 7 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (127 7 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (119 3 (:REWRITE RP::BOOLEANP-OF-RW-CONTEXT-DISABLED))
 (105 1 (:DEFINITION RP::RP-TERMP))
 (100 5 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (83 4 (:DEFINITION NAT-LISTP))
 (80 40 (:DEFINITION NTH))
 (69 5 (:REWRITE NATP-WHEN-GTE-0))
 (55 55 (:REWRITE DEFAULT-CAR))
 (53 53 (:REWRITE NTH-WHEN-PREFIXP))
 (50 6 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (42 42 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (42 42 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (36 3 (:REWRITE RP::CC-ST-LISTP-IMPLIES-TRUE-LISTP))
 (33 33 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (32 4 (:DEFINITION INTEGER-LISTP))
 (31 31 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (31 7 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (27 3 (:DEFINITION RP::CC-ST-LISTP))
 (26 3 (:REWRITE RP::DUMMY-LEN-EQUIV))
 (24 24 (:TYPE-PRESCRIPTION NAT-LISTP))
 (24 3 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (21 21 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (21 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (18 18 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (18 9 (:REWRITE DEFAULT-+-2))
 (16 2 (:REWRITE NATP-WHEN-INTEGERP))
 (16 1 (:DEFINITION SYMBOL-LISTP))
 (15 15 (:TYPE-PRESCRIPTION RP::CC-ST-LISTP))
 (15 5 (:REWRITE RP::RP-TERMP-IS-IF-LEMMA))
 (14 14 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (14 14 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (14 14 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (14 4 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (12 12 (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
 (12 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (12 5 (:REWRITE RP::IS-IF-RP-TERMP))
 (10 10 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (9 9 (:TYPE-PRESCRIPTION RP::CC-ST-P))
 (9 9 (:REWRITE DEFAULT-+-1))
 (8 8 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (8 3 (:REWRITE RP::RP-TERMP-CADR))
 (8 2 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (7 7 (:TYPE-PRESCRIPTION QUOTEP))
 (7 7 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (7 7 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (6 6 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (6 6 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 3 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (6 3 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (6 1 (:DEFINITION ALL-NILS))
 (5 5 (:TYPE-PRESCRIPTION ALL-NILS))
 (5 5 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (5 2 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (5 1 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (4 4 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (4 4 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (4 2 (:REWRITE RP::RP-TERMP-IMPLIES-SYMBOL-CAR-TERM))
 (4 2 (:REWRITE RP::RP-TERMP-CADDR))
 (4 2 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
 (4 2 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (4 2 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (3 3 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (3 3 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (3 3 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (3 3 (:REWRITE SET::IN-SET))
 (3 3 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (3 1 (:DEFINITION UPDATE-NTH))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (2 2 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 1 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (2 1 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 )
(SVL::RW-SVL-RUN-TO-SVEX-ALIST-FN)
(SVL::TRUE-LISTP-OF-UNQUOTE-ALL
 (3849 17 (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
 (3244 12 (:DEFINITION RP::RP-TERM-LISTP))
 (3084 21 (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
 (2963 15 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (2953 5 (:DEFINITION APPLY$-BADGEP))
 (1577 5 (:DEFINITION SUBSETP-EQUAL))
 (1502 70 (:DEFINITION MEMBER-EQUAL))
 (983 35 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (789 789 (:REWRITE DEFAULT-CDR))
 (587 25 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (584 21 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (550 550 (:REWRITE DEFAULT-CAR))
 (525 5 (:DEFINITION RP::RP-TERMP))
 (444 20 (:DEFINITION NAT-LISTP))
 (403 25 (:REWRITE NATP-WHEN-GTE-0))
 (308 30 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (213 35 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (206 206 (:TYPE-PRESCRIPTION RP::RP-TERMP))
 (195 17 (:REWRITE RP::CC-ST-LISTP-IMPLIES-TRUE-LISTP))
 (171 171 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (160 20 (:DEFINITION INTEGER-LISTP))
 (155 155 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (145 17 (:DEFINITION RP::CC-ST-LISTP))
 (136 17 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (130 15 (:REWRITE RP::DUMMY-LEN-EQUIV))
 (128 20 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (120 120 (:TYPE-PRESCRIPTION NAT-LISTP))
 (105 105 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (105 10 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (90 90 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (81 81 (:TYPE-PRESCRIPTION RP::CC-ST-LISTP))
 (80 10 (:REWRITE NATP-WHEN-INTEGERP))
 (80 5 (:DEFINITION SYMBOL-LISTP))
 (75 25 (:REWRITE RP::RP-TERMP-IS-IF-LEMMA))
 (71 71 (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
 (70 70 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (70 70 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (70 70 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (60 60 (:TYPE-PRESCRIPTION LEN))
 (60 30 (:REWRITE DEFAULT-+-2))
 (60 30 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (60 25 (:REWRITE RP::IS-IF-RP-TERMP))
 (50 50 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (48 48 (:TYPE-PRESCRIPTION RP::CC-ST-P))
 (46 46 (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
 (46 46 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (43 43 (:TYPE-PRESCRIPTION QUOTEP))
 (40 40 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (40 15 (:REWRITE RP::RP-TERMP-CADR))
 (40 10 (:REWRITE FOLD-CONSTS-IN-+))
 (35 35 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (34 34 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (34 17 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (34 17 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (30 30 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (30 30 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (30 30 (:REWRITE DEFAULT-+-1))
 (30 5 (:DEFINITION ALL-NILS))
 (25 25 (:TYPE-PRESCRIPTION ALL-NILS))
 (25 10 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (25 5 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (25 5 (:DEFINITION LEN))
 (20 20 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (20 20 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (20 20 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (20 20 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (20 20 (:LINEAR LEN-WHEN-PREFIXP))
 (20 10 (:REWRITE RP::RP-TERMP-IMPLIES-SYMBOL-CAR-TERM))
 (20 10 (:REWRITE RP::RP-TERMP-CADDR))
 (20 10 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
 (20 10 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (20 10 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (17 17 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (17 17 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (17 17 (:REWRITE SET::IN-SET))
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (10 10 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT))
 (10 10 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (10 10 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (10 10 (:REWRITE FN-CHECK-DEF-FORMALS))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (10 10 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (10 5 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (10 5 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (5 5 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 )
(SVL::TRUE-LISTP-OF-ALIST-TERM-TO-ENTRY-LIST
 (3627 9 (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
 (3624 3 (:DEFINITION TRUE-LISTP))
 (3267 6 (:DEFINITION RP::RP-TERM-LISTP))
 (3180 12 (:REWRITE RP::RP-TERMP-IMPLIES-SUBTERMS))
 (3153 12 (:DEFINITION QUOTEP))
 (3111 9 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (3105 3 (:DEFINITION APPLY$-BADGEP))
 (2037 3 (:DEFINITION SUBSETP-EQUAL))
 (1992 42 (:DEFINITION MEMBER-EQUAL))
 (1557 1557 (:REWRITE DEFAULT-CDR))
 (1317 21 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (762 762 (:REWRITE DEFAULT-CAR))
 (534 15 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (363 15 (:REWRITE NATP-WHEN-GTE-0))
 (348 12 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (327 12 (:DEFINITION NAT-LISTP))
 (315 3 (:DEFINITION RP::RP-TERMP))
 (306 18 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (249 21 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (205 205 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (198 12 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (108 9 (:REWRITE RP::CC-ST-LISTP-IMPLIES-TRUE-LISTP))
 (96 12 (:DEFINITION INTEGER-LISTP))
 (93 93 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (81 9 (:DEFINITION RP::CC-ST-LISTP))
 (78 9 (:REWRITE RP::DUMMY-LEN-EQUIV))
 (72 9 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (63 63 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (63 6 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (48 6 (:REWRITE NATP-WHEN-INTEGERP))
 (48 3 (:DEFINITION SYMBOL-LISTP))
 (45 45 (:TYPE-PRESCRIPTION RP::CC-ST-LISTP))
 (45 15 (:REWRITE RP::RP-TERMP-IS-IF-LEMMA))
 (42 42 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (42 42 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (42 42 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (39 39 (:TYPE-PRESCRIPTION RP::RP-TERM-LISTP))
 (36 36 (:TYPE-PRESCRIPTION LEN))
 (36 18 (:REWRITE DEFAULT-+-2))
 (36 18 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (36 15 (:REWRITE RP::IS-IF-RP-TERMP))
 (30 30 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (27 27 (:TYPE-PRESCRIPTION RP::CC-ST-P))
 (27 27 (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
 (24 24 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (24 9 (:REWRITE RP::RP-TERMP-CADR))
 (24 6 (:REWRITE FOLD-CONSTS-IN-+))
 (18 18 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (18 18 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (18 18 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 9 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (18 9 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (18 3 (:DEFINITION ALL-NILS))
 (15 15 (:TYPE-PRESCRIPTION ALL-NILS))
 (15 6 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (15 3 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (15 3 (:DEFINITION LEN))
 (12 12 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION QUOTEP))
 (12 12 (:TYPE-PRESCRIPTION RP::IS-RP$INLINE))
 (12 12 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (12 12 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (12 12 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (12 12 (:LINEAR LEN-WHEN-PREFIXP))
 (12 6 (:REWRITE RP::RP-TERMP-IMPLIES-SYMBOL-CAR-TERM))
 (12 6 (:REWRITE RP::RP-TERMP-CADDR))
 (12 6 (:REWRITE RP::IS-RP-PSEUDO-TERMP))
 (12 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (12 6 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (9 9 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (9 9 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (9 9 (:REWRITE SET::IN-SET))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (6 6 (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (6 6 (:REWRITE FN-CHECK-DEF-FORMALS))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE RP::ATOM-RP-TERMP-IS-SYMBOLP))
 (6 3 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (6 3 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 )
(SVL::UNSIGNED-BYTE-P-58-OF-RW-STEP-LIMIT
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 )
(SVL::RW-SVL-RUN-TO-SVEX-ALIST-FN
 (37587 6 (:REWRITE RP::RP-TERM-LISTP-IS-TRUE-LISTP))
 (37585 2 (:DEFINITION TRUE-LISTP))
 (37251 6 (:DEFINITION APPLY$-BADGEP))
 (37247 49 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (30644 2 (:DEFINITION SUBSETP-EQUAL))
 (30614 28 (:DEFINITION MEMBER-EQUAL))
 (23782 23 (:DEFINITION RP::RP-RW))
 (20402 14 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (18438 90 (:REWRITE ZP-OPEN))
 (17348 23 (:DEFINITION RP::RP-EX-COUNTERPART))
 (14443 67 (:DEFINITION RP::RP-RW-SUBTERMS))
 (9334 250 (:REWRITE DEFAULT-<-2))
 (9084 90 (:REWRITE SVL::INTEGERP-IMPLIES-ACL2-NUMBERP))
 (6761 185 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (6722 73 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (5933 50 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (5302 2651 (:DEFINITION NTH))
 (5167 5167 (:REWRITE DEFAULT-CDR))
 (4650 34 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (3774 3774 (:REWRITE DEFAULT-CAR))
 (3673 358 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (3280 73 (:REWRITE NATP-WHEN-GTE-0))
 (2778 183 (:DEFINITION SYMBOL-LISTP))
 (2651 2651 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (2651 2651 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (2651 2651 (:REWRITE NTH-WHEN-PREFIXP))
 (2080 48 (:DEFINITION NAT-LISTP))
 (1932 1731 (:REWRITE DEFAULT-+-2))
 (1731 1731 (:REWRITE DEFAULT-+-1))
 (1496 162 (:DEFINITION RP::UNQUOTE-ALL))
 (1018 170 (:DEFINITION ASSOC-EQUAL))
 (830 830 (:META RP::BINARY-OR**/AND**-GUARD-META-CORRECT))
 (698 92 (:DEFINITION INTEGER-LISTP))
 (418 370 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (390 161 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (380 185 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (375 375 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-ALISTP))
 (362 362 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (360 90 (:REWRITE ZP-WHEN-INTEGERP))
 (355 59 (:REWRITE RP::IS-IF-RP-TERMP))
 (346 346 (:REWRITE FN-CHECK-DEF-FORMALS))
 (321 23 (:DEFINITION RP::IS-RP$$INLINE))
 (318 35 (:REWRITE RP::RP-TERMP-IMPLIES-CDR-LISTP))
 (311 26 (:REWRITE RP::NOT-INCLUDE-RP))
 (310 67 (:REWRITE NATP-WHEN-INTEGERP))
 (278 32 (:REWRITE RP::RP-TERMP-CADR))
 (275 275 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (270 90 (:REWRITE ZP-WHEN-GT-0))
 (250 250 (:REWRITE DEFAULT-<-1))
 (242 242 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (237 25 (:DEFINITION RP::INCLUDE-FNC))
 (205 205 (:TYPE-PRESCRIPTION RP::IS-IF$INLINE))
 (191 191 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (188 188 (:REWRITE RP::RP-STATE-PRESERVEDP-IMPLIES-RP-STATEP))
 (179 61 (:REWRITE RP::RP-TERMP-IS-IF-LEMMA))
 (169 169 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (161 161 (:TYPE-PRESCRIPTION LOGICP))
 (161 161 (:REWRITE WITNESS-EV-META-EXTRACT-FNCALL))
 (161 161 (:REWRITE RP::RP-EVL-META-EXTRACT-FNCALL))
 (161 161 (:REWRITE MX-EV-META-EXTRACT-FNCALL))
 (161 161 (:REWRITE MEXTRACT-FNCALL))
 (161 161 (:REWRITE ARITIES-OKP-IMPLIES-LOGICP))
 (161 161 (:DEFINITION RP::MAGIC-EV-FNCALL-WRAPPER))
 (161 23 (:DEFINITION RP::QUOTE-LISTP))
 (138 23 (:DEFINITION RP::RW-CONTEXT-DISABLED))
 (118 3 (:REWRITE RP::BOOLEANP-OF-RW-CONTEXT-DISABLED))
 (116 4 (:REWRITE SYMBOL-LISTP-CDR-ASSOC-EQUAL))
 (111 111 (:REWRITE RP::RP-TERMP-SHOULD-TERM-BE-IN-CONS-LHS))
 (104 4 (:DEFINITION SYMBOL-LIST-LISTP))
 (96 96 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (85 85 (:TYPE-PRESCRIPTION RP::IS-HIDE))
 (72 6 (:REWRITE RP::CC-ST-LISTP-IMPLIES-TRUE-LISTP))
 (71 71 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC))
 (65 25 (:REWRITE RP::RP-TERMP-SINGLE-STEP-3))
 (64 64 (:TYPE-PRESCRIPTION NATP))
 (62 62 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (57 25 (:REWRITE RP::RP-TERMP-CADDR))
 (56 56 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (54 6 (:DEFINITION RP::CC-ST-LISTP))
 (52 6 (:REWRITE RP::DUMMY-LEN-EQUIV))
 (48 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (46 46 (:TYPE-PRESCRIPTION RP::INCLUDE-FNC-SUBTERMS))
 (46 46 (:REWRITE AND*-NIL-FIRST))
 (42 42 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (30 30 (:TYPE-PRESCRIPTION RP::CC-ST-LISTP))
 (28 28 (:REWRITE SV::REWRITE-MEMBER-OF-APPEND-UNDER-SET-EQUIV))
 (28 28 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (26 26 (:TYPE-PRESCRIPTION RP::EX-FROM-SYNP))
 (23 23 (:TYPE-PRESCRIPTION RP::QUOTE-LISTP))
 (23 23 (:TYPE-PRESCRIPTION RP::DISABLED-EXC-RULES-BOUNDP))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-LIST-LISTP))
 (18 18 (:TYPE-PRESCRIPTION RP::CC-ST-P))
 (18 6 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (18 2 (:REWRITE RP::RP-TERMP-CADDDR))
 (16 4 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 6 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (12 2 (:DEFINITION ALL-NILS))
 (10 10 (:TYPE-PRESCRIPTION ALL-NILS))
 (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (8 8 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (8 8 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (8 8 (:LINEAR LEN-WHEN-PREFIXP))
 (8 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (8 4 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (6 6 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE SET::IN-SET))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (4 2 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (2 2 (:TYPE-PRESCRIPTION RP::IS-RP-LOOSE$INLINE))
 )
(SVL::SVL-RUN-TO-SVEX-ALIST-CREATE-ENV-AUX)
(SVL::GET-VARS-FROM-PORT-BINDS)
(SVL::SVL-RUN-TO-SVEX-ALIST-FN-CREATE-ENV)
(SVL::SVL-RUN-TO-SVEX-ALIST-CREATE-HYP)
(SVL::SVL-RUN->SVEX-ALIST-AUX-FN)
