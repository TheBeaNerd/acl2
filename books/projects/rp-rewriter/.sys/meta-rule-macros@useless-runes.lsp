(RP::RP-STATE-PRESERVEDP-OF-THE-SAME-RP-STATE
 (1 1 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (1 1 (:REWRITE RP::RP-STATE-PRESERVEDP-SK-NECC))
 )
(RP::FIX-ARGS/RETURNS-PACKAGE)
(RP::ADD-META-RULE-GUARD)
(RP::ADD-PROCESSOR-GUARD)
(RP::WEAK-META-RULE-TABLE-REC-P)
(RP::WEAK-PRE-POST-PROCESSOR-TABLE-REC-P)
(RP::ADD-META-RULE-FN
 (22645 181 (:DEFINITION MEMBER-EQUAL))
 (19364 64 (:DEFINITION SUBSETP-EQUAL))
 (9824 134 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (9571 174 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (7902 107 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (7367 107 (:REWRITE APPLY$-PRIMITIVE))
 (7255 4827 (:REWRITE DEFAULT-CAR))
 (7153 107 (:META APPLY$-PRIM-META-FN-CORRECT))
 (7119 4719 (:REWRITE DEFAULT-CDR))
 (6176 48 (:DEFINITION ALWAYS$))
 (5024 1256 (:REWRITE O-P-O-INFP-CAR))
 (3778 37 (:REWRITE PLAIN-UQI-INTEGER-LISTP))
 (2763 307 (:DEFINITION ASSOC-EQUAL))
 (2702 37 (:REWRITE PLAIN-UQI-SYMBOL-LISTP))
 (2512 20 (:DEFINITION APPLY$-BADGEP))
 (2076 346 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-SYMBOL-NAME))
 (1880 16 (:REWRITE INTEGER-LISTP-IMPLIES-ALWAYS$-INTEGERP))
 (1832 16 (:DEFINITION INTEGER-LISTP))
 (1728 36 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (1556 37 (:REWRITE PLAIN-UQI-TRUE-LIST-LISTP))
 (1384 1384 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (1286 37 (:REWRITE PLAIN-UQI-ACL2-NUMBER-LISTP))
 (1256 1256 (:REWRITE O-P-DEF-O-FINP-1))
 (1226 37 (:REWRITE PLAIN-UQI-RATIONAL-LISTP))
 (1220 37 (:REWRITE PLAIN-UQI-RATIONAL-LIST-LISTP))
 (1038 346 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (848 16 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (692 692 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (614 307 (:DEFINITION NTH))
 (434 434 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (428 214 (:REWRITE APPLY$-PRIMP-BADGE))
 (426 426 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (414 414 (:TYPE-PRESCRIPTION ALWAYS$))
 (352 352 (:REWRITE DEFAULT-SYMBOL-NAME))
 (346 346 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (346 346 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (344 16 (:REWRITE TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP))
 (321 321 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (307 307 (:REWRITE NTH-WHEN-PREFIXP))
 (300 30 (:DEFINITION TRUE-LISTP))
 (296 16 (:DEFINITION TRUE-LIST-LISTP))
 (274 30 (:DEFINITION RATIONAL-LISTP))
 (252 24 (:DEFINITION NATP))
 (230 230 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (200 16 (:REWRITE SYMBOL-LISTP-IMPLIES-ALWAYS$-SYMBOLP))
 (200 16 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ALWAYS$-ACL2-NUMBERP))
 (182 182 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (174 174 (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (168 16 (:REWRITE RATIONAL-LISTP-IMPLIES-ALWAYS$-RATIONALP))
 (152 16 (:DEFINITION ACL2-NUMBER-LISTP))
 (124 124 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (107 107 (:REWRITE APPLY$-CONSP-ARITY-1))
 (107 107 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (84 42 (:REWRITE DEFAULT-+-2))
 (80 20 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (74 74 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (72 36 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (72 12 (:DEFINITION ALL-NILS))
 (60 60 (:TYPE-PRESCRIPTION ALL-NILS))
 (60 60 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (60 30 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (50 50 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (48 48 (:LINEAR LEN-WHEN-PREFIXP))
 (48 24 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (48 16 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (42 42 (:REWRITE DEFAULT-+-1))
 (40 40 (:REWRITE FN-CHECK-DEF-FORMALS))
 (37 37 (:REWRITE PLAIN-UQI-ALWAYS$))
 (32 32 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (30 30 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (28 26 (:REWRITE DEFAULT-<-2))
 (26 26 (:REWRITE DEFAULT-<-1))
 (24 24 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
 (24 24 (:LINEAR BOUNDS-POSITION-EQUAL))
 (24 12 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 )
(RP::ADD-PROCESSOR-FN)
(RP::CREATE-RP-RW-META-RULE-FN-AUX1)
(RP::CREATE-RP-RW-META-RULE-FN-AUX2)
(RP::IS-PROC-ENABLED)
(RP::CREATE-RP-RW-PROCESSOR-FN-AUX2)
(RP::CREATE-RP-RW-META-RULE-FN-AUX3)
(RP::CREATE-RP-RW-META-RULE-FN
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(RP::ATTACH-META-FNCS-FN)
(RP::IS-RP-CLAUSE-PROCESSOR-UP-TO-DATE
 (11172 12 (:DEFINITION SUBSETP-EQUAL))
 (7512 72 (:DEFINITION ALWAYS$))
 (6552 24 (:DEFINITION MEMBER-EQUAL))
 (5223 12 (:REWRITE PLAIN-UQI-INTEGER-LISTP))
 (4872 72 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (4512 72 (:REWRITE APPLY$-PRIMITIVE))
 (4368 72 (:META APPLY$-PRIM-META-FN-CORRECT))
 (4218 45 (:DEFINITION APPLY$-BADGEP))
 (3012 24 (:REWRITE INTEGER-LISTP-IMPLIES-ALWAYS$-INTEGERP))
 (2940 24 (:DEFINITION INTEGER-LISTP))
 (2721 1833 (:REWRITE DEFAULT-CDR))
 (2460 87 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (2139 93 (:DEFINITION FGETPROP))
 (2004 54 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (1650 1278 (:REWRITE DEFAULT-CAR))
 (1524 381 (:REWRITE O-P-O-INFP-CAR))
 (1353 12 (:REWRITE PLAIN-UQI-TRUE-LIST-LISTP))
 (1185 162 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (957 12 (:REWRITE PLAIN-UQI-ACL2-NUMBER-LISTP))
 (933 12 (:REWRITE PLAIN-UQI-SYMBOL-LISTP))
 (885 12 (:REWRITE PLAIN-UQI-RATIONAL-LISTP))
 (801 66 (:DEFINITION NATP))
 (783 12 (:REWRITE PLAIN-UQI-RATIONAL-LIST-LISTP))
 (762 762 (:TYPE-PRESCRIPTION O-P))
 (750 69 (:DEFINITION TRUE-LISTP))
 (690 24 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (558 24 (:REWRITE TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP))
 (486 24 (:DEFINITION TRUE-LIST-LISTP))
 (471 471 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (450 24 (:DEFINITION LOOP$-AS))
 (381 381 (:REWRITE O-P-DEF-O-FINP-1))
 (360 360 (:TYPE-PRESCRIPTION ALWAYS$))
 (306 36 (:DEFINITION RATIONAL-LISTP))
 (294 24 (:REWRITE SYMBOL-LISTP-IMPLIES-ALWAYS$-SYMBOLP))
 (294 24 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ALWAYS$-ACL2-NUMBERP))
 (288 144 (:REWRITE APPLY$-PRIMP-BADGE))
 (276 276 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (264 132 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (246 24 (:REWRITE RATIONAL-LISTP-IMPLIES-ALWAYS$-RATIONALP))
 (237 45 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (231 231 (:TYPE-PRESCRIPTION LEN))
 (231 33 (:DEFINITION LEN))
 (222 24 (:DEFINITION ACL2-NUMBER-LISTP))
 (216 216 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (210 51 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (198 99 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (198 33 (:DEFINITION ALL-NILS))
 (198 24 (:DEFINITION SYMBOL-LISTP))
 (180 180 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (165 165 (:TYPE-PRESCRIPTION ALL-NILS))
 (162 162 (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (144 24 (:DEFINITION CDR-LOOP$-AS-TUPLE))
 (144 24 (:DEFINITION CAR-LOOP$-AS-TUPLE))
 (138 138 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (132 132 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (132 132 (:LINEAR LEN-WHEN-PREFIXP))
 (132 24 (:DEFINITION EMPTY-LOOP$-AS-TUPLEP))
 (120 120 (:TYPE-PRESCRIPTION TRUE-LIST-LISTP))
 (120 120 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (120 120 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (120 120 (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (93 93 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (84 84 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (72 72 (:REWRITE CDR-CONS))
 (72 72 (:REWRITE CAR-CONS))
 (72 72 (:REWRITE APPLY$-CONSP-ARITY-1))
 (72 72 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (72 36 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (66 66 (:REWRITE DEFAULT-<-2))
 (66 66 (:REWRITE DEFAULT-<-1))
 (66 66 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
 (66 66 (:LINEAR BOUNDS-POSITION-EQUAL))
 (66 33 (:REWRITE DEFAULT-+-2))
 (60 60 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (48 48 (:TYPE-PRESCRIPTION LOOP$-AS))
 (48 48 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (48 48 (:REWRITE FN-CHECK-DEF-FORMALS))
 (36 36 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (36 36 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (36 36 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (33 33 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (33 33 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE PLAIN-UQI-ALWAYS$))
 )
(RP::CHECK-IF-CLAUSE-PROCESSOR-UP-TO-DATE)
(RP::APPLY$-WARRANT-META-RUNE-FNC$INLINE)
(RP::APPLY$-WARRANT-META-RUNE-FNC$INLINE-DEFINITION)
(RP::APPLY$-WARRANT-META-RUNE-FNC$INLINE-NECC)
(RP::APPLY$-META-RUNE-FNC$INLINE
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(RP::DISABLE-META-RULES-FNC)
(RP::ENABLE-META-RULES-FNC)
(RP::IFF-OF-RP-EVLT-LST
 (52 51 (:REWRITE DEFAULT-CDR))
 (52 2 (:DEFINITION RP::RP-TRANS))
 (31 30 (:REWRITE DEFAULT-CAR))
 (16 2 (:DEFINITION RP::IS-FALIST))
 (14 2 (:DEFINITION RP::TRANS-LIST))
 (6 2 (:DEFINITION QUOTEP))
 (4 2 (:REWRITE RP::RP-EVL-OF-VARIABLE))
 (2 2 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (2 2 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-RP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-QUOTE))
 (2 2 (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-LAMBDA))
 (2 2 (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-IF-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
 (2 2 (:REWRITE RP::RP-EVL-OF-<-CALL))
 (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 )
(RP::RP-EVL-OF-EX-FROM-RP-REVERSE-FOR-ATOM
 (193 193 (:REWRITE DEFAULT-CDR))
 (156 111 (:REWRITE O-P-O-INFP-CAR))
 (117 117 (:REWRITE DEFAULT-CAR))
 (53 34 (:REWRITE RP::RP-EVL-OF-VARIABLE))
 (44 36 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-<-CALL))
 (37 35 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
 (37 35 (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
 (37 35 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
 (37 35 (:REWRITE RP::RP-EVL-OF-LAMBDA))
 (37 35 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
 (37 35 (:REWRITE RP::RP-EVL-OF-IF-CALL))
 (37 35 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
 (37 35 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
 (37 35 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
 (37 35 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
 (21 21 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (15 15 (:REWRITE O-P-DEF-O-FINP-1))
 (14 14 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 )
(RP::RP-EVLT-OF-EX-FROM-RP-REVERSE-FOR-ATOM
 (558 558 (:REWRITE DEFAULT-CDR))
 (382 382 (:REWRITE DEFAULT-CAR))
 (224 32 (:DEFINITION RP::TRANS-LIST))
 (64 64 (:TYPE-PRESCRIPTION RP::RP-TRANS-LST))
 (60 15 (:REWRITE O-P-O-INFP-CAR))
 (53 34 (:REWRITE RP::RP-EVL-OF-VARIABLE))
 (46 46 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (38 36 (:REWRITE RP::RP-EVL-OF-ZP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-UNARY-/-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-UNARY---CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-TYPESPEC-CHECK-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-SYMBOLP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-SYMBOL-NAME-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-STRINGP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CNT-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-RP-EQUAL-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-REALPART-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-RATIONALP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-NUMERATOR-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-NATP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-INTEGERP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-IMAGPART-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-IFF-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-FORCE-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-FORCE$-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-DENOMINATOR-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CONSP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-COMPLEX-RATIONALP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-COERCE-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CODE-CHAR-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CHARACTERP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CHAR-CODE-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CDR-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-CAR-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-BITP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-BINARY-+-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-BINARY-*-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-BAD-ATOM<=-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-ACL2-NUMBERP-CALL))
 (38 36 (:REWRITE RP::RP-EVL-OF-<-CALL))
 (35 35 (:REWRITE RP::RP-EVL-OF-SYNP-CALL))
 (35 35 (:REWRITE RP::RP-EVL-OF-RETURN-LAST-CALL))
 (35 35 (:REWRITE RP::RP-EVL-OF-NOT-CALL))
 (35 35 (:REWRITE RP::RP-EVL-OF-LAMBDA))
 (35 35 (:REWRITE RP::RP-EVL-OF-IMPLIES-CALL))
 (35 35 (:REWRITE RP::RP-EVL-OF-IF-CALL))
 (35 35 (:REWRITE RP::RP-EVL-OF-HIDE-CALL))
 (35 35 (:REWRITE RP::RP-EVL-OF-FALIST-CALL))
 (35 35 (:REWRITE RP::RP-EVL-OF-EQUAL-CALL))
 (35 35 (:REWRITE RP::RP-EVL-OF-CONS-CALL))
 (21 21 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (15 15 (:REWRITE O-P-DEF-O-FINP-1))
 (1 1 (:REWRITE RP::RP-EVL-META-EXTRACT-FN-CHECK-DEF))
 )
(RP::CREATE-REGULAR-EVAL-LEMMA-FN)
