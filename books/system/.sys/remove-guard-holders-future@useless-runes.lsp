(SUMLIST)
(TERM-MEASURE
 (44112 2 (:DEFINITION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP1))
 (43896 2 (:DEFINITION TYPE-EXPRESSIONS-FROM-TYPE-SPEC))
 (43386 2 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD-GEN))
 (42464 50 (:DEFINITION CONJOIN?))
 (42414 398 (:DEFINITION CONJOIN))
 (41796 4 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD1-GEN))
 (23911 23859 (:REWRITE DEFAULT-CDR))
 (18904 18860 (:REWRITE DEFAULT-CAR))
 (6150 6 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD/INTEGER-GEN))
 (1119 599 (:REWRITE DEFAULT-+-2))
 (740 599 (:REWRITE DEFAULT-+-1))
 (548 116 (:DEFINITION CONJOIN2))
 (502 2 (:DEFINITION SUBST-EACH-FOR-VAR))
 (496 2 (:DEFINITION SUBST-VAR))
 (488 2 (:DEFINITION CONS-TERM))
 (470 2 (:DEFINITION CONS-TERM1))
 (380 52 (:DEFINITION LENGTH))
 (290 290 (:TYPE-PRESCRIPTION SUBST-VAR-LST))
 (272 68 (:DEFINITION INTEGER-ABS))
 (220 4 (:DEFINITION FLATTEN-ANDS-IN-LIT))
 (147 7 (:DEFINITION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTSP-WITHIN))
 (145 19 (:DEFINITION SUBSETP-EQUAL))
 (128 64 (:DEFINITION KWOTE?))
 (126 126 (:DEFINITION KWOTE))
 (126 2 (:DEFINITION FLATTEN-ANDS-IN-LIT-LST))
 (114 99 (:REWRITE DEFAULT-<-2))
 (114 46 (:DEFINITION WEAK-SATISFIES-TYPE-SPEC-P))
 (109 99 (:REWRITE DEFAULT-<-1))
 (104 4 (:DEFINITION DISJOIN?))
 (100 6 (:DEFINITION OR-MACRO))
 (90 36 (:DEFINITION MEMBER-EQUAL))
 (77 19 (:DEFINITION BINARY-APPEND))
 (72 18 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (72 9 (:DEFINITION NAT-LISTP))
 (72 4 (:DEFINITION DUMB-NEGATE-LIT))
 (70 70 (:REWRITE DEFAULT-UNARY-MINUS))
 (48 12 (:DEFINITION MV-NTH))
 (48 10 (:DEFINITION REVAPPEND))
 (45 15 (:DEFINITION SYMBOL-LISTP))
 (45 9 (:DEFINITION SYMBOL-ALISTP))
 (45 9 (:DEFINITION ALL-VARS1))
 (40 4 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (38 38 (:REWRITE DEFAULT-COERCE-2))
 (38 38 (:DEFINITION <=?))
 (36 36 (:REWRITE DEFAULT-REALPART))
 (36 36 (:REWRITE DEFAULT-NUMERATOR))
 (36 36 (:REWRITE DEFAULT-IMAGPART))
 (36 36 (:REWRITE DEFAULT-DENOMINATOR))
 (36 36 (:REWRITE DEFAULT-COERCE-1))
 (36 9 (:DEFINITION STRIP-CDRS))
 (32 32 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (28 28 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP1))
 (27 9 (:DEFINITION NATP))
 (25 25 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (24 24 (:TYPE-PRESCRIPTION FLATTEN-ANDS-IN-LIT))
 (22 11 (:DEFINITION ADD-TO-SET-EQUAL))
 (20 20 (:TYPE-PRESCRIPTION SUBST-EACH-FOR-VAR))
 (18 18 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (14 14 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTSP-WITHIN-LST))
 (14 2 (:DEFINITION QUOTE-LISTP))
 (14 2 (:DEFINITION INTERSECTP-EQUAL))
 (12 2 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (10 2 (:DEFINITION CHARACTER-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (8 8 (:DEFINITION >?))
 (8 2 (:REWRITE DEFAULT-COERCE-3))
 (6 2 (:DEFINITION EQLABLE-LISTP))
 (6 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (4 4 (:TYPE-PRESCRIPTION TRANSLATE-DECLARATION-TO-GUARD-GEN-LST))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (4 4 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION FLATTEN-ANDS-IN-LIT-LST))
 (4 4 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (4 2 (:REWRITE DEFAULT-PKG-IMPORTS))
 (4 2 (:DEFINITION QUOTEP))
 (2 2 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (2 2 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (2 2 (:REWRITE DEFAULT-UNARY-/))
 (2 2 (:REWRITE DEFAULT-SYMBOL-NAME))
 (2 2 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (2 2 (:REWRITE DEFAULT-COMPLEX-2))
 (2 2 (:REWRITE DEFAULT-COMPLEX-1))
 (2 2 (:REWRITE DEFAULT-CODE-CHAR))
 (2 2 (:REWRITE DEFAULT-CHAR-CODE))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 )
(NAT-LISTP-MAKE-LIST-AC
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 (11 10 (:REWRITE DEFAULT-CDR))
 (11 10 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(NATP-SUMLIST
 (18 18 (:REWRITE DEFAULT-CAR))
 (13 11 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE DEFAULT-<-2))
 (11 6 (:REWRITE DEFAULT-+-2))
 (11 6 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(TERM-MEASURE-TYPE
 (176448 8 (:DEFINITION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP1))
 (175584 8 (:DEFINITION TYPE-EXPRESSIONS-FROM-TYPE-SPEC))
 (173544 8 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD-GEN))
 (169856 200 (:DEFINITION CONJOIN?))
 (169656 1592 (:DEFINITION CONJOIN))
 (167184 16 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD1-GEN))
 (93929 93701 (:REWRITE DEFAULT-CDR))
 (74380 74184 (:REWRITE DEFAULT-CAR))
 (24600 24 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD/INTEGER-GEN))
 (2192 464 (:DEFINITION CONJOIN2))
 (2008 8 (:DEFINITION SUBST-EACH-FOR-VAR))
 (1984 8 (:DEFINITION SUBST-VAR))
 (1952 8 (:DEFINITION CONS-TERM))
 (1880 8 (:DEFINITION CONS-TERM1))
 (1304 682 (:REWRITE DEFAULT-+-2))
 (1160 1160 (:TYPE-PRESCRIPTION SUBST-VAR-LST))
 (880 16 (:DEFINITION FLATTEN-ANDS-IN-LIT))
 (852 682 (:REWRITE DEFAULT-+-1))
 (512 256 (:DEFINITION KWOTE?))
 (504 504 (:DEFINITION KWOTE))
 (504 8 (:DEFINITION FLATTEN-ANDS-IN-LIT-LST))
 (496 64 (:DEFINITION SUBSETP-EQUAL))
 (456 184 (:DEFINITION WEAK-SATISFIES-TYPE-SPEC-P))
 (432 72 (:DEFINITION LENGTH))
 (416 16 (:DEFINITION DISJOIN?))
 (400 24 (:DEFINITION OR-MACRO))
 (363 111 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (312 120 (:DEFINITION MEMBER-EQUAL))
 (288 16 (:DEFINITION DUMB-NEGATE-LIT))
 (240 22 (:DEFINITION SUMLIST))
 (224 48 (:DEFINITION BINARY-APPEND))
 (202 49 (:DEFINITION STRIP-CDRS))
 (192 40 (:DEFINITION REVAPPEND))
 (169 138 (:REWRITE DEFAULT-<-1))
 (160 16 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (152 152 (:DEFINITION <=?))
 (148 138 (:REWRITE DEFAULT-<-2))
 (140 10 (:DEFINITION MAKE-LIST-AC))
 (120 24 (:DEFINITION ALL-VARS1))
 (102 102 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (96 96 (:TYPE-PRESCRIPTION FLATTEN-ANDS-IN-LIT))
 (88 88 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (84 4 (:DEFINITION LAMBDA-OBJECT-BODY))
 (80 80 (:TYPE-PRESCRIPTION SUBST-EACH-FOR-VAR))
 (80 10 (:REWRITE ZP-OPEN))
 (73 73 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (73 7 (:DEFINITION PAIRLIS$))
 (64 32 (:DEFINITION ADD-TO-SET-EQUAL))
 (56 8 (:DEFINITION QUOTE-LISTP))
 (56 8 (:DEFINITION INTERSECTP-EQUAL))
 (48 8 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (40 8 (:DEFINITION CHARACTER-LISTP))
 (32 32 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (32 32 (:DEFINITION >?))
 (32 8 (:REWRITE DEFAULT-COERCE-3))
 (24 8 (:DEFINITION EQLABLE-LISTP))
 (16 16 (:TYPE-PRESCRIPTION TRANSLATE-DECLARATION-TO-GUARD-GEN-LST))
 (16 16 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (16 16 (:TYPE-PRESCRIPTION FLATTEN-ANDS-IN-LIT-LST))
 (16 16 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 8 (:REWRITE DEFAULT-PKG-IMPORTS))
 (16 8 (:DEFINITION QUOTEP))
 (8 8 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (8 8 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION PAIRLIS$))
 (8 8 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:REWRITE DEFAULT-UNARY-/))
 (8 8 (:REWRITE DEFAULT-SYMBOL-NAME))
 (8 8 (:REWRITE DEFAULT-REALPART))
 (8 8 (:REWRITE DEFAULT-NUMERATOR))
 (8 8 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (8 8 (:REWRITE DEFAULT-IMAGPART))
 (8 8 (:REWRITE DEFAULT-DENOMINATOR))
 (8 8 (:REWRITE DEFAULT-COMPLEX-2))
 (8 8 (:REWRITE DEFAULT-COMPLEX-1))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 (8 8 (:REWRITE DEFAULT-CODE-CHAR))
 (8 8 (:REWRITE DEFAULT-CHAR-CODE))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 )
(NATP-TERM-MEASURE-NIL
 (22502 1 (:DEFINITION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 (22056 1 (:DEFINITION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP1))
 (21948 1 (:DEFINITION TYPE-EXPRESSIONS-FROM-TYPE-SPEC))
 (21693 1 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD-GEN))
 (21232 25 (:DEFINITION CONJOIN?))
 (21207 199 (:DEFINITION CONJOIN))
 (20898 2 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD1-GEN))
 (11736 11707 (:REWRITE DEFAULT-CDR))
 (9281 9256 (:REWRITE DEFAULT-CAR))
 (3075 3 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD/INTEGER-GEN))
 (415 415 (:REWRITE CAR-CONS))
 (274 58 (:DEFINITION CONJOIN2))
 (258 258 (:REWRITE CDR-CONS))
 (255 5 (:DEFINITION PSEUDO-TERMP))
 (251 1 (:DEFINITION SUBST-EACH-FOR-VAR))
 (248 1 (:DEFINITION SUBST-VAR))
 (244 1 (:DEFINITION CONS-TERM))
 (235 1 (:DEFINITION CONS-TERM1))
 (191 87 (:REWRITE DEFAULT-+-2))
 (145 145 (:TYPE-PRESCRIPTION SUBST-VAR-LST))
 (140 28 (:DEFINITION LEN))
 (121 87 (:REWRITE DEFAULT-+-1))
 (110 2 (:DEFINITION FLATTEN-ANDS-IN-LIT))
 (92 92 (:TYPE-PRESCRIPTION LEN))
 (64 32 (:DEFINITION KWOTE?))
 (63 63 (:DEFINITION KWOTE))
 (63 1 (:DEFINITION FLATTEN-ANDS-IN-LIT-LST))
 (62 8 (:DEFINITION SUBSETP-EQUAL))
 (57 23 (:DEFINITION WEAK-SATISFIES-TYPE-SPEC-P))
 (54 9 (:DEFINITION LENGTH))
 (52 2 (:DEFINITION DISJOIN?))
 (50 18 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (50 3 (:DEFINITION OR-MACRO))
 (49 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (44 4 (:DEFINITION SUMLIST))
 (39 15 (:DEFINITION MEMBER-EQUAL))
 (38 19 (:DEFINITION TRUE-LISTP))
 (36 2 (:DEFINITION DUMB-NEGATE-LIT))
 (28 6 (:DEFINITION BINARY-APPEND))
 (27 3 (:REWRITE COMMUTATIVITY-OF-+))
 (27 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (24 6 (:DEFINITION MV-NTH))
 (24 5 (:DEFINITION REVAPPEND))
 (21 1 (:DEFINITION LAMBDA-OBJECT-BODY))
 (20 2 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (19 19 (:DEFINITION <=?))
 (18 18 (:TYPE-PRESCRIPTION SUMLIST))
 (18 3 (:DEFINITION ALL-VARS))
 (15 5 (:DEFINITION SYMBOL-LISTP))
 (15 3 (:DEFINITION ALL-VARS1))
 (14 14 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP1))
 (14 12 (:REWRITE DEFAULT-<-1))
 (13 2 (:DEFINITION MAX))
 (12 12 (:TYPE-PRESCRIPTION FLATTEN-ANDS-IN-LIT))
 (12 12 (:REWRITE DEFAULT-<-2))
 (12 3 (:DEFINITION STRIP-CDRS))
 (11 11 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (11 1 (:DEFINITION PAIRLIS$))
 (10 10 (:TYPE-PRESCRIPTION SUBST-EACH-FOR-VAR))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (10 2 (:DEFINITION SYMBOL-ALISTP))
 (9 9 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (8 4 (:DEFINITION ADD-TO-SET-EQUAL))
 (7 7 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTSP-WITHIN))
 (7 1 (:DEFINITION QUOTE-LISTP))
 (7 1 (:DEFINITION INTERSECTP-EQUAL))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 1 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (5 5 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (5 5 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (5 1 (:DEFINITION CHARACTER-LISTP))
 (5 1 (:DEFINITION ASSOC-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (4 4 (:DEFINITION >?))
 (4 1 (:REWRITE DEFAULT-COERCE-3))
 (3 1 (:DEFINITION NFIX))
 (3 1 (:DEFINITION EQLABLE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION TRANSLATE-DECLARATION-TO-GUARD-GEN-LST))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (2 2 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION FLATTEN-ANDS-IN-LIT-LST))
 (2 2 (:TYPE-PRESCRIPTION ARGLISTP))
 (2 2 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 1 (:REWRITE DEFAULT-PKG-IMPORTS))
 (2 1 (:DEFINITION QUOTEP))
 (1 1 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 (1 1 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (1 1 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION EQLABLE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-SYMBOL-NAME))
 (1 1 (:REWRITE DEFAULT-REALPART))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 (1 1 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (1 1 (:REWRITE DEFAULT-IMAGPART))
 (1 1 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE DEFAULT-COMPLEX-2))
 (1 1 (:REWRITE DEFAULT-COMPLEX-1))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE DEFAULT-CODE-CHAR))
 (1 1 (:REWRITE DEFAULT-CHAR-CODE))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(NAT-LISTP-TERM-MEASURE-LIST
 (112 8 (:DEFINITION MAKE-LIST-AC))
 (64 8 (:REWRITE ZP-OPEN))
 (62 62 (:TYPE-PRESCRIPTION LEN))
 (30 6 (:DEFINITION LEN))
 (21 21 (:REWRITE DEFAULT-CDR))
 (20 14 (:REWRITE DEFAULT-+-2))
 (20 12 (:REWRITE DEFAULT-<-2))
 (16 16 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 3 (:DEFINITION STRIP-CDRS))
 (12 2 (:DEFINITION PSEUDO-TERM-LISTP))
 (10 2 (:DEFINITION SYMBOL-ALISTP))
 (4 4 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(NATP-TERM-MEASURE-NUM)
(LEN-MAKE-LIST-AC
 (72 40 (:REWRITE DEFAULT-+-2))
 (44 40 (:REWRITE DEFAULT-+-1))
 (21 19 (:REWRITE DEFAULT-CDR))
 (7 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (5 5 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(LEN-TERM-MEASURE-LIST
 (24168 1 (:DEFINITION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 (23722 1 (:DEFINITION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP1))
 (23614 1 (:DEFINITION TYPE-EXPRESSIONS-FROM-TYPE-SPEC))
 (23359 1 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD-GEN))
 (22895 25 (:DEFINITION CONJOIN?))
 (22870 199 (:DEFINITION CONJOIN))
 (22502 2 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD1-GEN))
 (11793 11763 (:REWRITE DEFAULT-CDR))
 (11003 10978 (:REWRITE DEFAULT-CAR))
 (3305 3 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD/INTEGER-GEN))
 (415 415 (:REWRITE CAR-CONS))
 (274 58 (:DEFINITION CONJOIN2))
 (255 5 (:DEFINITION PSEUDO-TERMP))
 (251 1 (:DEFINITION SUBST-EACH-FOR-VAR))
 (248 1 (:DEFINITION SUBST-VAR))
 (244 1 (:DEFINITION CONS-TERM))
 (243 140 (:REWRITE DEFAULT-+-2))
 (235 1 (:DEFINITION CONS-TERM1))
 (210 15 (:DEFINITION MAKE-LIST-AC))
 (157 140 (:REWRITE DEFAULT-+-1))
 (145 145 (:TYPE-PRESCRIPTION SUBST-VAR-LST))
 (120 15 (:REWRITE ZP-OPEN))
 (110 2 (:DEFINITION FLATTEN-ANDS-IN-LIT))
 (64 32 (:DEFINITION KWOTE?))
 (63 63 (:DEFINITION KWOTE))
 (63 1 (:DEFINITION FLATTEN-ANDS-IN-LIT-LST))
 (62 8 (:DEFINITION SUBSETP-EQUAL))
 (57 23 (:DEFINITION WEAK-SATISFIES-TYPE-SPEC-P))
 (55 2 (:DEFINITION DISJOIN?))
 (54 9 (:DEFINITION LENGTH))
 (53 3 (:DEFINITION OR-MACRO))
 (52 37 (:REWRITE DEFAULT-<-2))
 (44 4 (:DEFINITION SUMLIST))
 (42 37 (:REWRITE DEFAULT-<-1))
 (40 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (40 10 (:DEFINITION STRIP-CDRS))
 (39 15 (:DEFINITION MEMBER-EQUAL))
 (38 19 (:DEFINITION TRUE-LISTP))
 (36 2 (:DEFINITION DUMB-NEGATE-LIT))
 (28 6 (:DEFINITION BINARY-APPEND))
 (26 26 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (24 6 (:DEFINITION MV-NTH))
 (24 5 (:DEFINITION REVAPPEND))
 (21 1 (:DEFINITION LAMBDA-OBJECT-BODY))
 (20 20 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (20 2 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (19 19 (:DEFINITION <=?))
 (18 3 (:DEFINITION ALL-VARS))
 (16 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (15 5 (:DEFINITION SYMBOL-LISTP))
 (15 3 (:DEFINITION ALL-VARS1))
 (14 14 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP1))
 (14 14 (:TYPE-PRESCRIPTION NATP-TERM-MEASURE-NUM))
 (13 2 (:DEFINITION MAX))
 (12 12 (:TYPE-PRESCRIPTION FLATTEN-ANDS-IN-LIT))
 (11 11 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (11 1 (:DEFINITION PAIRLIS$))
 (10 10 (:TYPE-PRESCRIPTION SUBST-EACH-FOR-VAR))
 (9 9 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (8 4 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (8 4 (:DEFINITION ADD-TO-SET-EQUAL))
 (7 7 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTSP-WITHIN))
 (7 1 (:DEFINITION QUOTE-LISTP))
 (7 1 (:DEFINITION INTERSECTP-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION NATP-TERM-MEASURE-NIL))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 1 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (5 5 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (5 1 (:DEFINITION CHARACTER-LISTP))
 (5 1 (:DEFINITION ASSOC-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION SUMLIST))
 (4 4 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (4 4 (:DEFINITION >?))
 (4 1 (:REWRITE DEFAULT-COERCE-3))
 (3 1 (:DEFINITION EQLABLE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION TRANSLATE-DECLARATION-TO-GUARD-GEN-LST))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (2 2 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION FLATTEN-ANDS-IN-LIT-LST))
 (2 2 (:TYPE-PRESCRIPTION ARGLISTP))
 (2 2 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 1 (:REWRITE DEFAULT-PKG-IMPORTS))
 (2 1 (:DEFINITION QUOTEP))
 (1 1 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 (1 1 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (1 1 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION EQLABLE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-UNARY-/))
 (1 1 (:REWRITE DEFAULT-SYMBOL-NAME))
 (1 1 (:REWRITE DEFAULT-REALPART))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 (1 1 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (1 1 (:REWRITE DEFAULT-IMAGPART))
 (1 1 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE DEFAULT-COMPLEX-2))
 (1 1 (:REWRITE DEFAULT-COMPLEX-1))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE DEFAULT-CODE-CHAR))
 (1 1 (:REWRITE DEFAULT-CHAR-CODE))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
(SYMBOL-ALISTP-PAIRLIS$
 (24 22 (:REWRITE DEFAULT-CAR))
 (11 10 (:REWRITE DEFAULT-CDR))
 )
(EQUAL-LEN-0
 (9 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(NAT-LISTP-STRIP-CDRS-PAIRLIS$
 (26 24 (:REWRITE DEFAULT-CDR))
 (25 23 (:REWRITE DEFAULT-CAR))
 (24 18 (:REWRITE DEFAULT-<-1))
 (23 18 (:REWRITE DEFAULT-<-2))
 (22 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-+-1))
 )
(TM-INDUCT-HINT
 (916 468 (:REWRITE DEFAULT-+-2))
 (608 468 (:REWRITE DEFAULT-+-1))
 (426 426 (:REWRITE DEFAULT-CDR))
 (322 322 (:REWRITE DEFAULT-CAR))
 (280 70 (:DEFINITION INTEGER-ABS))
 (280 35 (:DEFINITION LENGTH))
 (128 16 (:DEFINITION NAT-LISTP))
 (105 94 (:REWRITE DEFAULT-<-2))
 (102 94 (:REWRITE DEFAULT-<-1))
 (80 16 (:DEFINITION SYMBOL-ALISTP))
 (70 70 (:REWRITE DEFAULT-UNARY-MINUS))
 (64 16 (:DEFINITION STRIP-CDRS))
 (48 16 (:DEFINITION NATP))
 (35 35 (:REWRITE DEFAULT-REALPART))
 (35 35 (:REWRITE DEFAULT-NUMERATOR))
 (35 35 (:REWRITE DEFAULT-IMAGPART))
 (35 35 (:REWRITE DEFAULT-DENOMINATOR))
 (35 35 (:REWRITE DEFAULT-COERCE-2))
 (35 35 (:REWRITE DEFAULT-COERCE-1))
 (18 6 (:DEFINITION SYMBOL-LISTP))
 (14 14 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (9 9 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (6 1 (:DEFINITION PSEUDO-TERM-LISTP))
 )
(STRIP-CARS-PAIRLIS$
 (15 14 (:REWRITE DEFAULT-CAR))
 (12 11 (:REWRITE DEFAULT-CDR))
 )
(STRIP-CDRS-PAIRLIS$
 (28 25 (:REWRITE DEFAULT-CDR))
 (20 17 (:REWRITE DEFAULT-CAR))
 (20 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 )
(CONSP-STRIP-CARS
 (29 29 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(MEMBER-EQUAL-STRIP-CARS
 (78 68 (:REWRITE DEFAULT-CAR))
 (32 24 (:REWRITE DEFAULT-CDR))
 )
(NOT-STRIP-CARS
 (16 16 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-CDR))
 )
(ALIST-ALL<=)
(ALL<=)
(ALIST-ALL<=-IMPLIES-<=-ASSOC-EQUAL
 (190 182 (:REWRITE DEFAULT-CAR))
 (133 126 (:REWRITE DEFAULT-CDR))
 (75 54 (:REWRITE DEFAULT-<-1))
 (34 34 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NATP-CDR-ASSOC-EQUAL
 (81 77 (:REWRITE DEFAULT-CAR))
 (56 52 (:REWRITE DEFAULT-CDR))
 (22 20 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(ALL<=-IMPLIES-ALIST-ALL<=-PAIRLIS&
 (40 27 (:REWRITE DEFAULT-<-1))
 (27 27 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(ALIST-ALL-<=-PRESERVES-ASSOC-EQUAL-IFF
 (116 116 (:REWRITE DEFAULT-CAR))
 (32 32 (:REWRITE DEFAULT-CDR))
 (22 22 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (22 11 (:REWRITE DEFAULT-<-2))
 (22 11 (:REWRITE DEFAULT-<-1))
 )
(<=-SUMLIST
 (35 17 (:REWRITE DEFAULT-<-2))
 (30 17 (:REWRITE DEFAULT-<-1))
 (26 26 (:REWRITE DEFAULT-CAR))
 (26 8 (:REWRITE DEFAULT-+-2))
 (17 17 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (13 8 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE DEFAULT-CDR))
 )
(TERM-MEASURE-LEMMA-1-1-GENERAL
 (2080 1982 (:REWRITE DEFAULT-CDR))
 (1640 609 (:REWRITE DEFAULT-+-2))
 (1619 1521 (:REWRITE DEFAULT-CAR))
 (968 88 (:DEFINITION SUMLIST))
 (913 609 (:REWRITE DEFAULT-+-1))
 (392 94 (:DEFINITION STRIP-CDRS))
 (352 32 (:DEFINITION PAIRLIS$))
 (250 164 (:REWRITE DEFAULT-<-1))
 (208 164 (:REWRITE DEFAULT-<-2))
 (176 88 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (176 8 (:REWRITE STRIP-CDRS-PAIRLIS$))
 (130 130 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (120 120 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (111 111 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (92 19 (:DEFINITION ASSOC-EQUAL))
 (88 88 (:TYPE-PRESCRIPTION SUMLIST))
 (44 44 (:TYPE-PRESCRIPTION PAIRLIS$))
 )
(TERM-MEASURE-LEMMA-1-1
 (560 2 (:DEFINITION TERM-MEASURE))
 (152 55 (:REWRITE DEFAULT-+-2))
 (142 136 (:REWRITE DEFAULT-CDR))
 (94 88 (:REWRITE DEFAULT-CAR))
 (88 8 (:DEFINITION SUMLIST))
 (85 17 (:DEFINITION LEN))
 (83 55 (:REWRITE DEFAULT-+-1))
 (42 2 (:DEFINITION LAMBDA-OBJECT-BODY))
 (32 2 (:REWRITE COMMUTATIVITY-2-OF-+))
 (30 6 (:REWRITE COMMUTATIVITY-OF-+))
 (28 28 (:TYPE-PRESCRIPTION TERM-MEASURE))
 (28 28 (:TYPE-PRESCRIPTION NATP-TERM-MEASURE-NUM))
 (26 4 (:DEFINITION MAX))
 (22 2 (:DEFINITION PAIRLIS$))
 (16 8 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (14 8 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (9 3 (:DEFINITION SYMBOL-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SUMLIST))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 2 (:DEFINITION STRIP-CDRS))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (6 3 (:DEFINITION TRUE-LISTP))
 (6 2 (:DEFINITION ASSOC-EQUAL))
 (6 1 (:DEFINITION NFIX))
 (3 3 (:TYPE-PRESCRIPTION NATP-CDR-ASSOC-EQUAL))
 (3 3 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 )
(TRUE-LISTP-TERM-MEASURE-LIST
 (210 15 (:DEFINITION MAKE-LIST-AC))
 (160 160 (:TYPE-PRESCRIPTION LEN))
 (148 145 (:REWRITE DEFAULT-CDR))
 (120 15 (:REWRITE ZP-OPEN))
 (118 115 (:REWRITE DEFAULT-CAR))
 (118 56 (:REWRITE DEFAULT-+-2))
 (110 22 (:DEFINITION LEN))
 (102 2 (:DEFINITION PSEUDO-TERMP))
 (70 56 (:REWRITE DEFAULT-+-1))
 (44 4 (:DEFINITION SUMLIST))
 (43 28 (:REWRITE DEFAULT-<-2))
 (40 10 (:DEFINITION STRIP-CDRS))
 (32 9 (:DEFINITION TRUE-LISTP))
 (31 28 (:REWRITE DEFAULT-<-1))
 (23 23 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (21 1 (:DEFINITION LAMBDA-OBJECT-BODY))
 (16 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (15 3 (:REWRITE COMMUTATIVITY-OF-+))
 (14 14 (:TYPE-PRESCRIPTION NATP-TERM-MEASURE-NUM))
 (14 14 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (13 2 (:DEFINITION MAX))
 (11 1 (:DEFINITION PAIRLIS$))
 (8 4 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (6 6 (:TYPE-PRESCRIPTION NATP-TERM-MEASURE-NIL))
 (6 6 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (6 1 (:DEFINITION NFIX))
 (5 1 (:DEFINITION ASSOC-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION SUMLIST))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:TYPE-PRESCRIPTION NATP-CDR-ASSOC-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 )
(TERM-MEASURE-LEMMA-1
 (1187 466 (:REWRITE DEFAULT-+-2))
 (1083 1029 (:REWRITE DEFAULT-CDR))
 (762 708 (:REWRITE DEFAULT-CAR))
 (670 466 (:REWRITE DEFAULT-+-1))
 (528 48 (:DEFINITION SUMLIST))
 (210 10 (:DEFINITION LAMBDA-OBJECT-BODY))
 (198 18 (:DEFINITION PAIRLIS$))
 (130 20 (:DEFINITION MAX))
 (96 48 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (83 83 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (66 11 (:DEFINITION PSEUDO-TERM-LISTP))
 (57 57 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (55 32 (:REWRITE DEFAULT-<-1))
 (48 48 (:TYPE-PRESCRIPTION SUMLIST))
 (48 48 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (38 14 (:DEFINITION ASSOC-EQUAL))
 (37 32 (:REWRITE DEFAULT-<-2))
 (36 4 (:DEFINITION NFIX))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (24 8 (:TYPE-PRESCRIPTION NATP-CDR-ASSOC-EQUAL))
 (16 16 (:TYPE-PRESCRIPTION PAIRLIS$))
 (10 10 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 (2 2 (:LINEAR <=-SUMLIST))
 )
(TERM-MEASURE-LEMMA-2
 (9001 3436 (:REWRITE DEFAULT-+-2))
 (8262 7878 (:REWRITE DEFAULT-CDR))
 (6426 28 (:LINEAR TERM-MEASURE-LEMMA-1-1))
 (5463 5088 (:REWRITE DEFAULT-CAR))
 (4968 3436 (:REWRITE DEFAULT-+-1))
 (1743 83 (:DEFINITION LAMBDA-OBJECT-BODY))
 (1362 132 (:DEFINITION PAIRLIS$))
 (842 421 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (547 547 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (503 503 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (473 251 (:REWRITE DEFAULT-<-1))
 (421 421 (:TYPE-PRESCRIPTION SUMLIST))
 (421 421 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (368 251 (:REWRITE DEFAULT-<-2))
 (243 96 (:DEFINITION ASSOC-EQUAL))
 (126 9 (:DEFINITION MAKE-LIST-AC))
 (83 83 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 (72 9 (:REWRITE ZP-OPEN))
 (36 36 (:LINEAR <=-SUMLIST))
 (27 9 (:DEFINITION NATP))
 (6 6 (:REWRITE ALIST-ALL-<=-PRESERVES-ASSOC-EQUAL-IFF))
 )
(ALL<=-REFLEXIVE
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(LEN-APPEND
 (48 24 (:REWRITE DEFAULT-+-2))
 (31 24 (:REWRITE DEFAULT-+-1))
 (20 10 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (18 15 (:REWRITE DEFAULT-CDR))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (3 3 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(LEN-TAKE
 (14 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (9 8 (:REWRITE DEFAULT-CDR))
 (6 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(TERM-MEASURE-FLG-T
 (420 30 (:DEFINITION MAKE-LIST-AC))
 (240 30 (:REWRITE ZP-OPEN))
 (234 234 (:TYPE-PRESCRIPTION LEN))
 (120 24 (:DEFINITION LEN))
 (106 106 (:REWRITE DEFAULT-CDR))
 (101 101 (:REWRITE DEFAULT-CAR))
 (78 54 (:REWRITE DEFAULT-+-2))
 (75 45 (:REWRITE DEFAULT-<-2))
 (60 15 (:DEFINITION STRIP-CDRS))
 (54 54 (:REWRITE DEFAULT-+-1))
 (45 45 (:REWRITE DEFAULT-<-1))
 (33 33 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (16 16 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(PSEUDO-TERM-LISTP-APPEND
 (51 1 (:DEFINITION PSEUDO-TERMP))
 (36 34 (:REWRITE DEFAULT-CDR))
 (36 34 (:REWRITE DEFAULT-CAR))
 (33 33 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (19 19 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (15 3 (:DEFINITION LEN))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 )
(TERM-MEASURE-T-APPEND
 (534 512 (:REWRITE DEFAULT-CDR))
 (485 463 (:REWRITE DEFAULT-CAR))
 (313 115 (:REWRITE DEFAULT-+-2))
 (306 6 (:DEFINITION PSEUDO-TERMP))
 (180 36 (:DEFINITION LEN))
 (178 178 (:TYPE-PRESCRIPTION LEN))
 (176 16 (:DEFINITION SUMLIST))
 (173 115 (:REWRITE DEFAULT-+-1))
 (168 42 (:DEFINITION STRIP-CDRS))
 (87 87 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (84 4 (:DEFINITION LAMBDA-OBJECT-BODY))
 (67 55 (:REWRITE DEFAULT-<-1))
 (65 13 (:REWRITE COMMUTATIVITY-OF-+))
 (64 4 (:REWRITE COMMUTATIVITY-2-OF-+))
 (57 55 (:REWRITE DEFAULT-<-2))
 (56 56 (:TYPE-PRESCRIPTION NATP-TERM-MEASURE-NUM))
 (53 53 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (52 8 (:DEFINITION MAX))
 (44 4 (:DEFINITION PAIRLIS$))
 (32 16 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (25 25 (:REWRITE FOLD-CONSTS-IN-+))
 (24 24 (:TYPE-PRESCRIPTION NATP-TERM-MEASURE-NIL))
 (24 4 (:DEFINITION NFIX))
 (22 1 (:DEFINITION MAKE-LIST-AC))
 (20 4 (:DEFINITION ASSOC-EQUAL))
 (20 1 (:REWRITE LEN-APPEND))
 (18 6 (:DEFINITION SYMBOL-LISTP))
 (16 16 (:TYPE-PRESCRIPTION SUMLIST))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 12 (:TYPE-PRESCRIPTION NATP-CDR-ASSOC-EQUAL))
 (12 6 (:DEFINITION TRUE-LISTP))
 (12 1 (:REWRITE ZP-OPEN))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 )
(SUMLIST-APPEND
 (1070 349 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (349 349 (:TYPE-PRESCRIPTION NAT-LISTP))
 (270 135 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (135 135 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (135 135 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (105 24 (:REWRITE DEFAULT-+-2))
 (61 24 (:REWRITE DEFAULT-+-1))
 (21 18 (:REWRITE DEFAULT-CAR))
 (18 18 (:LINEAR <=-SUMLIST))
 (18 15 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(+-HACK-1
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 5 (:REWRITE DEFAULT-+-2))
 (8 5 (:REWRITE DEFAULT-+-1))
 (5 3 (:REWRITE DEFAULT-<-1))
 (4 3 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(PSEUDO-TERM-LISTP-TAKE
 (51 1 (:DEFINITION PSEUDO-TERMP))
 (31 30 (:REWRITE DEFAULT-CDR))
 (31 30 (:REWRITE DEFAULT-CAR))
 (24 24 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (15 15 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (15 3 (:DEFINITION LEN))
 (11 8 (:REWRITE DEFAULT-+-2))
 (10 7 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE DEFAULT-+-1))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(TERM-MEASURE-T-TAKE
 (748 681 (:REWRITE DEFAULT-CDR))
 (625 560 (:REWRITE DEFAULT-CAR))
 (561 11 (:DEFINITION PSEUDO-TERMP))
 (548 269 (:REWRITE DEFAULT-+-2))
 (339 269 (:REWRITE DEFAULT-+-1))
 (220 20 (:DEFINITION SUMLIST))
 (193 21 (:DEFINITION MAKE-LIST-AC))
 (168 40 (:REWRITE ZP-OPEN))
 (156 39 (:DEFINITION STRIP-CDRS))
 (126 126 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (124 100 (:REWRITE DEFAULT-<-1))
 (109 100 (:REWRITE DEFAULT-<-2))
 (105 5 (:DEFINITION LAMBDA-OBJECT-BODY))
 (80 5 (:REWRITE COMMUTATIVITY-2-OF-+))
 (79 79 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (75 15 (:REWRITE COMMUTATIVITY-OF-+))
 (70 70 (:TYPE-PRESCRIPTION NATP-TERM-MEASURE-NUM))
 (65 10 (:DEFINITION MAX))
 (55 5 (:DEFINITION PAIRLIS$))
 (40 20 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (33 11 (:DEFINITION SYMBOL-LISTP))
 (31 31 (:REWRITE TERM-MEASURE-FLG-T))
 (30 30 (:TYPE-PRESCRIPTION NATP-TERM-MEASURE-NIL))
 (25 5 (:DEFINITION ASSOC-EQUAL))
 (22 11 (:DEFINITION TRUE-LISTP))
 (21 21 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 20 (:TYPE-PRESCRIPTION SUMLIST))
 (15 15 (:TYPE-PRESCRIPTION NATP-CDR-ASSOC-EQUAL))
 (11 11 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (5 5 (:TYPE-PRESCRIPTION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 )
(SUMLIST-TAKE
 (54 22 (:REWRITE DEFAULT-+-2))
 (30 14 (:REWRITE DEFAULT-<-2))
 (24 22 (:REWRITE DEFAULT-CAR))
 (21 14 (:REWRITE DEFAULT-<-1))
 (15 13 (:REWRITE DEFAULT-CDR))
 (13 7 (:REWRITE ZP-OPEN))
 (12 12 (:LINEAR <=-SUMLIST))
 (7 7 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE +-HACK-1))
 )
(CONSP-MV-NTH-1-REMOVE-GUARD-HOLDERS1-LST
 (6912 1 (:DEFINITION REMOVE-GUARD-HOLDERS1))
 (4542 224 (:DEFINITION CONS-TERM))
 (2923 224 (:DEFINITION CONS-TERM1))
 (2232 2023 (:REWRITE DEFAULT-CAR))
 (1744 1526 (:REWRITE DEFAULT-CDR))
 (1208 231 (:DEFINITION QUOTE-LISTP))
 (1049 4 (:DEFINITION SUBCOR-VAR))
 (580 580 (:TYPE-PRESCRIPTION SUBCOR-VAR-LST))
 (472 233 (:DEFINITION QUOTEP))
 (223 223 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (187 187 (:DEFINITION KWOTE))
 (162 54 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (57 57 (:DEFINITION TRIVIAL-LAMBDA-P))
 (57 5 (:DEFINITION SUBCOR-VAR1))
 (46 23 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (36 6 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (26 6 (:DEFINITION CHARACTER-LISTP))
 (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (23 23 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (18 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-<-1))
 (18 6 (:REWRITE DEFAULT-COERCE-3))
 (16 4 (:DEFINITION MEMBER-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (12 12 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (12 12 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (12 12 (:REWRITE DEFAULT-COERCE-2))
 (12 6 (:REWRITE DEFAULT-PKG-IMPORTS))
 (9 9 (:REWRITE CAR-CONS))
 (8 8 (:REWRITE CDR-CONS))
 (6 6 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:REWRITE DEFAULT-UNARY-/))
 (6 6 (:REWRITE DEFAULT-SYMBOL-NAME))
 (6 6 (:REWRITE DEFAULT-REALPART))
 (6 6 (:REWRITE DEFAULT-NUMERATOR))
 (6 6 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (6 6 (:REWRITE DEFAULT-IMAGPART))
 (6 6 (:REWRITE DEFAULT-DENOMINATOR))
 (6 6 (:REWRITE DEFAULT-COMPLEX-2))
 (6 6 (:REWRITE DEFAULT-COMPLEX-1))
 (6 6 (:REWRITE DEFAULT-COERCE-1))
 (6 6 (:REWRITE DEFAULT-CODE-CHAR))
 (6 6 (:REWRITE DEFAULT-CHAR-CODE))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-*-1))
 (5 1 (:DEFINITION BINARY-APPEND))
 (3 3 (:TYPE-PRESCRIPTION LAST))
 (3 1 (:DEFINITION TAKE))
 (3 1 (:DEFINITION LAST))
 )
(RGH-FLG-EXIT)
(RGH-BASE)
(RGH-LAMBDA-CASE)
(RGH-LAMBDA-EXIT)
(RGH-SYMBOLP-EXIT)
(REMOVE-GUARD-HOLDERS1-FLG
 (88013 32427 (:REWRITE DEFAULT-+-2))
 (46652 32427 (:REWRITE DEFAULT-+-1))
 (11560 2312 (:DEFINITION LEN))
 (7160 5303 (:REWRITE DEFAULT-<-2))
 (6099 5303 (:REWRITE DEFAULT-<-1))
 (4624 4624 (:REWRITE DEFAULT-UNARY-MINUS))
 (2312 2312 (:REWRITE DEFAULT-NUMERATOR))
 (2312 2312 (:REWRITE DEFAULT-DENOMINATOR))
 (2312 2312 (:REWRITE DEFAULT-COERCE-2))
 (2312 2312 (:REWRITE DEFAULT-COERCE-1))
 (2311 2311 (:REWRITE DEFAULT-REALPART))
 (2311 2311 (:REWRITE DEFAULT-IMAGPART))
 (154 154 (:REWRITE +-HACK-1))
 )
(REMOVE-GUARD-HOLDERS-FLG-ELIM
 (86413 3880 (:DEFINITION SUBCOR-VAR))
 (70893 4823 (:DEFINITION SUBCOR-VAR1))
 (36277 5457 (:DEFINITION QUOTE-LISTP))
 (4212 4212 (:TYPE-PRESCRIPTION LAST))
 (4120 824 (:DEFINITION BINARY-APPEND))
 (3982 824 (:DEFINITION TAKE))
 (1648 1648 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 )
(SYMBOL-FORWARD-TO-RGH-BASE)
(FQUOTEP-FORWARD-TO-RGH-BASE)
(HIDE-FORWARD-TO-RGH-BASE)
(WELL-FORMED-LAMBDA-OBJECTP-IMPLIES-SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP)
(TERM-MEASURE-LEMMA-4
 (160 2 (:LINEAR TERM-MEASURE-LEMMA-1-1))
 (65 65 (:REWRITE DEFAULT-CDR))
 (60 12 (:DEFINITION LEN))
 (55 55 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE DEFAULT-+-2))
 (18 4 (:DEFINITION SYMBOL-LISTP))
 (14 4 (:DEFINITION TRUE-LISTP))
 (12 12 (:REWRITE DEFAULT-+-1))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 4 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE PSEUDO-TERMP-REMOVE-GUARD-HOLDERS1))
 (1 1 (:REWRITE WELL-FORMED-LAMBDA-OBJECTP-IMPLIES-SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 )
(TERM-MEASURE-LEMMA-5
 (13482 1 (:DEFINITION SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP1))
 (13374 1 (:DEFINITION TYPE-EXPRESSIONS-FROM-TYPE-SPEC))
 (13363 1 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD-GEN))
 (12917 25 (:DEFINITION CONJOIN?))
 (12892 199 (:DEFINITION CONJOIN))
 (12878 2 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD1-GEN))
 (6630 6622 (:REWRITE DEFAULT-CDR))
 (5863 5859 (:REWRITE DEFAULT-CAR))
 (1925 3 (:DEFINITION TRANSLATE-DECLARATION-TO-GUARD/INTEGER-GEN))
 (274 58 (:DEFINITION CONJOIN2))
 (160 2 (:LINEAR TERM-MEASURE-LEMMA-1-1))
 (120 24 (:DEFINITION LEN))
 (110 2 (:DEFINITION FLATTEN-ANDS-IN-LIT))
 (87 63 (:REWRITE DEFAULT-+-2))
 (64 32 (:DEFINITION KWOTE?))
 (63 63 (:REWRITE DEFAULT-+-1))
 (63 1 (:DEFINITION FLATTEN-ANDS-IN-LIT-LST))
 (57 23 (:DEFINITION WEAK-SATISFIES-TYPE-SPEC-P))
 (54 9 (:DEFINITION LENGTH))
 (44 19 (:DEFINITION TRUE-LISTP))
 (37 2 (:DEFINITION DISJOIN?))
 (36 2 (:DEFINITION DUMB-NEGATE-LIT))
 (35 3 (:DEFINITION OR-MACRO))
 (32 32 (:DEFINITION KWOTE))
 (32 4 (:DEFINITION SUBSETP-EQUAL))
 (25 5 (:DEFINITION BINARY-APPEND))
 (24 5 (:DEFINITION REVAPPEND))
 (21 5 (:DEFINITION SYMBOL-LISTP))
 (19 19 (:DEFINITION <=?))
 (15 5 (:DEFINITION MEMBER-EQUAL))
 (12 12 (:TYPE-PRESCRIPTION FLATTEN-ANDS-IN-LIT))
 (10 10 (:TYPE-PRESCRIPTION SUBST-EACH-FOR-VAR))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (8 8 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (7 1 (:DEFINITION SUBST-EACH-FOR-VAR))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (4 4 (:DEFINITION >?))
 (4 1 (:DEFINITION SUBST-VAR))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 1 (:DEFINITION EQLABLE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION TRANSLATE-DECLARATION-TO-GUARD-GEN-LST))
 (2 2 (:TYPE-PRESCRIPTION FLATTEN-ANDS-IN-LIT-LST))
 (2 2 (:REWRITE PSEUDO-TERMP-REMOVE-GUARD-HOLDERS1))
 (2 1 (:DEFINITION ADD-TO-SET-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION EQLABLE-LISTP))
 (1 1 (:REWRITE WELL-FORMED-LAMBDA-OBJECTP-IMPLIES-SYNTACTICALLY-PLAUSIBLE-LAMBDA-OBJECTP))
 )
(CLEAN-UP-DIRTY-LAMBDA-OBJECTS
 (36708 33305 (:REWRITE DEFAULT-CDR))
 (31168 11764 (:REWRITE DEFAULT-+-2))
 (24931 22782 (:REWRITE DEFAULT-CAR))
 (17262 19 (:DEFINITION WARRANTS-FOR-TAMEP))
 (17226 11764 (:REWRITE DEFAULT-+-1))
 (9491 19 (:DEFINITION FIND-WARRANT-FUNCTION-NAME))
 (6090 38 (:DEFINITION WARRANT-NAME))
 (5748 38 (:DEFINITION STRING-APPEND))
 (5558 608 (:DEFINITION BINARY-APPEND))
 (4830 2374 (:TYPE-PRESCRIPTION NATP-CDR-ASSOC-EQUAL))
 (4422 402 (:DEFINITION PAIRLIS$))
 (3667 19 (:DEFINITION EXECUTABLE-BADGE))
 (2954 1477 (:TYPE-PRESCRIPTION NATP-SUMLIST))
 (2926 266 (:DEFINITION FGETPROP))
 (1891 1891 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1733 922 (:REWRITE DEFAULT-<-1))
 (1477 1477 (:TYPE-PRESCRIPTION SUMLIST))
 (1477 1477 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1234 1234 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1148 922 (:REWRITE DEFAULT-<-2))
 (912 76 (:DEFINITION TABLE-ALIST))
 (684 76 (:DEFINITION HONS-GET))
 (646 646 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (646 646 (:REWRITE DEFAULT-COERCE-2))
 (628 628 (:REWRITE TERM-MEASURE-FLG-T))
 (608 608 (:REWRITE DEFAULT-SYMBOL-NAME))
 (608 608 (:REWRITE DEFAULT-COERCE-1))
 (608 76 (:DEFINITION HONS-ASSOC-EQUAL))
 (456 38 (:DEFINITION GLOBAL-VAL))
 (405 45 (:DEFINITION NFIX))
 (350 25 (:DEFINITION MAKE-LIST-AC))
 (228 38 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (202 202 (:TYPE-PRESCRIPTION PAIRLIS$))
 (200 25 (:REWRITE ZP-OPEN))
 (158 2 (:LINEAR TERM-MEASURE-LEMMA-2))
 (114 114 (:TYPE-PRESCRIPTION SYMBOLP-INTERN-IN-PACKAGE-OF-SYMBOL))
 (100 4 (:REWRITE NAT-LISTP-STRIP-CDRS-PAIRLIS$))
 (90 10 (:DEFINITION SUBSETP-EQUAL))
 (76 76 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (76 76 (:DEFINITION HONS-EQUAL))
 (76 38 (:REWRITE DEFAULT-PKG-IMPORTS))
 (76 38 (:DEFINITION ADD-TO-SET-EQUAL))
 (68 48 (:DEFINITION MEMBER-EQUAL))
 (38 38 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (38 38 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (38 38 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (38 38 (:REWRITE DEFAULT-COERCE-3))
 (35 5 (:DEFINITION SYMBOL-ALISTP))
 (24 4 (:DEFINITION STRIP-CDRS))
 (12 6 (:REWRITE EQUAL-LEN-0))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 10 (:LINEAR <=-SUMLIST))
 (8 8 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (6 6 (:REWRITE +-HACK-1))
 )
(MAY-CONTAIN-DIRTY-LAMBDA-OBJECTSP
 (931 384 (:REWRITE DEFAULT-+-2))
 (540 384 (:REWRITE DEFAULT-+-1))
 (264 66 (:DEFINITION INTEGER-ABS))
 (264 33 (:DEFINITION LENGTH))
 (165 33 (:DEFINITION LEN))
 (110 79 (:REWRITE DEFAULT-<-2))
 (88 79 (:REWRITE DEFAULT-<-1))
 (66 66 (:REWRITE DEFAULT-UNARY-MINUS))
 (33 33 (:TYPE-PRESCRIPTION LEN))
 (33 33 (:REWRITE DEFAULT-REALPART))
 (33 33 (:REWRITE DEFAULT-NUMERATOR))
 (33 33 (:REWRITE DEFAULT-IMAGPART))
 (33 33 (:REWRITE DEFAULT-DENOMINATOR))
 (33 33 (:REWRITE DEFAULT-COERCE-2))
 (33 33 (:REWRITE DEFAULT-COERCE-1))
 (9 9 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(POSSIBLY-CLEAN-UP-DIRTY-LAMBDA-OBJECTS)
(REMOVE-GUARD-HOLDERS
 (5 5 (:TYPE-PRESCRIPTION POSSIBLY-CLEAN-UP-DIRTY-LAMBDA-OBJECTS))
 )
