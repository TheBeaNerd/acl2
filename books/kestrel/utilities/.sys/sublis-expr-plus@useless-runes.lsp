(SUBLIS-EXPR+-RESTRICT-ALIST-AUX
 (28 28 (:REWRITE DEFAULT-CAR))
 (17 17 (:REWRITE DEFAULT-CDR))
 (5 1 (:DEFINITION ASSOC-EQUAL))
 )
(SUBLIS-EXPR+-RESTRICT-ALIST
 (992 13 (:DEFINITION PSEUDO-TERMP))
 (456 448 (:REWRITE DEFAULT-CDR))
 (325 39 (:DEFINITION LENGTH))
 (260 52 (:DEFINITION LEN))
 (192 192 (:TYPE-PRESCRIPTION LEN))
 (104 52 (:REWRITE DEFAULT-+-2))
 (96 8 (:DEFINITION SUBLIS-EXPR+-RESTRICT-ALIST-AUX))
 (95 19 (:DEFINITION ASSOC-EQUAL))
 (82 26 (:DEFINITION TRUE-LISTP))
 (79 18 (:DEFINITION SYMBOL-LISTP))
 (75 15 (:DEFINITION ALL-VARS1))
 (71 71 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (52 52 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (52 52 (:REWRITE DEFAULT-+-1))
 (40 40 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (30 15 (:DEFINITION ADD-TO-SET-EQUAL))
 (26 26 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALL-VARS1-TYPE))
 (15 15 (:DEFINITION MEMBER-EQUAL))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (13 13 (:REWRITE DEFAULT-COERCE-1))
 )
(MAKE-LAMBDA-TERM)
(SUBLIS-EXPR+
 (455 187 (:REWRITE DEFAULT-+-2))
 (263 187 (:REWRITE DEFAULT-+-1))
 (128 32 (:DEFINITION INTEGER-ABS))
 (128 16 (:DEFINITION LENGTH))
 (80 16 (:DEFINITION LEN))
 (53 38 (:REWRITE DEFAULT-<-2))
 (42 38 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (30 6 (:DEFINITION ASSOC-EQUAL))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-ALISTP-PAIRLIS$
 (24 22 (:REWRITE DEFAULT-CAR))
 (11 10 (:REWRITE DEFAULT-CDR))
 )
(R-SYMBOL-ALISTP-FORWARD-TO-ALISTP
 (21 21 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE DEFAULT-CDR))
 )
(SUBLIS-EXPR+-RESTRICT-ALIST-PRESERVES-PSEUDO-TERM-LISTP-STRIP-CARS
 (324 312 (:REWRITE DEFAULT-CAR))
 (256 4 (:DEFINITION PSEUDO-TERMP))
 (252 240 (:REWRITE DEFAULT-CDR))
 (100 12 (:DEFINITION LENGTH))
 (80 16 (:DEFINITION LEN))
 (75 15 (:DEFINITION ALL-VARS1))
 (60 60 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (36 36 (:TYPE-PRESCRIPTION LEN))
 (36 36 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (32 16 (:REWRITE DEFAULT-+-2))
 (30 15 (:DEFINITION ADD-TO-SET-EQUAL))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 8 (:DEFINITION TRUE-LISTP))
 (15 15 (:DEFINITION MEMBER-EQUAL))
 (12 4 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(SUBLIS-EXPR+-RESTRICT-ALIST-PRESERVES-R-SYMBOL-ALISTP
 (220 216 (:REWRITE DEFAULT-CAR))
 (168 166 (:REWRITE DEFAULT-CDR))
 (75 15 (:DEFINITION ALL-VARS1))
 (30 15 (:DEFINITION ADD-TO-SET-EQUAL))
 (15 15 (:DEFINITION MEMBER-EQUAL))
 )
(FLAG-SUBLIS-EXPR+
 (787 347 (:REWRITE DEFAULT-+-2))
 (486 347 (:REWRITE DEFAULT-+-1))
 (264 66 (:DEFINITION INTEGER-ABS))
 (264 33 (:DEFINITION LENGTH))
 (165 33 (:DEFINITION LEN))
 (108 81 (:REWRITE DEFAULT-<-2))
 (94 81 (:REWRITE DEFAULT-<-1))
 (66 66 (:REWRITE DEFAULT-UNARY-MINUS))
 (35 7 (:DEFINITION ASSOC-EQUAL))
 (33 33 (:TYPE-PRESCRIPTION LEN))
 (33 33 (:REWRITE DEFAULT-REALPART))
 (33 33 (:REWRITE DEFAULT-NUMERATOR))
 (33 33 (:REWRITE DEFAULT-IMAGPART))
 (33 33 (:REWRITE DEFAULT-DENOMINATOR))
 (33 33 (:REWRITE DEFAULT-COERCE-2))
 (33 33 (:REWRITE DEFAULT-COERCE-1))
 (16 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(FLAG-SUBLIS-EXPR+-EQUIVALENCES)
(R-SYMBOL-ALISTP-IMPLIES-PSEUDO-TERMP-CDR-ASSOC
 (81 81 (:REWRITE DEFAULT-CAR))
 (80 16 (:DEFINITION LEN))
 (79 79 (:REWRITE DEFAULT-CDR))
 (32 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 8 (:DEFINITION TRUE-LISTP))
 (12 4 (:DEFINITION SYMBOL-LISTP))
 (9 9 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 4 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(LEN-SUBLIS-EXPR+-LST
 (354 1 (:DEFINITION SUBLIS-EXPR+))
 (244 1 (:DEFINITION CONS-TERM))
 (235 1 (:DEFINITION CONS-TERM1))
 (98 79 (:REWRITE DEFAULT-CDR))
 (73 55 (:REWRITE DEFAULT-CAR))
 (61 1 (:DEFINITION SUBLIS-EXPR+-RESTRICT-ALIST))
 (49 25 (:REWRITE DEFAULT-+-2))
 (36 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (31 31 (:DEFINITION KWOTE))
 (28 2 (:DEFINITION SUBLIS-EXPR+-RESTRICT-ALIST-AUX))
 (26 4 (:DEFINITION ASSOC-EQUAL))
 (26 1 (:DEFINITION MAKE-LAMBDA-TERM))
 (25 25 (:REWRITE DEFAULT-+-1))
 (18 3 (:DEFINITION ALL-VARS))
 (15 3 (:DEFINITION ALL-VARS1))
 (11 1 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (8 2 (:DEFINITION BINARY-APPEND))
 (7 1 (:DEFINITION QUOTE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALL-VARS1-TYPE))
 (6 6 (:TYPE-PRESCRIPTION PAIRLIS$))
 (6 4 (:DEFINITION MEMBER-EQUAL))
 (6 3 (:DEFINITION ADD-TO-SET-EQUAL))
 (6 1 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (5 1 (:DEFINITION PAIRLIS$))
 (5 1 (:DEFINITION CHARACTER-LISTP))
 (4 1 (:REWRITE DEFAULT-COERCE-3))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION SUBLIS-EXPR+-RESTRICT-ALIST-AUX))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (2 2 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 1 (:REWRITE DEFAULT-PKG-IMPORTS))
 (2 1 (:DEFINITION QUOTEP))
 (1 1 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (1 1 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
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
(PSEUDO-TERM-LISTP-APPEND
 (64 1 (:DEFINITION PSEUDO-TERMP))
 (43 40 (:REWRITE DEFAULT-CDR))
 (41 41 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (41 38 (:REWRITE DEFAULT-CAR))
 (25 3 (:DEFINITION LENGTH))
 (22 22 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (20 4 (:DEFINITION LEN))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (8 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 2 (:DEFINITION TRUE-LISTP))
 (3 1 (:DEFINITION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 )
(PSEUDO-TERM-LISTP-SET-DIFFERENCE-EQUAL
 (128 2 (:DEFINITION PSEUDO-TERMP))
 (65 64 (:REWRITE DEFAULT-CDR))
 (64 63 (:REWRITE DEFAULT-CAR))
 (50 6 (:DEFINITION LENGTH))
 (40 8 (:DEFINITION LEN))
 (35 35 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (20 20 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (16 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 4 (:DEFINITION TRUE-LISTP))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-LISTP-IMPLIES-PSEUDO-TERM-LISTP
 (13 13 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 )
(SYMBOL-LISTP-APPEND
 (21 18 (:REWRITE DEFAULT-CAR))
 (18 15 (:REWRITE DEFAULT-CDR))
 (18 9 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (9 9 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (9 9 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(SYMBOL-LISTP-SET-DIFFERENCE-EQUAL
 (32 31 (:REWRITE DEFAULT-CAR))
 (21 20 (:REWRITE DEFAULT-CDR))
 )
(FLAG-LEMMA-FOR-PSEUDO-TERMP-SUBLIS-EXPR+
 (5676 3809 (:REWRITE DEFAULT-CAR))
 (5274 4115 (:REWRITE DEFAULT-CDR))
 (3548 437 (:DEFINITION SYMBOL-LISTP))
 (1730 28 (:DEFINITION SUBLIS-EXPR+-RESTRICT-ALIST))
 (784 56 (:DEFINITION SUBLIS-EXPR+-RESTRICT-ALIST-AUX))
 (645 163 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (385 77 (:DEFINITION ALL-VARS1))
 (384 384 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (291 154 (:REWRITE DEFAULT-+-2))
 (287 287 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (231 21 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (168 168 (:TYPE-PRESCRIPTION PAIRLIS$))
 (158 154 (:REWRITE DEFAULT-+-1))
 (154 154 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALL-VARS1-TYPE))
 (154 77 (:DEFINITION ADD-TO-SET-EQUAL))
 (140 98 (:DEFINITION MEMBER-EQUAL))
 (140 28 (:DEFINITION PAIRLIS$))
 (136 34 (:DEFINITION BINARY-APPEND))
 (102 17 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (86 18 (:DEFINITION CHARACTER-LISTP))
 (67 53 (:REWRITE DEFAULT-<-1))
 (65 17 (:REWRITE DEFAULT-COERCE-3))
 (62 62 (:REWRITE DEFAULT-COERCE-2))
 (56 56 (:TYPE-PRESCRIPTION SUBLIS-EXPR+-RESTRICT-ALIST-AUX))
 (53 53 (:REWRITE DEFAULT-<-2))
 (45 45 (:REWRITE DEFAULT-COERCE-1))
 (44 44 (:TYPE-PRESCRIPTION SUBLIS-EXPR+-RESTRICT-ALIST))
 (34 34 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (34 34 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (34 17 (:REWRITE DEFAULT-PKG-IMPORTS))
 (21 21 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (17 17 (:REWRITE DEFAULT-UNARY-MINUS))
 (17 17 (:REWRITE DEFAULT-UNARY-/))
 (17 17 (:REWRITE DEFAULT-SYMBOL-NAME))
 (17 17 (:REWRITE DEFAULT-REALPART))
 (17 17 (:REWRITE DEFAULT-NUMERATOR))
 (17 17 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (17 17 (:REWRITE DEFAULT-IMAGPART))
 (17 17 (:REWRITE DEFAULT-DENOMINATOR))
 (17 17 (:REWRITE DEFAULT-COMPLEX-2))
 (17 17 (:REWRITE DEFAULT-COMPLEX-1))
 (17 17 (:REWRITE DEFAULT-CODE-CHAR))
 (17 17 (:REWRITE DEFAULT-CHAR-CODE))
 (17 17 (:REWRITE DEFAULT-*-2))
 (17 17 (:REWRITE DEFAULT-*-1))
 )
(PSEUDO-TERMP-SUBLIS-EXPR+)
(PSEUDO-TERM-LISTP-SUBLIS-EXPR+-LST)
(SUBLIS-EXPR+
 (653 68 (:REWRITE SYMBOL-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (564 546 (:REWRITE DEFAULT-CDR))
 (563 545 (:REWRITE DEFAULT-CAR))
 (358 1 (:DEFINITION SUBLIS-EXPR+))
 (244 1 (:DEFINITION CONS-TERM))
 (235 1 (:DEFINITION CONS-TERM1))
 (177 89 (:REWRITE DEFAULT-+-2))
 (151 151 (:TYPE-PRESCRIPTION SUBLIS-EXPR+-LST))
 (124 2 (:DEFINITION SUBLIS-EXPR+-RESTRICT-ALIST))
 (109 19 (:DEFINITION ASSOC-EQUAL))
 (89 89 (:REWRITE DEFAULT-+-1))
 (67 67 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (66 16 (:DEFINITION STRIP-CARS))
 (58 58 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (56 4 (:DEFINITION SUBLIS-EXPR+-RESTRICT-ALIST-AUX))
 (36 9 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (31 31 (:DEFINITION KWOTE))
 (30 5 (:DEFINITION ALL-VARS))
 (28 4 (:DEFINITION SYMBOL-ALISTP))
 (26 1 (:DEFINITION MAKE-LAMBDA-TERM))
 (25 5 (:DEFINITION ALL-VARS1))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (15 15 (:REWRITE DEFAULT-COERCE-1))
 (11 1 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALL-VARS1-TYPE))
 (10 5 (:DEFINITION ADD-TO-SET-EQUAL))
 (9 3 (:DEFINITION SUBLIS-EXPR+-LST))
 (8 6 (:DEFINITION MEMBER-EQUAL))
 (8 2 (:DEFINITION BINARY-APPEND))
 (7 1 (:DEFINITION QUOTE-LISTP))
 (6 1 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (5 1 (:DEFINITION CHARACTER-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SUBLIS-EXPR+-RESTRICT-ALIST-AUX))
 (4 1 (:REWRITE DEFAULT-COERCE-3))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (2 2 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (2 1 (:REWRITE DEFAULT-PKG-IMPORTS))
 (2 1 (:DEFINITION QUOTEP))
 (1 1 (:TYPE-PRESCRIPTION STRINGP-SYMBOL-PACKAGE-NAME))
 (1 1 (:TYPE-PRESCRIPTION QUOTE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
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
 (1 1 (:REWRITE DEFAULT-CODE-CHAR))
 (1 1 (:REWRITE DEFAULT-CHAR-CODE))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE DEFAULT-*-1))
 )
