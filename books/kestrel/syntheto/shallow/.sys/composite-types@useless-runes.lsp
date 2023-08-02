(SYNTHETO::PARSE-MIXED-LISTS-AND-KEYVALS-AUX
 (6795 244 (:DEFINITION TRUE-LISTP))
 (6020 1799 (:REWRITE DEFAULT-+-2))
 (3975 1447 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP))
 (3975 1447 (:REWRITE SYNTHETO::TYPE-REF-CONSTRUCTOR-P-IMPLIES-CONSP))
 (3840 480 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (3550 3550 (:TYPE-PRESCRIPTION SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P))
 (3550 3550 (:TYPE-PRESCRIPTION SYNTHETO::TYPE-REF-CONSTRUCTOR-P))
 (3067 1799 (:REWRITE DEFAULT-+-1))
 (2877 201 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (2039 969 (:REWRITE DEFAULT-CDR))
 (2008 32 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-TRUE-LIST-LISTP))
 (1984 16 (:DEFINITION TRUE-LIST-LISTP))
 (1661 87 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (1586 564 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (1586 564 (:REWRITE SYNTHETO::CONSP-CDR-IF-TYPE-REF-CONSTRUCTOR-P))
 (1586 564 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (1200 80 (:REWRITE SYMBOL-PACKAGE-NAME-WHEN-MEMBER-EQUAL-OF-COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE))
 (1170 90 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (960 960 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (960 480 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (960 480 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (960 80 (:DEFINITION MEMBER-EQUAL))
 (840 840 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (767 396 (:REWRITE DEFAULT-<-2))
 (696 24 (:LINEAR ACL2-COUNT-OF-SUM))
 (684 396 (:REWRITE DEFAULT-<-1))
 (675 38 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (626 19 (:DEFINITION SYMBOL-LISTP))
 (480 480 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (480 480 (:TYPE-PRESCRIPTION COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE))
 (480 480 (:REWRITE SET::IN-SET))
 (475 395 (:REWRITE DEFAULT-CAR))
 (450 90 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (450 90 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (432 12 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (416 32 (:REWRITE TRUE-LIST-LISTP-WHEN-NOT-CONSP))
 (400 400 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (400 400 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (400 400 (:LINEAR LEN-WHEN-PREFIXP))
 (393 135 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDDR))
 (386 1 (:LINEAR ACL2-COUNT-OF-CONS-GREATER))
 (380 38 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (330 330 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (330 220 (:REWRITE STR::CONSP-OF-EXPLODE))
 (223 223 (:REWRITE DEFAULT-UNARY-MINUS))
 (182 91 (:REWRITE ALISTP-WHEN-PSEUDO-TERM-ALISTP-CHEAP))
 (180 180 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (180 180 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (180 90 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (180 90 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (174 87 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (152 8 (:REWRITE ALISTP-OF-CDR))
 (126 126 (:REWRITE DEFAULT-DENOMINATOR))
 (110 110 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (108 90 (:REWRITE ALISTP-WHEN-ATOM))
 (106 106 (:REWRITE DEFAULT-NUMERATOR))
 (97 97 (:REWRITE DEFAULT-REALPART))
 (97 97 (:REWRITE DEFAULT-IMAGPART))
 (91 91 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (91 91 (:TYPE-PRESCRIPTION PSEUDO-TERM-ALISTP))
 (80 80 (:REWRITE SYMBOL-PACKAGE-NAME-WHEN-MEMBER-EQUAL-AND-ALL-SYMBOLS-HAVE-PACKAGEP))
 (80 80 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (74 74 (:REWRITE NOT-EQUAL-OF-SYMBOL-PACKAGE-NAME-WHEN-NOT-MEMBER-EQUAL-OF-MAP-SYMBOL-PACKAGE-NAME))
 (50 25 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (48 24 (:REWRITE TRUE-LIST-LISTP-OF-CDR-WHEN-TRUE-LIST-LISTP))
 (22 4 (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (22 4 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (16 2 (:DEFINITION RATIONAL-LISTP))
 (16 2 (:DEFINITION INTEGER-LISTP))
 (8 4 (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (8 4 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (8 4 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1 1 (:REWRITE ALIST-FIX-OF-ATOM))
 )
(SYNTHETO::TRUE-LISTP-OF-PARSE-MIXED-LISTS-AND-KEYVALS-AUX.LIST-ARGS
 (1619 81 (:DEFINITION TRUE-LISTP))
 (1520 41 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (1280 160 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (792 44 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (746 22 (:DEFINITION SYMBOL-LISTP))
 (736 252 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP))
 (736 252 (:REWRITE SYNTHETO::TYPE-REF-CONSTRUCTOR-P-IMPLIES-CONSP))
 (654 654 (:TYPE-PRESCRIPTION SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P))
 (654 654 (:TYPE-PRESCRIPTION SYNTHETO::TYPE-REF-CONSTRUCTOR-P))
 (475 19 (:REWRITE ALIST-FIX-WHEN-ALISTP))
 (445 44 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (429 33 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (391 40 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (320 320 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (320 160 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (320 160 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (292 292 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (266 14 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (264 94 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (264 94 (:REWRITE SYNTHETO::CONSP-CDR-IF-TYPE-REF-CONSTRUCTOR-P))
 (264 94 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (242 229 (:REWRITE DEFAULT-CDR))
 (195 13 (:REWRITE SYMBOL-PACKAGE-NAME-WHEN-MEMBER-EQUAL-OF-COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE))
 (165 33 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (165 33 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (160 160 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (160 160 (:REWRITE SET::IN-SET))
 (156 13 (:DEFINITION MEMBER-EQUAL))
 (147 33 (:REWRITE ALISTP-WHEN-ATOM))
 (143 130 (:REWRITE DEFAULT-CAR))
 (103 13 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (102 51 (:REWRITE DEFAULT-+-2))
 (91 33 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDDR))
 (78 78 (:TYPE-PRESCRIPTION COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE))
 (70 70 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (70 70 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (70 70 (:LINEAR LEN-WHEN-PREFIXP))
 (66 66 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (66 66 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (66 66 (:TYPE-PRESCRIPTION ALISTP))
 (66 33 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (66 33 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (66 33 (:REWRITE ALISTP-WHEN-PSEUDO-TERM-ALISTP-CHEAP))
 (60 30 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (51 51 (:REWRITE DEFAULT-+-1))
 (33 33 (:TYPE-PRESCRIPTION PSEUDO-TERM-ALISTP))
 (30 15 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (29 29 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (19 19 (:REWRITE ALIST-FIX-OF-ATOM))
 (13 13 (:REWRITE SYMBOL-PACKAGE-NAME-WHEN-MEMBER-EQUAL-AND-ALL-SYMBOLS-HAVE-PACKAGEP))
 (13 2 (:REWRITE REV-WHEN-NOT-CONSP))
 (9 9 (:REWRITE NOT-EQUAL-OF-SYMBOL-PACKAGE-NAME-WHEN-NOT-MEMBER-EQUAL-OF-MAP-SYMBOL-PACKAGE-NAME))
 (4 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(SYNTHETO::ALISTP-OF-PARSE-MIXED-LISTS-AND-KEYVALS-AUX.KEYS-AND-VALS
 (1075 47 (:DEFINITION TRUE-LISTP))
 (884 68 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (792 44 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (746 22 (:DEFINITION SYMBOL-LISTP))
 (739 253 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP))
 (739 253 (:REWRITE SYNTHETO::TYPE-REF-CONSTRUCTOR-P-IMPLIES-CONSP))
 (736 92 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (656 656 (:TYPE-PRESCRIPTION SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P))
 (656 656 (:TYPE-PRESCRIPTION SYNTHETO::TYPE-REF-CONSTRUCTOR-P))
 (475 19 (:REWRITE ALIST-FIX-WHEN-ALISTP))
 (445 44 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (392 68 (:REWRITE ALISTP-WHEN-ATOM))
 (391 40 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (364 364 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (340 68 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (340 68 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (266 14 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (264 94 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (264 94 (:REWRITE SYNTHETO::CONSP-CDR-IF-TYPE-REF-CONSTRUCTOR-P))
 (264 94 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (209 209 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (208 195 (:REWRITE DEFAULT-CDR))
 (195 13 (:REWRITE SYMBOL-PACKAGE-NAME-WHEN-MEMBER-EQUAL-OF-COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE))
 (184 184 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (184 92 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (184 92 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (156 13 (:DEFINITION MEMBER-EQUAL))
 (143 130 (:REWRITE DEFAULT-CAR))
 (140 70 (:REWRITE ALISTP-WHEN-PSEUDO-TERM-ALISTP-CHEAP))
 (136 136 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (136 136 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (136 68 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (136 68 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (103 13 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (102 51 (:REWRITE DEFAULT-+-2))
 (92 92 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (92 92 (:REWRITE SET::IN-SET))
 (91 33 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDDR))
 (78 78 (:TYPE-PRESCRIPTION COMMON-LISP-SYMBOLS-FROM-MAIN-LISP-PACKAGE))
 (70 70 (:TYPE-PRESCRIPTION PSEUDO-TERM-ALISTP))
 (70 70 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (70 70 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (70 70 (:LINEAR LEN-WHEN-PREFIXP))
 (60 30 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (51 51 (:REWRITE DEFAULT-+-1))
 (30 15 (:REWRITE IFF-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (29 29 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (28 14 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (19 19 (:REWRITE ALIST-FIX-OF-ATOM))
 (13 13 (:REWRITE SYMBOL-PACKAGE-NAME-WHEN-MEMBER-EQUAL-AND-ALL-SYMBOLS-HAVE-PACKAGEP))
 (13 2 (:REWRITE REV-WHEN-NOT-CONSP))
 (9 9 (:REWRITE NOT-EQUAL-OF-SYMBOL-PACKAGE-NAME-WHEN-NOT-MEMBER-EQUAL-OF-MAP-SYMBOL-PACKAGE-NAME))
 (4 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(SYNTHETO::PARSE-MIXED-LISTS-AND-KEYVALS)
(SYNTHETO::TRUE-LISTP-OF-PARSE-MIXED-LISTS-AND-KEYVALS.LIST-ARGS)
(SYNTHETO::ALISTP-OF-PARSE-MIXED-LISTS-AND-KEYVALS.KEYS-AND-VALS)
(SYNTHETO::REQFIX-FUNCTION-NAME)
(SYNTHETO::CONSTRUCT-REQFIX-FUNCTION)
(SYNTHETO::CONSTRUCT-REQFIX-FUNCTIONS-RECUR
 (874 8 (:DEFINITION ACL2-COUNT))
 (170 8 (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (170 8 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (164 4 (:DEFINITION RATIONAL-LISTP))
 (164 4 (:DEFINITION INTEGER-LISTP))
 (133 48 (:REWRITE DEFAULT-+-2))
 (130 5 (:DEFINITION LENGTH))
 (115 5 (:DEFINITION LEN))
 (104 8 (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (104 8 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (94 34 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP))
 (94 34 (:REWRITE SYNTHETO::TYPE-REF-CONSTRUCTOR-P-IMPLIES-CONSP))
 (92 92 (:TYPE-PRESCRIPTION SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P))
 (92 92 (:TYPE-PRESCRIPTION SYNTHETO::TYPE-REF-CONSTRUCTOR-P))
 (88 48 (:REWRITE DEFAULT-+-1))
 (73 28 (:REWRITE DEFAULT-CDR))
 (52 20 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (52 20 (:REWRITE SYNTHETO::CONSP-CDR-IF-TYPE-REF-CONSTRUCTOR-P))
 (52 20 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (50 10 (:REWRITE COMMUTATIVITY-OF-+))
 (40 10 (:DEFINITION INTEGER-ABS))
 (38 2 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (26 2 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (22 22 (:REWRITE DEFAULT-CAR))
 (16 1 (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
 (15 15 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (15 10 (:REWRITE STR::CONSP-OF-EXPLODE))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (13 11 (:REWRITE DEFAULT-<-2))
 (13 11 (:REWRITE DEFAULT-<-1))
 (12 6 (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (12 6 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (12 4 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDDR))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 5 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (10 2 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (10 2 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (8 8 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (5 5 (:TYPE-PRESCRIPTION LEN))
 (5 5 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (5 5 (:REWRITE DEFAULT-REALPART))
 (5 5 (:REWRITE DEFAULT-NUMERATOR))
 (5 5 (:REWRITE DEFAULT-IMAGPART))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (4 4 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 2 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (4 2 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (4 2 (:REWRITE ALISTP-WHEN-PSEUDO-TERM-ALISTP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-TERM-ALISTP))
 (2 2 (:REWRITE ALISTP-WHEN-ATOM))
 )
(SYNTHETO::CONSTRUCT-REQFIX-FUNCTIONS)
(SYNTHETO::CONSTRUCT-REQFIX-FUNCTION-NAMES)
(SYNTHETO::GATHER-FIELD-SYMBOLS)
(SYNTHETO::CONSTRUCT-DEFPROD-FIELDSPEC)
(SYNTHETO::CONSTRUCT-DEFPROD-FIELDSPEC-LIST-RECUR)
(SYNTHETO::CONSTRUCT-DEFPROD-FIELDSPEC-LIST)
(SYNTHETO::FIXVALS-FOR-TYPES)
(SYNTHETO::FIND-FIXVALS-FOR-PRODUCT)
(SYNTHETO::MAKE-PRODUCT-TYPE-MAIN)
(SYNTHETO::PARSE-SYN-FIELDSPECS)
(SYNTHETO::FTY-SUM-PROD-REQUIRE-FUNCTION-NAME)
(SYNTHETO::CONSTRUCT-REQUIRE-FUNCTION)
(SYNTHETO::FTY-FIELDNAMES-TO-S-VAR-REFS)
(SYNTHETO::REQFIX-FUNCTION-NAME-V2)
(SYNTHETO::CONSTRUCT-REQFIX-FUNCTION-V2)
(SYNTHETO::CONSTRUCT-DEFSUM-PROD-FIELDSPEC)
(SYNTHETO::SYN-FIELDSPEC-TO-FTY-FIELDSPEC)
(SYNTHETO::SYN-FIELDSPECS-TO-FTY-FIELDSPECS-RECUR
 (874 8 (:DEFINITION ACL2-COUNT))
 (170 8 (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (170 8 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (164 4 (:DEFINITION RATIONAL-LISTP))
 (164 4 (:DEFINITION INTEGER-LISTP))
 (133 48 (:REWRITE DEFAULT-+-2))
 (130 5 (:DEFINITION LENGTH))
 (115 5 (:DEFINITION LEN))
 (104 8 (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (104 8 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (94 34 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP))
 (94 34 (:REWRITE SYNTHETO::TYPE-REF-CONSTRUCTOR-P-IMPLIES-CONSP))
 (92 92 (:TYPE-PRESCRIPTION SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P))
 (92 92 (:TYPE-PRESCRIPTION SYNTHETO::TYPE-REF-CONSTRUCTOR-P))
 (88 48 (:REWRITE DEFAULT-+-1))
 (73 28 (:REWRITE DEFAULT-CDR))
 (52 20 (:REWRITE SYNTHETO::UNARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (52 20 (:REWRITE SYNTHETO::CONSP-CDR-IF-TYPE-REF-CONSTRUCTOR-P))
 (52 20 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDR))
 (50 10 (:REWRITE COMMUTATIVITY-OF-+))
 (40 10 (:DEFINITION INTEGER-ABS))
 (38 2 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (26 2 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (22 22 (:REWRITE DEFAULT-CAR))
 (16 1 (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
 (15 15 (:TYPE-PRESCRIPTION STR::TRUE-LISTP-OF-EXPLODE))
 (15 10 (:REWRITE STR::CONSP-OF-EXPLODE))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (13 11 (:REWRITE DEFAULT-<-2))
 (13 11 (:REWRITE DEFAULT-<-1))
 (12 6 (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (12 6 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (12 4 (:REWRITE SYNTHETO::BINARY-TYPE-CONSTRUCTOR-P-IMPLIES-CONSP-CDDR))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 5 (:REWRITE STR::COERCE-TO-LIST-REMOVAL))
 (10 2 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (10 2 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (8 8 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (5 5 (:TYPE-PRESCRIPTION LEN))
 (5 5 (:REWRITE STR::EXPLODE-WHEN-NOT-STRINGP))
 (5 5 (:REWRITE DEFAULT-REALPART))
 (5 5 (:REWRITE DEFAULT-NUMERATOR))
 (5 5 (:REWRITE DEFAULT-IMAGPART))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (4 4 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 2 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (4 2 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (4 2 (:REWRITE ALISTP-WHEN-PSEUDO-TERM-ALISTP-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-TERM-ALISTP))
 (2 2 (:REWRITE ALISTP-WHEN-ATOM))
 )
(SYNTHETO::SYN-FIELDSPECS-TO-FTY-FIELDSPECS)
(SYNTHETO::SYN-PRODSPEC-W-INVARIANT-TO-FTY-PRODSPEC)
(SYNTHETO::SYNTHETO-PRODSPEC-TO-DEFTAGSUM-PRODSPEC)
(SYNTHETO::SYNTHETO-PRODSPECS-TO-DEFTAGSUM-PRODSPECS
 (6 3 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (3 3 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
