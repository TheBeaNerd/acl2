(GL::MEASURE-FOR-GEVAL
 (200 96 (:REWRITE DEFAULT-+-2))
 (134 96 (:REWRITE DEFAULT-+-1))
 (100 10 (:DEFINITION LENGTH))
 (80 20 (:REWRITE COMMUTATIVITY-OF-+))
 (80 20 (:DEFINITION INTEGER-ABS))
 (70 10 (:DEFINITION LEN))
 (64 4 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
 (44 4 (:DEFINITION MEMBER-EQUAL))
 (42 42 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (36 12 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (33 33 (:REWRITE DEFAULT-CDR))
 (28 28 (:REWRITE FOLD-CONSTS-IN-+))
 (26 22 (:REWRITE DEFAULT-<-2))
 (24 24 (:TYPE-PRESCRIPTION BOOLEANP))
 (24 22 (:REWRITE DEFAULT-<-1))
 (23 23 (:REWRITE DEFAULT-CAR))
 (20 20 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (10 10 (:REWRITE DEFAULT-REALPART))
 (10 10 (:REWRITE DEFAULT-NUMERATOR))
 (10 10 (:REWRITE DEFAULT-IMAGPART))
 (10 10 (:REWRITE DEFAULT-DENOMINATOR))
 (10 10 (:REWRITE DEFAULT-COERCE-2))
 (10 10 (:REWRITE DEFAULT-COERCE-1))
 (8 8 (:REWRITE GL::TAG-WHEN-ATOM))
 (8 8 (:REWRITE SUBSETP-MEMBER . 2))
 (8 8 (:REWRITE SUBSETP-MEMBER . 1))
 (6 3 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 )
(GL::EQLABLEP-COMPOUND-RECOGNIZER
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(GL::CONSP-ASSOC-EQUAL-OF-CONS
 (87 35 (:REWRITE DEFAULT-CAR))
 (70 70 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (30 15 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (8 8 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (6 6 (:REWRITE DEFAULT-CDR))
 )
(GL::SYMBOL-ALISTP-IMPLIES-EQLABLE-ALISTP)
(GL::GOBJ->TERM)
(GL::GOBJ-IND)
(GL::GOBJ-FLAG
 (268 8 (:DEFINITION ACL2-COUNT))
 (84 40 (:REWRITE DEFAULT-+-2))
 (56 56 (:TYPE-PRESCRIPTION ACL2-COUNT))
 (56 40 (:REWRITE DEFAULT-+-1))
 (40 4 (:DEFINITION LENGTH))
 (32 8 (:REWRITE COMMUTATIVITY-OF-+))
 (32 8 (:DEFINITION INTEGER-ABS))
 (28 4 (:DEFINITION LEN))
 (16 16 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (12 12 (:REWRITE DEFAULT-CDR))
 (12 4 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (4 4 (:TYPE-PRESCRIPTION LEN))
 (4 4 (:REWRITE GL::TAG-WHEN-ATOM))
 (4 4 (:REWRITE DEFAULT-REALPART))
 (4 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE DEFAULT-IMAGPART))
 (4 4 (:REWRITE DEFAULT-DENOMINATOR))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(GL::GOBJ-FLAG-EQUIVALENCES)
(GL::DEF-GEVAL-FN)
(OPEN-HIDE-FOR-DEFAPPLY)
(GL::BASE-GEVAL-APPLY)
(APPLY-FOR-DEFEVALUATOR)
(GL::BASE-GEVAL-EV)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(GL::BASE-GEVAL-EV-OF-FNCALL-ARGS)
(GL::BASE-GEVAL-EV-OF-VARIABLE)
(GL::BASE-GEVAL-EV-OF-QUOTE)
(GL::BASE-GEVAL-EV-OF-LAMBDA)
(GL::BASE-GEVAL-EV-LST-OF-ATOM)
(GL::BASE-GEVAL-EV-LST-OF-CONS)
(GL::BASE-GEVAL-EV-OF-NONSYMBOL-ATOM)
(GL::BASE-GEVAL-EV-OF-BAD-FNCALL)
(GL::BASE-GEVAL-APPLY-AGREES-WITH-BASE-GEVAL-EV)
(GL::BASE-GEVAL-APPLY-AGREES-WITH-BASE-GEVAL-EV-REV)
(GL::BASE-GEVAL-APPLY-OF-FNS)
(GL::BASE-GEVAL-EV-CONCRETE
 (812 56 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (691 36 (:REWRITE PSEUDO-TERMP-CAR))
 (640 15 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (572 572 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (555 237 (:REWRITE DEFAULT-+-2))
 (361 7 (:DEFINITION PSEUDO-TERM-LISTP))
 (313 237 (:REWRITE DEFAULT-+-1))
 (312 52 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (306 56 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (240 40 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (204 3 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
 (160 16 (:DEFINITION LENGTH))
 (156 6 (:REWRITE SUBSETP-CAR-MEMBER))
 (146 73 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (140 67 (:REWRITE PSEUDO-TERMP-OPENER))
 (128 32 (:DEFINITION INTEGER-ABS))
 (120 40 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (114 3 (:DEFINITION MEMBER-EQUAL))
 (113 46 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (104 104 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (104 52 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (102 12 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (101 12 (:DEFINITION SYMBOL-LISTP))
 (99 99 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (98 98 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (80 80 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (60 60 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (53 38 (:REWRITE DEFAULT-<-2))
 (52 52 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (52 52 (:REWRITE SET::IN-SET))
 (42 42 (:TYPE-PRESCRIPTION BOOLEANP))
 (42 38 (:REWRITE DEFAULT-<-1))
 (42 18 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (36 36 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (24 24 (:REWRITE FN-CHECK-DEF-FORMALS))
 (24 18 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (18 18 (:REWRITE SUBSETP-TRANS2))
 (18 18 (:REWRITE SUBSETP-TRANS))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (16 16 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
 (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (6 6 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (5 1 (:DEFINITION GL::BASE-GEVAL-EV-CONCRETE-LST))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(GL::BASE-GEVAL-EV-CONCRETE-LST-OF-KWOTE-LST
 (136 6 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (84 7 (:DEFINITION TRUE-LISTP))
 (78 13 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (28 28 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (26 26 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (26 13 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (26 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 23 (:REWRITE DEFAULT-CDR))
 (14 13 (:REWRITE DEFAULT-CAR))
 (14 7 (:REWRITE DEFAULT-+-2))
 (13 13 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (13 13 (:REWRITE SET::IN-SET))
 (13 5 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(GL::BASE-GEVAL-EVAL-NTH-KWOTE-LST
 (28 28 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (20 19 (:REWRITE DEFAULT-CAR))
 (9 8 (:REWRITE DEFAULT-CDR))
 (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 6 (:REWRITE GL::BASE-GEVAL-EV-OF-LAMBDA))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(GL::NTH-OF-BASE-GEVAL-EV-CONCRETE-LST
 (126 126 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (80 79 (:REWRITE DEFAULT-CDR))
 (73 73 (:REWRITE DEFAULT-+-2))
 (73 73 (:REWRITE DEFAULT-+-1))
 (70 69 (:REWRITE DEFAULT-CAR))
 (48 14 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (28 28 (:TYPE-PRESCRIPTION BOOLEANP))
 (24 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 )
(GL::BASE-GEVAL-EV-CONCRETE-IS-INSTANCE-OF-BASE-GEVAL-EV)
(GL::BASE-GEVAL)
(GL::GET-GUARD-VERIFICATION-THEOREM)
(GL::BASE-GEVAL-GUARDS-OK
 (16 2 (:DEFINITION KWOTE-LST))
 (7 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (7 2 (:REWRITE GL::BASE-GEVAL-EV-OF-QUOTE))
 (7 2 (:REWRITE GL::BASE-GEVAL-EV-OF-LAMBDA))
 (6 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (6 4 (:REWRITE DEFAULT-CAR))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (4 2 (:REWRITE GL::BASE-GEVAL-EV-OF-VARIABLE))
 (2 2 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE CAR-CONS))
 (2 2 (:DEFINITION KWOTE))
 (1 1 (:REWRITE GL::TAG-WHEN-ATOM))
 )
(OPEN-HIDE-FOR-DEFAPPLY)
(GL::GENERIC-GEVAL-APPLY)
(APPLY-FOR-DEFEVALUATOR)
(GL::GENERIC-GEVAL-EV)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(GL::GENERIC-GEVAL-EV-OF-FNCALL-ARGS)
(GL::GENERIC-GEVAL-EV-OF-VARIABLE)
(GL::GENERIC-GEVAL-EV-OF-QUOTE)
(GL::GENERIC-GEVAL-EV-OF-LAMBDA)
(GL::GENERIC-GEVAL-EV-LST-OF-ATOM)
(GL::GENERIC-GEVAL-EV-LST-OF-CONS)
(GL::GENERIC-GEVAL-EV-OF-NONSYMBOL-ATOM)
(GL::GENERIC-GEVAL-EV-OF-BAD-FNCALL)
(GL::GENERIC-GEVAL-EV-OF-CONS-CALL)
(GL::GENERIC-GEVAL-EV-OF-IF-CALL)
(GL::GENERIC-GEVAL-APPLY-AGREES-WITH-GENERIC-GEVAL-EV)
(GL::GENERIC-GEVAL-APPLY-AGREES-WITH-GENERIC-GEVAL-EV-REV)
(GL::GENERIC-GEVAL-APPLY-OF-FNS
 (5 5 (:DEFINITION NTH))
 )
(GL::GENERIC-GEVAL-EV-CONCRETE
 (812 56 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (691 36 (:REWRITE PSEUDO-TERMP-CAR))
 (640 15 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (572 572 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (555 237 (:REWRITE DEFAULT-+-2))
 (361 7 (:DEFINITION PSEUDO-TERM-LISTP))
 (313 237 (:REWRITE DEFAULT-+-1))
 (312 52 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (306 56 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (240 40 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (204 3 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
 (160 16 (:DEFINITION LENGTH))
 (156 6 (:REWRITE SUBSETP-CAR-MEMBER))
 (146 73 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (140 67 (:REWRITE PSEUDO-TERMP-OPENER))
 (128 32 (:DEFINITION INTEGER-ABS))
 (120 40 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (114 3 (:DEFINITION MEMBER-EQUAL))
 (113 46 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (104 104 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (104 52 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (102 12 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (101 12 (:DEFINITION SYMBOL-LISTP))
 (99 99 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (98 98 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (80 80 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (60 60 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (53 38 (:REWRITE DEFAULT-<-2))
 (52 52 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (52 52 (:REWRITE SET::IN-SET))
 (42 42 (:TYPE-PRESCRIPTION BOOLEANP))
 (42 38 (:REWRITE DEFAULT-<-1))
 (42 18 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (36 36 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (24 24 (:REWRITE FN-CHECK-DEF-FORMALS))
 (24 18 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (18 18 (:REWRITE SUBSETP-TRANS2))
 (18 18 (:REWRITE SUBSETP-TRANS))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (16 16 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
 (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (6 6 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (5 1 (:DEFINITION GL::GENERIC-GEVAL-EV-CONCRETE-LST))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(GL::GENERIC-GEVAL-EV-CONCRETE-LST-OF-KWOTE-LST
 (136 6 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (84 7 (:DEFINITION TRUE-LISTP))
 (78 13 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (28 28 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (26 26 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (26 13 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (26 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 23 (:REWRITE DEFAULT-CDR))
 (14 13 (:REWRITE DEFAULT-CAR))
 (14 7 (:REWRITE DEFAULT-+-2))
 (13 13 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (13 13 (:REWRITE SET::IN-SET))
 (13 5 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(GL::GENERIC-GEVAL-EVAL-NTH-KWOTE-LST
 (28 28 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (22 21 (:REWRITE DEFAULT-CAR))
 (9 8 (:REWRITE DEFAULT-CDR))
 (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 6 (:REWRITE GL::GENERIC-GEVAL-EV-OF-LAMBDA))
 (8 6 (:REWRITE GL::GENERIC-GEVAL-EV-OF-IF-CALL))
 (8 6 (:REWRITE GL::GENERIC-GEVAL-EV-OF-CONS-CALL))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(GL::NTH-OF-GENERIC-GEVAL-EV-CONCRETE-LST
 (126 126 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (80 79 (:REWRITE DEFAULT-CDR))
 (73 73 (:REWRITE DEFAULT-+-2))
 (73 73 (:REWRITE DEFAULT-+-1))
 (70 69 (:REWRITE DEFAULT-CAR))
 (48 14 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (28 28 (:TYPE-PRESCRIPTION BOOLEANP))
 (24 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 )
(GL::GENERIC-GEVAL-EV-CONCRETE-IS-INSTANCE-OF-GENERIC-GEVAL-EV)
(GL::GENERIC-GEVAL)
(GL::GENERIC-GEVAL
 (492 285 (:REWRITE DEFAULT-CAR))
 (474 174 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (408 408 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (360 15 (:DEFINITION GL::BFR-LIST->S))
 (300 300 (:TYPE-PRESCRIPTION BOOLEANP))
 (259 132 (:REWRITE DEFAULT-CDR))
 (255 15 (:DEFINITION HONS-ASSOC-EQUAL))
 (193 31 (:REWRITE GL::GENERIC-GEVAL-EV-OF-IF-CALL))
 (180 23 (:DEFINITION KWOTE-LST))
 (180 15 (:DEFINITION LOGCONS$INLINE))
 (178 31 (:REWRITE GL::GENERIC-GEVAL-EV-OF-BAD-FNCALL))
 (153 31 (:REWRITE GL::GENERIC-GEVAL-EV-OF-CONS-CALL))
 (99 99 (:REWRITE CAR-CONS))
 (92 92 (:REWRITE GL::TAG-WHEN-ATOM))
 (90 15 (:DEFINITION GL::FIRST/REST/END))
 (75 30 (:REWRITE GL::BFR-LIST->S-WHEN-S-ENDP))
 (62 31 (:REWRITE GL::GENERIC-GEVAL-EV-OF-NONSYMBOL-ATOM))
 (60 15 (:DEFINITION HONS-EQUAL))
 (56 28 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (50 25 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 (45 45 (:TYPE-PRESCRIPTION GL::S-ENDP$INLINE))
 (30 30 (:TYPE-PRESCRIPTION BOOL->BIT$INLINE))
 (30 15 (:REWRITE GL::SCDR-WHEN-S-ENDP))
 (30 15 (:REWRITE DEFAULT-+-2))
 (30 15 (:REWRITE DEFAULT-+-1))
 (30 15 (:REWRITE DEFAULT-*-2))
 (30 15 (:REWRITE BFIX-BITP))
 (30 15 (:DEFINITION IFIX))
 (30 15 (:DEFINITION GL::BOOL->SIGN))
 (28 2 (:DEFINITION ASSOC-EQUAL))
 (26 2 (:DEFINITION PAIRLIS$))
 (23 23 (:DEFINITION KWOTE))
 (22 22 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (15 15 (:TYPE-PRESCRIPTION GL::TRUE-LISTP-OF-SCDR))
 (15 15 (:REWRITE DEFAULT-*-1))
 (12 6 (:REWRITE GL::GENERIC-GEVAL-EV-LST-OF-ATOM))
 )
(GL::FLAG-LEMMA-FOR-GENERIC-GEVAL-IS-GENERIC-GEVAL-EV-OF-GOBJ->TERM
 (687 239 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (576 24 (:DEFINITION GL::BFR-LIST->S))
 (517 314 (:REWRITE DEFAULT-CAR))
 (448 448 (:TYPE-PRESCRIPTION BOOLEANP))
 (442 442 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (408 24 (:DEFINITION HONS-ASSOC-EQUAL))
 (336 166 (:REWRITE DEFAULT-CDR))
 (288 24 (:DEFINITION LOGCONS$INLINE))
 (210 210 (:TYPE-PRESCRIPTION GL::GOBJ->TERM))
 (200 200 (:REWRITE GL::TAG-WHEN-ATOM))
 (183 183 (:TYPE-PRESCRIPTION KWOTE-LST))
 (153 34 (:REWRITE GL::GENERIC-GEVAL-EV-OF-LAMBDA))
 (144 24 (:DEFINITION GL::FIRST/REST/END))
 (120 48 (:REWRITE GL::BFR-LIST->S-WHEN-S-ENDP))
 (112 14 (:DEFINITION KWOTE-LST))
 (96 24 (:DEFINITION HONS-EQUAL))
 (72 72 (:TYPE-PRESCRIPTION GL::S-ENDP$INLINE))
 (72 72 (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
 (72 72 (:TYPE-PRESCRIPTION GL::BFR-LIST->S))
 (60 30 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (48 48 (:TYPE-PRESCRIPTION BOOL->BIT$INLINE))
 (48 24 (:REWRITE GL::SCDR-WHEN-S-ENDP))
 (48 24 (:REWRITE DEFAULT-+-2))
 (48 24 (:REWRITE DEFAULT-+-1))
 (48 24 (:REWRITE DEFAULT-*-2))
 (48 24 (:REWRITE BFIX-BITP))
 (48 24 (:DEFINITION IFIX))
 (48 24 (:DEFINITION GL::BOOL->SIGN))
 (28 28 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (24 24 (:TYPE-PRESCRIPTION GL::TRUE-LISTP-OF-SCDR))
 (24 24 (:TYPE-PRESCRIPTION BFR-EVAL))
 (24 24 (:REWRITE DEFAULT-*-1))
 )
(GL::GENERIC-GEVAL-IS-GENERIC-GEVAL-EV-OF-GOBJ->TERM)
(GL::GENERIC-GEVAL-LIST-IS-GENERIC-GEVAL-EV-LST-OF-GOBJ-LIST->TERMS)
(OPEN-HIDE-FOR-DEFAPPLY)
(GL::IMPLIES-GEVAL-APPLY)
(APPLY-FOR-DEFEVALUATOR)
(GL::IMPLIES-GEVAL-EV)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(GL::IMPLIES-GEVAL-EV-OF-FNCALL-ARGS)
(GL::IMPLIES-GEVAL-EV-OF-VARIABLE)
(GL::IMPLIES-GEVAL-EV-OF-QUOTE)
(GL::IMPLIES-GEVAL-EV-OF-LAMBDA)
(GL::IMPLIES-GEVAL-EV-LST-OF-ATOM)
(GL::IMPLIES-GEVAL-EV-LST-OF-CONS)
(GL::IMPLIES-GEVAL-EV-OF-NONSYMBOL-ATOM)
(GL::IMPLIES-GEVAL-EV-OF-BAD-FNCALL)
(GL::IMPLIES-GEVAL-EV-OF-IMPLIES-CALL)
(GL::IMPLIES-GEVAL-APPLY-AGREES-WITH-IMPLIES-GEVAL-EV)
(GL::IMPLIES-GEVAL-APPLY-AGREES-WITH-IMPLIES-GEVAL-EV-REV)
(GL::IMPLIES-GEVAL-APPLY-OF-FNS
 (2 2 (:DEFINITION NTH))
 )
(GL::IMPLIES-GEVAL-EV-CONCRETE
 (812 56 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (691 36 (:REWRITE PSEUDO-TERMP-CAR))
 (640 15 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (572 572 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (555 237 (:REWRITE DEFAULT-+-2))
 (361 7 (:DEFINITION PSEUDO-TERM-LISTP))
 (313 237 (:REWRITE DEFAULT-+-1))
 (312 52 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (306 56 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (240 40 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (204 3 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
 (160 16 (:DEFINITION LENGTH))
 (156 6 (:REWRITE SUBSETP-CAR-MEMBER))
 (146 73 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (140 67 (:REWRITE PSEUDO-TERMP-OPENER))
 (128 32 (:DEFINITION INTEGER-ABS))
 (120 40 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (114 3 (:DEFINITION MEMBER-EQUAL))
 (113 46 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (104 104 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (104 52 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (102 12 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (101 12 (:DEFINITION SYMBOL-LISTP))
 (99 99 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (98 98 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (80 80 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (60 60 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (53 38 (:REWRITE DEFAULT-<-2))
 (52 52 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (52 52 (:REWRITE SET::IN-SET))
 (42 42 (:TYPE-PRESCRIPTION BOOLEANP))
 (42 38 (:REWRITE DEFAULT-<-1))
 (42 18 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (36 36 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (24 24 (:REWRITE FN-CHECK-DEF-FORMALS))
 (24 18 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (18 18 (:REWRITE SUBSETP-TRANS2))
 (18 18 (:REWRITE SUBSETP-TRANS))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (16 16 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
 (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (6 6 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (5 1 (:DEFINITION GL::IMPLIES-GEVAL-EV-CONCRETE-LST))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(GL::IMPLIES-GEVAL-EV-CONCRETE-LST-OF-KWOTE-LST
 (136 6 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (84 7 (:DEFINITION TRUE-LISTP))
 (78 13 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (28 28 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (26 26 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (26 13 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (26 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 23 (:REWRITE DEFAULT-CDR))
 (14 13 (:REWRITE DEFAULT-CAR))
 (14 7 (:REWRITE DEFAULT-+-2))
 (13 13 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (13 13 (:REWRITE SET::IN-SET))
 (13 5 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(GL::IMPLIES-GEVAL-EVAL-NTH-KWOTE-LST
 (28 28 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (21 20 (:REWRITE DEFAULT-CAR))
 (9 8 (:REWRITE DEFAULT-CDR))
 (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 6 (:REWRITE GL::IMPLIES-GEVAL-EV-OF-LAMBDA))
 (8 6 (:REWRITE GL::IMPLIES-GEVAL-EV-OF-IMPLIES-CALL))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(GL::NTH-OF-IMPLIES-GEVAL-EV-CONCRETE-LST
 (126 126 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (80 79 (:REWRITE DEFAULT-CDR))
 (73 73 (:REWRITE DEFAULT-+-2))
 (73 73 (:REWRITE DEFAULT-+-1))
 (70 69 (:REWRITE DEFAULT-CAR))
 (48 14 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (28 28 (:TYPE-PRESCRIPTION BOOLEANP))
 (24 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 )
(GL::IMPLIES-GEVAL-EV-CONCRETE-IS-INSTANCE-OF-IMPLIES-GEVAL-EV)
(GL::IMPLIES-GEVAL)
(GL::IMPLIES-GEVAL
 (453 153 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (451 264 (:REWRITE DEFAULT-CAR))
 (408 408 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (360 15 (:DEFINITION GL::BFR-LIST->S))
 (300 300 (:TYPE-PRESCRIPTION BOOLEANP))
 (259 132 (:REWRITE DEFAULT-CDR))
 (255 15 (:DEFINITION HONS-ASSOC-EQUAL))
 (193 31 (:REWRITE GL::IMPLIES-GEVAL-EV-OF-IMPLIES-CALL))
 (180 23 (:DEFINITION KWOTE-LST))
 (180 15 (:DEFINITION LOGCONS$INLINE))
 (178 31 (:REWRITE GL::IMPLIES-GEVAL-EV-OF-BAD-FNCALL))
 (92 92 (:REWRITE GL::TAG-WHEN-ATOM))
 (90 15 (:DEFINITION GL::FIRST/REST/END))
 (79 79 (:REWRITE CAR-CONS))
 (75 30 (:REWRITE GL::BFR-LIST->S-WHEN-S-ENDP))
 (62 31 (:REWRITE GL::IMPLIES-GEVAL-EV-OF-NONSYMBOL-ATOM))
 (60 15 (:DEFINITION HONS-EQUAL))
 (56 28 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (50 25 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 (45 45 (:TYPE-PRESCRIPTION GL::S-ENDP$INLINE))
 (30 30 (:TYPE-PRESCRIPTION BOOL->BIT$INLINE))
 (30 15 (:REWRITE GL::SCDR-WHEN-S-ENDP))
 (30 15 (:REWRITE DEFAULT-+-2))
 (30 15 (:REWRITE DEFAULT-+-1))
 (30 15 (:REWRITE DEFAULT-*-2))
 (30 15 (:REWRITE BFIX-BITP))
 (30 15 (:DEFINITION IFIX))
 (30 15 (:DEFINITION GL::BOOL->SIGN))
 (28 2 (:DEFINITION ASSOC-EQUAL))
 (26 2 (:DEFINITION PAIRLIS$))
 (23 23 (:DEFINITION KWOTE))
 (22 22 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (15 15 (:TYPE-PRESCRIPTION GL::TRUE-LISTP-OF-SCDR))
 (15 15 (:REWRITE DEFAULT-*-1))
 (12 6 (:REWRITE GL::IMPLIES-GEVAL-EV-LST-OF-ATOM))
 )
(OPEN-HIDE-FOR-DEFAPPLY)
(GL::LITTLE-GEVAL-APPLY)
(APPLY-FOR-DEFEVALUATOR)
(GL::LITTLE-GEVAL-EV)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(GL::LITTLE-GEVAL-EV-OF-FNCALL-ARGS)
(GL::LITTLE-GEVAL-EV-OF-VARIABLE)
(GL::LITTLE-GEVAL-EV-OF-QUOTE)
(GL::LITTLE-GEVAL-EV-OF-LAMBDA)
(GL::LITTLE-GEVAL-EV-LST-OF-ATOM)
(GL::LITTLE-GEVAL-EV-LST-OF-CONS)
(GL::LITTLE-GEVAL-EV-OF-NONSYMBOL-ATOM)
(GL::LITTLE-GEVAL-EV-OF-BAD-FNCALL)
(GL::LITTLE-GEVAL-EV-OF-BINARY-*-CALL)
(GL::LITTLE-GEVAL-EV-OF-IF-CALL)
(GL::LITTLE-GEVAL-EV-OF-CONS-CALL)
(GL::LITTLE-GEVAL-EV-OF-BINARY-+-CALL)
(GL::LITTLE-GEVAL-EV-OF-PKG-WITNESS-CALL)
(GL::LITTLE-GEVAL-EV-OF-UNARY---CALL)
(GL::LITTLE-GEVAL-EV-OF-COMPLEX-RATIONALP-CALL)
(GL::LITTLE-GEVAL-EV-OF-ACL2-NUMBERP-CALL)
(GL::LITTLE-GEVAL-EV-OF-SYMBOL-PACKAGE-NAME-CALL)
(GL::LITTLE-GEVAL-EV-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL)
(GL::LITTLE-GEVAL-EV-OF-CODE-CHAR-CALL)
(GL::LITTLE-GEVAL-EV-OF-CDR-CALL)
(GL::LITTLE-GEVAL-EV-OF-CAR-CALL)
(GL::LITTLE-GEVAL-EV-OF-CONSP-CALL)
(GL::LITTLE-GEVAL-EV-OF-SYMBOL-NAME-CALL)
(GL::LITTLE-GEVAL-EV-OF-CHAR-CODE-CALL)
(GL::LITTLE-GEVAL-EV-OF-IMAGPART-CALL)
(GL::LITTLE-GEVAL-EV-OF-SYMBOLP-CALL)
(GL::LITTLE-GEVAL-EV-OF-REALPART-CALL)
(GL::LITTLE-GEVAL-EV-OF-EQUAL-CALL)
(GL::LITTLE-GEVAL-EV-OF-STRINGP-CALL)
(GL::LITTLE-GEVAL-EV-OF-RATIONALP-CALL)
(GL::LITTLE-GEVAL-EV-OF-INTEGERP-CALL)
(GL::LITTLE-GEVAL-EV-OF-CHARACTERP-CALL)
(GL::LITTLE-GEVAL-EV-OF-<-CALL)
(GL::LITTLE-GEVAL-EV-OF-COERCE-CALL)
(GL::LITTLE-GEVAL-EV-OF-BOOLEANP-CALL)
(GL::LITTLE-GEVAL-EV-OF-LOGBITP-CALL)
(GL::LITTLE-GEVAL-EV-OF-BINARY-LOGAND-CALL)
(GL::LITTLE-GEVAL-EV-OF-BINARY-LOGIOR-CALL)
(GL::LITTLE-GEVAL-EV-OF-LOGNOT-CALL)
(GL::LITTLE-GEVAL-EV-OF-ASH-CALL)
(GL::LITTLE-GEVAL-EV-OF-INTEGER-LENGTH-CALL)
(GL::LITTLE-GEVAL-EV-OF-FLOOR-CALL)
(GL::LITTLE-GEVAL-EV-OF-MOD-CALL)
(GL::LITTLE-GEVAL-EV-OF-TRUNCATE-CALL)
(GL::LITTLE-GEVAL-EV-OF-REM-CALL)
(GL::LITTLE-GEVAL-EV-OF-NOT-CALL)
(GL::LITTLE-GEVAL-EV-OF-IMPLIES-CALL)
(GL::LITTLE-GEVAL-EV-OF-EQ-CALL)
(GL::LITTLE-GEVAL-EV-OF-ATOM-CALL)
(GL::LITTLE-GEVAL-EV-OF-EQL-CALL)
(GL::LITTLE-GEVAL-EV-OF-=-CALL)
(GL::LITTLE-GEVAL-EV-OF-/=-CALL)
(GL::LITTLE-GEVAL-EV-OF-NULL-CALL)
(GL::LITTLE-GEVAL-EV-OF-ENDP-CALL)
(GL::LITTLE-GEVAL-EV-OF-ZEROP-CALL)
(GL::LITTLE-GEVAL-EV-OF-PLUSP-CALL)
(GL::LITTLE-GEVAL-EV-OF-MINUSP-CALL)
(GL::LITTLE-GEVAL-EV-OF-LISTP-CALL)
(GL::LITTLE-GEVAL-APPLY-AGREES-WITH-LITTLE-GEVAL-EV)
(GL::LITTLE-GEVAL-APPLY-AGREES-WITH-LITTLE-GEVAL-EV-REV)
(GL::LITTLE-GEVAL-APPLY-OF-FNS
 (72 72 (:DEFINITION NTH))
 )
(GL::LITTLE-GEVAL-EV-CONCRETE
 (812 56 (:REWRITE PSEUDO-TERM-LISTP-CDR))
 (691 36 (:REWRITE PSEUDO-TERMP-CAR))
 (640 15 (:REWRITE PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP))
 (572 572 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (555 237 (:REWRITE DEFAULT-+-2))
 (361 7 (:DEFINITION PSEUDO-TERM-LISTP))
 (313 237 (:REWRITE DEFAULT-+-1))
 (312 52 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (306 56 (:REWRITE PSEUDO-TERMP-LIST-CDR))
 (240 40 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (204 3 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
 (160 16 (:DEFINITION LENGTH))
 (156 6 (:REWRITE SUBSETP-CAR-MEMBER))
 (146 73 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (140 67 (:REWRITE PSEUDO-TERMP-OPENER))
 (128 32 (:DEFINITION INTEGER-ABS))
 (120 40 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (114 3 (:DEFINITION MEMBER-EQUAL))
 (113 46 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (104 104 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (104 52 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (102 12 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (101 12 (:DEFINITION SYMBOL-LISTP))
 (99 99 (:REWRITE PSEUDO-TERM-LISTP-OF-ATOM))
 (98 98 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (80 80 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (60 60 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (53 38 (:REWRITE DEFAULT-<-2))
 (52 52 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (52 52 (:REWRITE SET::IN-SET))
 (42 42 (:TYPE-PRESCRIPTION BOOLEANP))
 (42 38 (:REWRITE DEFAULT-<-1))
 (42 18 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (36 36 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (24 24 (:REWRITE FN-CHECK-DEF-FORMALS))
 (24 18 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (18 18 (:REWRITE SUBSETP-TRANS2))
 (18 18 (:REWRITE SUBSETP-TRANS))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (16 16 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
 (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (6 6 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (5 1 (:DEFINITION GL::LITTLE-GEVAL-EV-CONCRETE-LST))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(GL::LITTLE-GEVAL-EV-CONCRETE-LST-OF-KWOTE-LST
 (136 6 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (84 7 (:DEFINITION TRUE-LISTP))
 (78 13 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (46 46 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (28 28 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (26 26 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (26 13 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (26 7 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (24 23 (:REWRITE DEFAULT-CDR))
 (14 13 (:REWRITE DEFAULT-CAR))
 (14 7 (:REWRITE DEFAULT-+-2))
 (13 13 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (13 13 (:REWRITE SET::IN-SET))
 (13 5 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(GL::LITTLE-GEVAL-EVAL-NTH-KWOTE-LST
 (70 69 (:REWRITE DEFAULT-CAR))
 (28 28 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (9 8 (:REWRITE DEFAULT-CDR))
 (9 3 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-ZEROP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-UNARY---CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-TRUNCATE-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-SYMBOLP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-SYMBOL-PACKAGE-NAME-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-SYMBOL-NAME-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-STRINGP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-REM-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-REALPART-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-RATIONALP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-PLUSP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-PKG-WITNESS-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-NULL-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-NOT-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-MOD-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-MINUSP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-LOGNOT-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-LOGBITP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-LISTP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-LAMBDA))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-INTEGERP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-INTEGER-LENGTH-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-IMPLIES-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-IMAGPART-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-IF-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-FLOOR-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-EQUAL-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-EQL-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-EQ-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-ENDP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CONSP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CONS-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-COMPLEX-RATIONALP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-COERCE-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CODE-CHAR-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CHARACTERP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CHAR-CODE-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CDR-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CAR-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BOOLEANP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BINARY-LOGIOR-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BINARY-LOGAND-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BINARY-+-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BINARY-*-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-ATOM-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-ASH-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-ACL2-NUMBERP-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-=-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-<-CALL))
 (8 6 (:REWRITE GL::LITTLE-GEVAL-EV-OF-/=-CALL))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:REWRITE ZP-OPEN))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(GL::NTH-OF-LITTLE-GEVAL-EV-CONCRETE-LST
 (126 126 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (80 79 (:REWRITE DEFAULT-CDR))
 (73 73 (:REWRITE DEFAULT-+-2))
 (73 73 (:REWRITE DEFAULT-+-1))
 (70 69 (:REWRITE DEFAULT-CAR))
 (48 14 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (28 28 (:TYPE-PRESCRIPTION BOOLEANP))
 (24 24 (:REWRITE DEFAULT-<-2))
 (24 24 (:REWRITE DEFAULT-<-1))
 )
(GL::LITTLE-GEVAL-EV-CONCRETE-IS-INSTANCE-OF-LITTLE-GEVAL-EV)
(GL::LITTLE-GEVAL)
(GL::LITTLE-GEVAL
 (2460 1293 (:REWRITE DEFAULT-CAR))
 (1482 1182 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (1059 1059 (:REWRITE CAR-CONS))
 (408 408 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (360 15 (:DEFINITION GL::BFR-LIST->S))
 (300 300 (:TYPE-PRESCRIPTION BOOLEANP))
 (259 132 (:REWRITE DEFAULT-CDR))
 (255 15 (:DEFINITION HONS-ASSOC-EQUAL))
 (193 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-LISTP-CALL))
 (180 23 (:DEFINITION KWOTE-LST))
 (180 15 (:DEFINITION LOGCONS$INLINE))
 (178 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BAD-FNCALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-ZEROP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-UNARY---CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-TRUNCATE-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-SYMBOLP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-SYMBOL-PACKAGE-NAME-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-SYMBOL-NAME-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-STRINGP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-REM-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-REALPART-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-RATIONALP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-PLUSP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-PKG-WITNESS-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-NULL-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-NOT-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-MOD-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-MINUSP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-LOGNOT-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-LOGBITP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-INTEGERP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-INTEGER-LENGTH-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-IMPLIES-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-IMAGPART-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-IF-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-FLOOR-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-EQUAL-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-EQL-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-EQ-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-ENDP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CONSP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CONS-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-COMPLEX-RATIONALP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-COERCE-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CODE-CHAR-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CHARACTERP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CHAR-CODE-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CDR-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-CAR-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BOOLEANP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BINARY-LOGIOR-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BINARY-LOGAND-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BINARY-+-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-BINARY-*-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-ATOM-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-ASH-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-ACL2-NUMBERP-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-=-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-<-CALL))
 (153 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-/=-CALL))
 (92 92 (:REWRITE GL::TAG-WHEN-ATOM))
 (90 15 (:DEFINITION GL::FIRST/REST/END))
 (75 30 (:REWRITE GL::BFR-LIST->S-WHEN-S-ENDP))
 (62 31 (:REWRITE GL::LITTLE-GEVAL-EV-OF-NONSYMBOL-ATOM))
 (60 15 (:DEFINITION HONS-EQUAL))
 (56 28 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (50 25 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 (45 45 (:TYPE-PRESCRIPTION GL::S-ENDP$INLINE))
 (30 30 (:TYPE-PRESCRIPTION BOOL->BIT$INLINE))
 (30 15 (:REWRITE GL::SCDR-WHEN-S-ENDP))
 (30 15 (:REWRITE DEFAULT-+-2))
 (30 15 (:REWRITE DEFAULT-+-1))
 (30 15 (:REWRITE DEFAULT-*-2))
 (30 15 (:REWRITE BFIX-BITP))
 (30 15 (:DEFINITION IFIX))
 (30 15 (:DEFINITION GL::BOOL->SIGN))
 (28 2 (:DEFINITION ASSOC-EQUAL))
 (26 2 (:DEFINITION PAIRLIS$))
 (23 23 (:DEFINITION KWOTE))
 (22 22 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (15 15 (:TYPE-PRESCRIPTION GL::TRUE-LISTP-OF-SCDR))
 (15 15 (:REWRITE DEFAULT-*-1))
 (12 6 (:REWRITE GL::LITTLE-GEVAL-EV-LST-OF-ATOM))
 )
