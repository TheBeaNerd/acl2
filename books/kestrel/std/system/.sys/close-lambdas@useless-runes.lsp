(CLOSE-LAMBDAS
 (492 205 (:REWRITE DEFAULT-+-2))
 (288 205 (:REWRITE DEFAULT-+-1))
 (165 3 (:REWRITE ACL2-COUNT-WHEN-MEMBER))
 (144 36 (:DEFINITION INTEGER-ABS))
 (144 18 (:DEFINITION LENGTH))
 (126 6 (:REWRITE SUBSETP-CAR-MEMBER))
 (90 18 (:DEFINITION LEN))
 (87 3 (:DEFINITION MEMBER-EQUAL))
 (84 12 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (60 43 (:REWRITE DEFAULT-<-2))
 (47 43 (:REWRITE DEFAULT-<-1))
 (36 36 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (36 36 (:REWRITE DEFAULT-UNARY-MINUS))
 (20 20 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (18 18 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (18 18 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (18 18 (:REWRITE SUBSETP-TRANS2))
 (18 18 (:REWRITE SUBSETP-TRANS))
 (18 18 (:REWRITE DEFAULT-REALPART))
 (18 18 (:REWRITE DEFAULT-NUMERATOR))
 (18 18 (:REWRITE DEFAULT-IMAGPART))
 (18 18 (:REWRITE DEFAULT-DENOMINATOR))
 (18 18 (:REWRITE DEFAULT-COERCE-2))
 (18 18 (:REWRITE DEFAULT-COERCE-1))
 (18 3 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (15 15 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8 8 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LISTP))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE SUBSETP-MEMBER . 2))
 (6 6 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (1 1 (:TYPE-PRESCRIPTION CLOSE-LAMBDAS))
 )
(CLOSE-LAMBDAS-FLAG
 (692 301 (:REWRITE DEFAULT-+-2))
 (422 301 (:REWRITE DEFAULT-+-1))
 (224 56 (:DEFINITION INTEGER-ABS))
 (224 28 (:DEFINITION LENGTH))
 (140 28 (:DEFINITION LEN))
 (105 6 (:DEFINITION MEMBER-EQUAL))
 (92 68 (:REWRITE DEFAULT-<-2))
 (84 12 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (77 68 (:REWRITE DEFAULT-<-1))
 (56 56 (:REWRITE DEFAULT-UNARY-MINUS))
 (28 28 (:TYPE-PRESCRIPTION LEN))
 (28 28 (:REWRITE DEFAULT-REALPART))
 (28 28 (:REWRITE DEFAULT-NUMERATOR))
 (28 28 (:REWRITE DEFAULT-IMAGPART))
 (28 28 (:REWRITE DEFAULT-DENOMINATOR))
 (28 28 (:REWRITE DEFAULT-COERCE-2))
 (28 28 (:REWRITE DEFAULT-COERCE-1))
 (28 28 (:LINEAR ACL2-COUNT-WHEN-MEMBER))
 (24 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (19 19 (:REWRITE SUBSETP-TRANS2))
 (19 19 (:REWRITE SUBSETP-TRANS))
 (18 18 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (18 18 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (18 3 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (12 12 (:REWRITE SUBSETP-MEMBER . 2))
 (12 12 (:REWRITE SUBSETP-MEMBER . 1))
 (8 8 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LISTP))
 (6 6 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (3 3 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE MEMBER-SELF))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(CLOSE-LAMBDAS-FLAG-EQUIVALENCES)
(FLAG-LEMMA-FOR-RETURN-TYPE-OF-CLOSE-LAMBDAS.NEW-TERM
 (6555 41 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP))
 (4518 846 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (4137 184 (:DEFINITION MEMBER-EQUAL))
 (3908 135 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP))
 (2378 293 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (1693 1535 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (1648 1535 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (1586 1546 (:REWRITE SUBSETP-TRANS2))
 (1569 176 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE))
 (1546 1546 (:REWRITE SUBSETP-TRANS))
 (1266 176 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (1243 1202 (:REWRITE DEFAULT-CDR))
 (1197 1160 (:REWRITE DEFAULT-CAR))
 (791 678 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (782 126 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LISTP))
 (586 45 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (409 373 (:REWRITE SUBSETP-MEMBER . 1))
 (386 193 (:REWRITE DEFAULT-+-2))
 (373 373 (:REWRITE SUBSETP-MEMBER . 2))
 (352 352 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (352 176 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (258 258 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (195 193 (:REWRITE DEFAULT-+-1))
 (176 176 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (176 176 (:REWRITE SET::IN-SET))
 (160 1 (:REWRITE MEMBER-OF-APPEND))
 (141 1 (:REWRITE MEMBER-OF-SET-DIFFERENCE-EQUAL))
 (126 7 (:REWRITE SUBSETP-APPEND1))
 (123 3 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (81 81 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (63 2 (:REWRITE SUBSETP-OF-CONS))
 (51 13 (:REWRITE SUBSETP-MEMBER . 3))
 (39 3 (:DEFINITION ALL-VARS1))
 (24 3 (:DEFINITION ADD-TO-SET-EQUAL))
 (16 4 (:DEFINITION BINARY-APPEND))
 (13 13 (:REWRITE SUBSETP-MEMBER . 4))
 (13 13 (:REWRITE MEMBER-WHEN-ATOM))
 (13 13 (:REWRITE INTERSECTP-MEMBER . 3))
 (13 13 (:REWRITE INTERSECTP-MEMBER . 2))
 (13 1 (:REWRITE SYMBOL-LISTP-OF-CONS))
 (10 8 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (4 1 (:REWRITE CONSP-OF-APPEND))
 )
(RETURN-TYPE-OF-CLOSE-LAMBDAS.NEW-TERM)
(RETURN-TYPE-OF-CLOSE-LAMBDAS-LST.NEW-TERMS)
(CLOSE-LAMBDAS
 (464 37 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP))
 (407 4 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP))
 (325 226 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (315 20 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP))
 (313 44 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE))
 (259 44 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (256 53 (:REWRITE SYMBOL-LISTP-OF-CDR-WHEN-SYMBOL-LISTP))
 (135 27 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (125 125 (:REWRITE DEFAULT-CDR))
 (119 113 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (117 117 (:REWRITE DEFAULT-CAR))
 (104 4 (:DEFINITION MEMBER-EQUAL))
 (88 1 (:DEFINITION CLOSE-LAMBDAS))
 (86 86 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (86 43 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (64 9 (:REWRITE SYMBOLP-OF-CAR-WHEN-SYMBOL-LISTP))
 (45 45 (:REWRITE SUBSETP-TRANS2))
 (45 45 (:REWRITE SUBSETP-TRANS))
 (44 44 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (44 44 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (43 43 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (43 43 (:REWRITE SET::IN-SET))
 (41 1 (:DEFINITION SET-DIFFERENCE-EQUAL))
 (36 36 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (36 36 (:REWRITE PSEUDO-TERM-LISTP-WHEN-NOT-CONSP))
 (28 28 (:TYPE-PRESCRIPTION CLOSE-LAMBDAS))
 (28 14 (:REWRITE DEFAULT-+-2))
 (26 2 (:DEFINITION ALL-VARS1))
 (18 18 (:REWRITE SYMBOLP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LISTP))
 (16 2 (:DEFINITION ADD-TO-SET-EQUAL))
 (14 14 (:REWRITE DEFAULT-+-1))
 (12 12 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (10 10 (:REWRITE SUBSETP-MEMBER . 2))
 (10 10 (:REWRITE SUBSETP-MEMBER . 1))
 (10 2 (:DEFINITION BINARY-APPEND))
 (7 4 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (4 4 (:REWRITE SUBSETP-MEMBER . 4))
 (4 4 (:REWRITE SUBSETP-MEMBER . 3))
 (4 4 (:REWRITE MEMBER-WHEN-ATOM))
 (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
 (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
 (3 1 (:DEFINITION CLOSE-LAMBDAS-LST))
 )
