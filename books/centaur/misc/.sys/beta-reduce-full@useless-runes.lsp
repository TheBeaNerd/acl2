(APPLY-FOR-DEFEVALUATOR)
(BETA-EVAL)
(EVAL-LIST-KWOTE-LST)
(TRUE-LIST-FIX-EV-LST)
(EV-COMMUTES-CAR)
(EV-LST-COMMUTES-CDR)
(BETA-EVAL-CONSTRAINT-0)
(BETA-EVAL-CONSTRAINT-1)
(BETA-EVAL-CONSTRAINT-2)
(BETA-EVAL-CONSTRAINT-3)
(BETA-EVAL-CONSTRAINT-4)
(BETA-EVAL-CONSTRAINT-5)
(BETA-EVAL-CONSTRAINT-6)
(BETA-EVAL-CONSTRAINT-7)
(BETA-REDUCE-FULL-REC
 (455 187 (:REWRITE DEFAULT-+-2))
 (263 187 (:REWRITE DEFAULT-+-1))
 (128 32 (:DEFINITION INTEGER-ABS))
 (128 16 (:DEFINITION LENGTH))
 (80 16 (:DEFINITION LEN))
 (53 38 (:REWRITE DEFAULT-<-2))
 (42 38 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(BETA-REDUCE-FLG
 (455 187 (:REWRITE DEFAULT-+-2))
 (263 187 (:REWRITE DEFAULT-+-1))
 (128 32 (:DEFINITION INTEGER-ABS))
 (128 16 (:DEFINITION LENGTH))
 (80 16 (:DEFINITION LEN))
 (53 38 (:REWRITE DEFAULT-<-2))
 (42 38 (:REWRITE DEFAULT-<-1))
 (32 32 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (16 16 (:REWRITE DEFAULT-REALPART))
 (16 16 (:REWRITE DEFAULT-NUMERATOR))
 (16 16 (:REWRITE DEFAULT-IMAGPART))
 (16 16 (:REWRITE DEFAULT-DENOMINATOR))
 (16 16 (:REWRITE DEFAULT-COERCE-2))
 (16 16 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (4 2 (:TYPE-PRESCRIPTION RETURN-LAST))
 (2 2 (:TYPE-PRESCRIPTION THROW-NONEXEC-ERROR))
 )
(FLAG::FLAG-EQUIV-LEMMA)
(BETA-REDUCE-FLG-EQUIVALENCES)
(LEN-OF-BETA-REDUCE-FULL-REC-LIST
 (49 45 (:REWRITE DEFAULT-CDR))
 (48 24 (:REWRITE DEFAULT-+-2))
 (26 1 (:DEFINITION BETA-REDUCE-FULL-REC))
 (24 24 (:REWRITE DEFAULT-+-1))
 (23 20 (:REWRITE DEFAULT-CAR))
 (11 1 (:DEFINITION PAIRLIS$))
 (5 1 (:DEFINITION ASSOC-EQUAL))
 )
(TRUE-LISTP-OF-BETA-REDUCE-FULL-REC-LIST)
(SYMBOL-ALISTP-PAIRLIS
 (24 22 (:REWRITE DEFAULT-CAR))
 (11 10 (:REWRITE DEFAULT-CDR))
 )
(BETA-REDUCE-FULL-REC
 (324 309 (:REWRITE DEFAULT-CAR))
 (296 281 (:REWRITE DEFAULT-CDR))
 (142 71 (:REWRITE DEFAULT-+-2))
 (108 20 (:DEFINITION SYMBOL-ALISTP))
 (71 71 (:REWRITE DEFAULT-+-1))
 (69 19 (:DEFINITION SYMBOL-LISTP))
 (55 5 (:DEFINITION PAIRLIS$))
 (34 34 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (24 24 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (15 5 (:DEFINITION BETA-REDUCE-FULL-REC-LIST))
 (8 8 (:TYPE-PRESCRIPTION PAIRLIS$))
 )
(BETA-EVAL-ALIST)
(BETA-EVAL-ALIST-OF-PAIRLIS
 (24 24 (:REWRITE BETA-EVAL-CONSTRAINT-3))
 (24 24 (:REWRITE BETA-EVAL-CONSTRAINT-2))
 )
(LOOKUP-IN-BETA-EVAL-ALIST
 (116 112 (:REWRITE DEFAULT-CAR))
 (43 41 (:REWRITE DEFAULT-CDR))
 (16 16 (:REWRITE BETA-EVAL-CONSTRAINT-3))
 (16 16 (:REWRITE BETA-EVAL-CONSTRAINT-2))
 (16 16 (:REWRITE BETA-EVAL-CONSTRAINT-1))
 )
(STRIP-CDRS-OF-PAIRLIS
 (28 25 (:REWRITE DEFAULT-CDR))
 (23 12 (:REWRITE DEFAULT-+-2))
 (20 17 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE DEFAULT-+-1))
 )
(FLAG-LEMMA-FOR-PSEUDO-TERMP-OF-BETA-REDUCE-FULL-REC
 (674 624 (:REWRITE DEFAULT-CDR))
 (639 588 (:REWRITE DEFAULT-CAR))
 (190 95 (:REWRITE DEFAULT-+-2))
 (165 15 (:DEFINITION PAIRLIS$))
 (120 120 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (101 101 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (95 95 (:REWRITE DEFAULT-+-1))
 (75 25 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:TYPE-PRESCRIPTION PAIRLIS$))
 )
(PSEUDO-TERMP-OF-BETA-REDUCE-FULL-REC)
(PSEUDO-TERM-LISTP-OF-BETA-REDUCE-FULL-REC-LIST)
(FLAG-LEMMA-FOR-BETA-REDUCE-FULL-REC-CORRECT
 (351 317 (:REWRITE DEFAULT-CAR))
 (332 303 (:REWRITE DEFAULT-CDR))
 (115 12 (:DEFINITION BETA-EVAL-ALIST))
 (114 12 (:DEFINITION PAIRLIS$))
 (64 32 (:REWRITE DEFAULT-+-2))
 (32 32 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (32 32 (:REWRITE DEFAULT-+-1))
 (31 31 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (24 8 (:DEFINITION SYMBOL-LISTP))
 (9 9 (:TYPE-PRESCRIPTION KWOTE-LST))
 (8 2 (:DEFINITION KWOTE-LST))
 (6 6 (:TYPE-PRESCRIPTION PAIRLIS$))
 (2 2 (:DEFINITION KWOTE))
 )
(BETA-REDUCE-FULL-REC-CORRECT)
(BETA-REDUCE-FULL-REC-LIST-CORRECT)
(BETA-REDUCE-FULL
 (289 274 (:REWRITE DEFAULT-CDR))
 (282 267 (:REWRITE DEFAULT-CAR))
 (200 99 (:REWRITE DEFAULT-+-2))
 (110 99 (:REWRITE DEFAULT-+-1))
 (69 19 (:DEFINITION SYMBOL-LISTP))
 (55 5 (:DEFINITION PAIRLIS$))
 (34 34 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (28 4 (:DEFINITION SYMBOL-ALISTP))
 (24 24 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (24 6 (:REWRITE COMMUTATIVITY-OF-+))
 (24 6 (:DEFINITION INTEGER-ABS))
 (24 3 (:DEFINITION LENGTH))
 (15 5 (:DEFINITION BETA-REDUCE-FULL-LIST))
 (9 7 (:REWRITE DEFAULT-<-2))
 (8 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-REALPART))
 (3 3 (:REWRITE DEFAULT-NUMERATOR))
 (3 3 (:REWRITE DEFAULT-IMAGPART))
 (3 3 (:REWRITE DEFAULT-DENOMINATOR))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 )
(LEN-OF-BETA-REDUCE-FULL-LIST
 (58 51 (:REWRITE DEFAULT-CDR))
 (48 24 (:REWRITE DEFAULT-+-2))
 (48 1 (:DEFINITION BETA-REDUCE-FULL))
 (32 26 (:REWRITE DEFAULT-CAR))
 (28 1 (:DEFINITION BETA-REDUCE-FULL-REC))
 (24 24 (:REWRITE DEFAULT-+-1))
 (22 2 (:DEFINITION PAIRLIS$))
 (7 1 (:DEFINITION ASSOC-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION BETA-REDUCE-FULL-REC-LIST))
 (2 2 (:TYPE-PRESCRIPTION PAIRLIS$))
 )
(TRUE-LISTP-OF-BETA-REDUCE-FULL-LIST)
(FLAG-LEMMA-FOR-PSEUDO-TERMP-OF-BETA-REDUCE-FULL
 (353 315 (:REWRITE DEFAULT-CDR))
 (342 303 (:REWRITE DEFAULT-CAR))
 (168 6 (:DEFINITION BETA-REDUCE-FULL-REC))
 (132 12 (:DEFINITION PAIRLIS$))
 (86 43 (:REWRITE DEFAULT-+-2))
 (48 48 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (46 46 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (43 43 (:REWRITE DEFAULT-+-1))
 (42 6 (:DEFINITION ASSOC-EQUAL))
 (36 36 (:TYPE-PRESCRIPTION BETA-REDUCE-FULL-REC-LIST))
 (33 11 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:TYPE-PRESCRIPTION PAIRLIS$))
 )
(PSEUDO-TERMP-OF-BETA-REDUCE-FULL)
(PSEUDO-TERM-LISTP-OF-BETA-REDUCE-FULL-LIST)
(FLAG-LEMMA-FOR-BETA-REDUCE-FULL-CORRECT
 (330 287 (:REWRITE DEFAULT-CAR))
 (327 289 (:REWRITE DEFAULT-CDR))
 (168 6 (:DEFINITION BETA-REDUCE-FULL-REC))
 (142 14 (:DEFINITION PAIRLIS$))
 (64 32 (:REWRITE DEFAULT-+-2))
 (52 8 (:DEFINITION ASSOC-EQUAL))
 (36 36 (:TYPE-PRESCRIPTION BETA-REDUCE-FULL-REC-LIST))
 (32 32 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (32 32 (:REWRITE DEFAULT-+-1))
 (31 31 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (24 8 (:DEFINITION SYMBOL-LISTP))
 (12 12 (:TYPE-PRESCRIPTION PAIRLIS$))
 (9 9 (:TYPE-PRESCRIPTION KWOTE-LST))
 (8 2 (:DEFINITION KWOTE-LST))
 (2 2 (:DEFINITION KWOTE))
 )
(BETA-REDUCE-FULL-CORRECT)
(BETA-REDUCE-FULL-LIST-CORRECT)
