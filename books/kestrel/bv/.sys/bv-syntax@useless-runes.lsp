(BV-TERM-SIZE
 (767 352 (:REWRITE DEFAULT-+-2))
 (459 352 (:REWRITE DEFAULT-+-1))
 (405 81 (:DEFINITION LEN))
 (240 60 (:REWRITE COMMUTATIVITY-OF-+))
 (240 60 (:DEFINITION INTEGER-ABS))
 (240 30 (:DEFINITION LENGTH))
 (238 238 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (190 168 (:REWRITE DEFAULT-<-2))
 (176 168 (:REWRITE DEFAULT-<-1))
 (164 164 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (149 149 (:TYPE-PRESCRIPTION LEN))
 (62 62 (:REWRITE DEFAULT-UNARY-MINUS))
 (51 17 (:DEFINITION SYMBOL-LISTP))
 (34 17 (:DEFINITION TRUE-LISTP))
 (30 30 (:REWRITE DEFAULT-REALPART))
 (30 30 (:REWRITE DEFAULT-NUMERATOR))
 (30 30 (:REWRITE DEFAULT-IMAGPART))
 (30 30 (:REWRITE DEFAULT-DENOMINATOR))
 (30 30 (:REWRITE DEFAULT-COERCE-2))
 (30 30 (:REWRITE DEFAULT-COERCE-1))
 (17 17 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (9 9 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
(BIND-VAR-TO-BV-TERM-SIZE)
(BIND-VAR-TO-BV-TERM-SIZE-IF-TRIMMABLE)
(TERM-SHOULD-BE-TRIMMED-HELPER
 (102 2 (:DEFINITION PSEUDO-TERMP))
 (30 30 (:REWRITE DEFAULT-CAR))
 (30 6 (:DEFINITION LEN))
 (28 28 (:REWRITE DEFAULT-CDR))
 (14 14 (:TYPE-PRESCRIPTION LEN))
 (12 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 2 (:DEFINITION SYMBOL-LISTP))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 2 (:DEFINITION TRUE-LISTP))
 (2 2 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(TERM-SHOULD-BE-TRIMMED)
