(READ-FILE-INTO-STRING-IN-CHUNKS-REC
 (932 2 (:DEFINITION EXPLODE-ATOM))
 (850 6 (:DEFINITION EXPLODE-NONNEGATIVE-INTEGER))
 (458 12 (:DEFINITION FLOOR))
 (352 6 (:DEFINITION MOD))
 (312 312 (:TYPE-PRESCRIPTION NONNEGATIVE-INTEGER-QUOTIENT))
 (256 16 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (246 6 (:DEFINITION DIGIT-TO-CHAR))
 (136 93 (:REWRITE DEFAULT-+-2))
 (104 18 (:REWRITE COMMUTATIVITY-OF-*))
 (99 93 (:REWRITE DEFAULT-+-1))
 (73 60 (:REWRITE DEFAULT-<-1))
 (64 20 (:REWRITE COMMUTATIVITY-OF-+))
 (61 60 (:REWRITE DEFAULT-<-2))
 (56 2 (:DEFINITION ADD-PAIR))
 (54 44 (:REWRITE DEFAULT-*-2))
 (52 44 (:REWRITE DEFAULT-*-1))
 (48 34 (:REWRITE DEFAULT-UNARY-MINUS))
 (48 16 (:DEFINITION NFIX))
 (42 8 (:REWRITE DISTRIBUTIVITY))
 (38 4 (:REWRITE ASSOCIATIVITY-OF-+))
 (36 8 (:DEFINITION BINARY-APPEND))
 (34 28 (:REWRITE DEFAULT-CDR))
 (32 1 (:DEFINITION LENGTH))
 (28 28 (:REWRITE DEFAULT-CAR))
 (23 23 (:TYPE-PRESCRIPTION TRUE-LISTP-EXPLODE-ATOM))
 (22 11 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (18 2 (:REWRITE SYMBOL<-ASYMMETRIC))
 (17 5 (:REWRITE ZP-OPEN))
 (16 16 (:DEFINITION IFIX))
 (14 14 (:REWRITE DEFAULT-NUMERATOR))
 (14 14 (:REWRITE DEFAULT-DENOMINATOR))
 (14 2 (:REWRITE IMAGPART-+))
 (13 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (12 4 (:REWRITE SYMBOL<-TRICHOTOMY))
 (11 11 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (10 2 (:REWRITE REALPART-+))
 (10 2 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (10 2 (:DEFINITION ASSOC-EQUAL))
 (8 2 (:REWRITE DEFAULT-INTERN-IN-PACKAGE-OF-SYMBOL))
 (8 2 (:REWRITE DEFAULT-COERCE-3))
 (7 2 (:REWRITE INTERN-IN-PACKAGE-OF-SYMBOL-IS-IDENTITY))
 (6 6 (:TYPE-PRESCRIPTION SYMBOLP-INTERN-IN-PACKAGE-OF-SYMBOL))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL<))
 (6 4 (:REWRITE DEFAULT-REALPART))
 (6 4 (:REWRITE DEFAULT-IMAGPART))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 1 (:DEFINITION LEN))
 (4 4 (:REWRITE SYMBOL<-TRANSITIVE))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 2 (:TYPE-PRESCRIPTION TRUE-LISTP-UPDATE-NTH))
 (4 2 (:REWRITE UNICITY-OF-0))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:TYPE-PRESCRIPTION UPDATE-NTH))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-SYMBOL-NAME))
 (2 2 (:REWRITE RATIONALP-+))
 (2 2 (:DEFINITION FIX))
 (1 1 (:TYPE-PRESCRIPTION LEN))
 )
(READ-FILE-INTO-STRING-IN-CHUNKS)
(STRING-APPEND*
 (154 76 (:REWRITE DEFAULT-+-2))
 (105 76 (:REWRITE DEFAULT-+-1))
 (72 18 (:REWRITE COMMUTATIVITY-OF-+))
 (72 18 (:DEFINITION INTEGER-ABS))
 (72 9 (:DEFINITION LENGTH))
 (45 9 (:DEFINITION LEN))
 (27 22 (:REWRITE DEFAULT-<-2))
 (26 22 (:REWRITE DEFAULT-<-1))
 (25 25 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE FOLD-CONSTS-IN-+))
 (18 18 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:REWRITE DEFAULT-CAR))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (9 9 (:REWRITE DEFAULT-REALPART))
 (9 9 (:REWRITE DEFAULT-NUMERATOR))
 (9 9 (:REWRITE DEFAULT-IMAGPART))
 (9 9 (:REWRITE DEFAULT-DENOMINATOR))
 (9 9 (:REWRITE DEFAULT-COERCE-2))
 (9 9 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 )
