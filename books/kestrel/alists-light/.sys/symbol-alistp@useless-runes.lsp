(SYMBOL-ALISTP-OF-CONS
 (11 11 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(SYMBOL-ALISTP-OF-ACONS
 (10 2 (:DEFINITION SYMBOL-ALISTP))
 (7 7 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(SYMBOL-ALISTP-OF-APPEND
 (95 95 (:REWRITE DEFAULT-CAR))
 (72 36 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (37 37 (:REWRITE DEFAULT-CDR))
 (36 36 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (36 36 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(SYMBOL-ALISTP-OF-UNION-EQUAL
 (74 74 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE DEFAULT-CDR))
 )
(SYMBOL-ALISTP-OF-CDR
 (3 3 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(SYMBOL-ALISTP-OF-TAKE
 (96 96 (:REWRITE DEFAULT-CAR))
 (60 41 (:REWRITE DEFAULT-+-2))
 (51 36 (:REWRITE DEFAULT-<-1))
 (44 44 (:REWRITE DEFAULT-CDR))
 (41 41 (:REWRITE DEFAULT-+-1))
 (36 36 (:REWRITE DEFAULT-<-2))
 (23 11 (:REWRITE ZP-OPEN))
 (12 4 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(SYMBOL-ALISTP-OF-NTHCDR
 (73 73 (:REWRITE DEFAULT-CAR))
 (54 54 (:REWRITE DEFAULT-+-2))
 (54 54 (:REWRITE DEFAULT-+-1))
 (49 19 (:REWRITE ZP-OPEN))
 (38 38 (:REWRITE DEFAULT-CDR))
 (30 10 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 )
(SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(SYMBOL-LISTP-OF-STRIP-CARS-WHEN-SYMBOL-ALISTP
 (20 19 (:REWRITE DEFAULT-CAR))
 (9 8 (:REWRITE DEFAULT-CDR))
 (8 2 (:REWRITE SYMBOL-ALISTP-OF-CDR))
 (6 3 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 )
(SYMBOL-LISTP-OF-STRIP-CARS-WHEN-SYMBOL-ALISTP-CHEAP)
(SYMBOL-ALISTP-OF-PAIRLIS$-ALT
 (26 26 (:REWRITE DEFAULT-CAR))
 (14 14 (:REWRITE DEFAULT-CDR))
 )
(SYMBOL-ALISTP-FORWARD-TO-ALISTP)
(TRUE-LISTP-WHEN-SYMBOL-ALISTP)
(ALISTP-WHEN-SYMBOL-ALISTP)
(SYMBOL-ALISTP-OF-REVAPPEND
 (134 104 (:REWRITE DEFAULT-CAR))
 (56 41 (:REWRITE DEFAULT-CDR))
 )
