(<-OF-0-AND-LENGTH-WHEN-STRINGP
 (23 3 (:DEFINITION LEN))
 (8 6 (:REWRITE CONSP-OF-COERCE-OF-LIST))
 (6 3 (:REWRITE DEFAULT-CDR))
 (6 3 (:REWRITE DEFAULT-<-2))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE EQUAL-OF-COERCE-OF-STRING-WHEN-QUOTEP))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-+-1))
 )
(EQUAL-OF-EMPTY-STRING-WHEN-STRINGP
 (9 1 (:DEFINITION LEN))
 (4 2 (:REWRITE CONSP-OF-COERCE-OF-LIST))
 (3 3 (:REWRITE EQUAL-OF-COERCE-OF-STRING-WHEN-QUOTEP))
 (2 1 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(NOT-EQUAL-OF-EMPTY-STRING-FORWARD-TO-<-OF-0-AND-LENGTH
 (7 1 (:DEFINITION LEN))
 (2 2 (:REWRITE CONSP-OF-COERCE-OF-LIST))
 (2 1 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-COERCE-2))
 (1 1 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(LENGTH-WHEN-NOT-STRINGP
 (10 2 (:DEFINITION LEN))
 (4 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
