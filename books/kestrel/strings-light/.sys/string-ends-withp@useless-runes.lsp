(STRING-ENDS-WITHP
 (6 6 (:TYPE-PRESCRIPTION STRINGP-OF-REVERSE-TYPE))
 )
(STRING-ENDS-WITHP-FORWARD-TO-<=-OF-LENGTH-AND-LENGTH
 (95 11 (:DEFINITION LEN))
 (40 20 (:REWRITE CONSP-OF-COERCE-OF-LIST))
 (34 1 (:REWRITE PREFIXP-WHEN-NOT-SHORTER))
 (22 11 (:REWRITE DEFAULT-+-2))
 (21 11 (:REWRITE DEFAULT-CDR))
 (19 1 (:REWRITE PREFIXP-WHEN-LEN-0))
 (11 11 (:REWRITE EQUAL-OF-COERCE-OF-STRING-WHEN-QUOTEP))
 (11 11 (:REWRITE DEFAULT-+-1))
 (9 3 (:REWRITE PREFIX-WHEN-NOT-CONSP-ARG1-CHEAP))
 (8 8 (:REWRITE DEFAULT-COERCE-2))
 (7 3 (:REWRITE DEFAULT-<-1))
 (6 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:TYPE-PRESCRIPTION STRINGP-OF-REVERSE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION REVERSE))
 (3 1 (:REWRITE EQUAL-OF-LEN-OF-COERCE-OF-LIST-AND-0))
 (2 2 (:REWRITE <-OF-LEN-AND-LEN-WHEN-PREFIXP))
 )
(STRING-ENDS-WITHP-WHEN-NOT-STRINGP-ARG1
 (19 1 (:REWRITE PREFIXP-WHEN-LONGER))
 (18 2 (:DEFINITION LEN))
 (8 4 (:REWRITE CONSP-OF-COERCE-OF-LIST))
 (4 4 (:REWRITE EQUAL-OF-COERCE-OF-STRING-WHEN-QUOTEP))
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 1 (:REWRITE PREFIX-WHEN-NOT-CONSP-ARG1-CHEAP))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:TYPE-PRESCRIPTION STRINGP-OF-REVERSE-TYPE))
 (1 1 (:TYPE-PRESCRIPTION REVERSE))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
