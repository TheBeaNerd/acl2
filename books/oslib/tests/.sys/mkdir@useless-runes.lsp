(OSLIB::TRUE-LISTP-WHEN-STRING-LISTP
 (24 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (16 2 (:DEFINITION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:REWRITE SET::IN-SET))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(OSLIB::BASIC-MKDIR-TEST-FN
 (33 11 (:DEFINITION MEMBER-EQUAL))
 (11 11 (:REWRITE DEFAULT-CDR))
 (11 11 (:REWRITE DEFAULT-CAR))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 )
(OSLIB::STATE-P1-OF-BASIC-MKDIR-TEST
 (12 4 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (8 2 (:DEFINITION STATE-P))
 (6 2 (:DEFINITION MEMBER-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION STATE-P))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
