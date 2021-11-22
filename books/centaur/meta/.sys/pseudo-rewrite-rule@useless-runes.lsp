(CMR::PSEUDO-REWRITE-RULE-P)
(CMR::PSEUDO-REWRITE-RULE-P-IMPLIES
 (131 131 (:REWRITE DEFAULT-CDR))
 (80 16 (:DEFINITION LEN))
 (56 56 (:REWRITE DEFAULT-CAR))
 (32 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 8 (:DEFINITION TRUE-LISTP))
 (16 4 (:DEFINITION SYMBOL-LISTP))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (8 8 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (8 8 (:REWRITE FN-CHECK-DEF-FORMALS))
 (5 5 (:REWRITE FN-CHECK-DEF-NOT-QUOTE))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(CMR::PSEUDO-REWRITE-RULE-P-IMPLIES-NATP-NUME)
(CMR::MEXTRACT-GOOD-REWRITE-RULESP)
(CMR::MEXTRACT-GOOD-REWRITE-RULESP-OF-CONS
 (253 253 (:REWRITE DEFAULT-CDR))
 (96 96 (:REWRITE DEFAULT-CAR))
 (10 5 (:REWRITE MEXTRACT-EV-OF-TYPESPEC-CHECK-CALL))
 (10 5 (:REWRITE MEXTRACT-EV-OF-QUOTE))
 (10 5 (:REWRITE MEXTRACT-EV-OF-NOT-CALL))
 (10 5 (:REWRITE MEXTRACT-EV-OF-LAMBDA))
 (10 5 (:REWRITE MEXTRACT-EV-OF-IMPLIES-CALL))
 (10 5 (:REWRITE MEXTRACT-EV-OF-IFF-CALL))
 (10 5 (:REWRITE MEXTRACT-EV-OF-IF-CALL))
 (10 5 (:REWRITE MEXTRACT-EV-OF-EQUAL-CALL))
 (5 5 (:REWRITE MEXTRACT-EV-OF-VARIABLE))
 )
(CMR::MEXTRACT-GOOD-REWRITE-RULESP-OF-CDR
 (20 20 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE MEXTRACT-EV-OF-TYPESPEC-CHECK-CALL))
 (2 1 (:REWRITE MEXTRACT-EV-OF-QUOTE))
 (2 1 (:REWRITE MEXTRACT-EV-OF-NOT-CALL))
 (2 1 (:REWRITE MEXTRACT-EV-OF-LAMBDA))
 (2 1 (:REWRITE MEXTRACT-EV-OF-IMPLIES-CALL))
 (2 1 (:REWRITE MEXTRACT-EV-OF-IFF-CALL))
 (2 1 (:REWRITE MEXTRACT-EV-OF-IF-CALL))
 (2 1 (:REWRITE MEXTRACT-EV-OF-EQUAL-CALL))
 (1 1 (:REWRITE MEXTRACT-EV-OF-VARIABLE))
 )
(CMR::MEXTRACT-EV-OF-CAR-WHEN-GOOD-REWRITE-RULESP
 (37 21 (:REWRITE DEFAULT-CAR))
 (17 3 (:REWRITE MEXTRACT-EV-OF-TYPESPEC-CHECK-CALL))
 (17 3 (:REWRITE MEXTRACT-EV-OF-QUOTE))
 (17 3 (:REWRITE MEXTRACT-EV-OF-NOT-CALL))
 (17 3 (:REWRITE MEXTRACT-EV-OF-IMPLIES-CALL))
 (17 3 (:REWRITE MEXTRACT-EV-OF-IFF-CALL))
 (17 3 (:REWRITE MEXTRACT-EV-OF-IF-CALL))
 (17 3 (:REWRITE MEXTRACT-EV-OF-EQUAL-CALL))
 (15 3 (:REWRITE MEXTRACT-EV-OF-LAMBDA))
 (6 3 (:REWRITE MEXTRACT-EV-OF-VARIABLE))
 (3 3 (:REWRITE MEXTRACT-LEMMA-TERM))
 )
(CMR::MEXTRACT-GOOD-REWRITE-RULESP-BADGUY)
(CMR::MEXTRACT-GOOD-REWRITE-RULESP-BY-BADGUY
 (13332 13332 (:REWRITE DEFAULT-CDR))
 (5486 5486 (:REWRITE DEFAULT-CAR))
 (2008 67 (:REWRITE CMR::MEXTRACT-GOOD-REWRITE-RULESP-OF-CDR))
 (630 336 (:REWRITE MEXTRACT-EV-OF-TYPESPEC-CHECK-CALL))
 (630 336 (:REWRITE MEXTRACT-EV-OF-NOT-CALL))
 (630 336 (:REWRITE MEXTRACT-EV-OF-LAMBDA))
 (630 336 (:REWRITE MEXTRACT-EV-OF-IFF-CALL))
 (630 336 (:REWRITE MEXTRACT-EV-OF-IF-CALL))
 (630 336 (:REWRITE MEXTRACT-EV-OF-EQUAL-CALL))
 (308 308 (:REWRITE MEXTRACT-EV-OF-VARIABLE))
 (145 145 (:REWRITE MEXTRACT-EV-FN-GET-DEF))
 (145 145 (:REWRITE MEXTRACT-EV-FN-CHECK-DEF))
 (69 69 (:REWRITE MEXTRACT-EV-CONJOIN-ATOM))
 (55 55 (:REWRITE MEXTRACT-LEMMA))
 (1 1 (:REWRITE FN-CHECK-DEF-FORMALS))
 )
(CMR::MEXTRACT-GOOD-REWRITE-RULESP-OF-LEMMAS
 (11 1 (:DEFINITION FGETPROP))
 (7 7 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE MEXTRACT-EV-OF-VARIABLE))
 (1 1 (:REWRITE MEXTRACT-EV-OF-TYPESPEC-CHECK-CALL))
 (1 1 (:REWRITE MEXTRACT-EV-OF-QUOTE))
 (1 1 (:REWRITE MEXTRACT-EV-OF-NOT-CALL))
 (1 1 (:REWRITE MEXTRACT-EV-OF-LAMBDA))
 (1 1 (:REWRITE MEXTRACT-EV-OF-IMPLIES-CALL))
 (1 1 (:REWRITE MEXTRACT-EV-OF-IFF-CALL))
 (1 1 (:REWRITE MEXTRACT-EV-OF-IF-CALL))
 (1 1 (:REWRITE MEXTRACT-EV-OF-EQUAL-CALL))
 )
(CMR::PSEUDO-REWRITE-RULE-LISTP)
(CMR::PSEUDO-REWRITE-RULE-LISTP-OF-CONS
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(CMR::PSEUDO-REWRITE-RULE-LISTP-OF-CDR
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(CMR::PSEUDO-REWRITE-RULE-P-OF-CAR
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(CMR::REWRITE-RULE-TERM-ALT-DEF
 (50 50 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
