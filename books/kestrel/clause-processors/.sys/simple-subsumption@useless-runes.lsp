(IF-AND-NOT-EVAL-OF-MAKE-IF-TERM
 (461 37 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (384 120 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (280 64 (:REWRITE DEFAULT-CAR))
 (173 37 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (144 144 (:TYPE-PRESCRIPTION LEN))
 (120 120 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (96 96 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (96 96 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (72 24 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (48 24 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (37 37 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (37 37 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (28 28 (:REWRITE DEFAULT-CDR))
 (24 24 (:TYPE-PRESCRIPTION ALISTP))
 (24 24 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 )
(IF-AND-NOT-EVAL-WHEN-CLEARLY-IMPLIED-BY-SOME-DISJUNCTIONP
 (742 107 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (400 48 (:REWRITE DEFAULT-CAR))
 (237 45 (:REWRITE LEN-OF-CDR))
 (177 35 (:REWRITE DEFAULT-CDR))
 (153 153 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (112 56 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (107 107 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (101 20 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (92 92 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (74 2 (:DEFINITION PAIRLIS$))
 (71 16 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (52 37 (:REWRITE DEFAULT-<-2))
 (48 46 (:REWRITE DEFAULT-+-2))
 (46 46 (:REWRITE DEFAULT-+-1))
 (37 37 (:REWRITE DEFAULT-<-1))
 (27 9 (:REWRITE +-COMBINE-CONSTANTS))
 (24 24 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (23 23 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (19 1 (:DEFINITION KWOTE-LST))
 (18 9 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (18 3 (:REWRITE LEN-OF-IF-AND-NOT-EVAL-LIST))
 (17 5 (:REWRITE IF-AND-NOT-EVAL-LIST-OF-ATOM))
 (11 11 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (9 9 (:DEFINITION FIX))
 (1 1 (:REWRITE EQUAL-OF-LEN-AND-0))
 (1 1 (:DEFINITION KWOTE))
 )
(IF-AND-NOT-EVAL-OF-CADDDR-WHEN-TERM-IS-CONJUNCTIONP-FORWARD)
(IF-AND-NOT-EVAL-OF-CADDDR-WHEN-TERM-IS-CONJUNCTIONP)
(IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP)
(ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-OF-HANDLE-CONSTANT-LITERALS
 (2747 264 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (546 462 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (513 79 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-NOT-CONSP))
 (504 77 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (469 77 (:REWRITE LEN-OF-CDR))
 (281 165 (:REWRITE DEFAULT-<-2))
 (264 264 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (210 210 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (165 165 (:REWRITE DEFAULT-<-1))
 (137 137 (:REWRITE DEFAULT-CDR))
 (131 90 (:REWRITE DEFAULT-+-2))
 (126 63 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (106 15 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (103 103 (:TYPE-PRESCRIPTION ALISTP))
 (100 100 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (90 90 (:REWRITE DEFAULT-+-1))
 (80 40 (:REWRITE CAR-WHEN-ALISTP-IFF-CHEAP))
 (51 17 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (46 15 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (40 15 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (34 34 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (28 28 (:REWRITE EQUAL-OF-LEN-AND-0))
 (17 17 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-IMPLIED-BY-SOME-DISJUNCTIONP))
 (15 15 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (12 12 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (8 2 (:REWRITE +-COMBINE-CONSTANTS))
 )
(IF-AND-NOT-EVAL-OF-DISJOIN-OF-HANDLE-CONSTANT-LITERALS)
(IF-AND-NOT-EVAL-OF-CONJOIN-OF-DISJOIN-LST-OF-CLAUSE-TO-CLAUSE-LIST)
(ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-OF-NEGATE-DISJUNCT-LIST
 (105 1 (:DEFINITION ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL))
 (94 12 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (50 4 (:REWRITE NOT-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T))
 (48 4 (:REWRITE DISJOIN-WHEN-NOT-CONSP))
 (40 40 (:TYPE-PRESCRIPTION LEN))
 (29 8 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (22 17 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (22 3 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (20 2 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-NOT-CONSP))
 (14 14 (:TYPE-PRESCRIPTION NEGATE-TERMS))
 (13 2 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (11 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (10 5 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (10 3 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (8 3 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (8 1 (:REWRITE LEN-OF-CDR))
 (7 7 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (7 3 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (5 5 (:TYPE-PRESCRIPTION ALISTP))
 (4 4 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (4 3 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (4 2 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-IMPLIED-BY-SOME-DISJUNCTIONP))
 (3 3 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (1 1 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (1 1 (:REWRITE EQUAL-OF-LEN-AND-0))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(SKIP-CONJUNCTS-BEFORE
 (87 40 (:REWRITE DEFAULT-+-2))
 (56 25 (:REWRITE DEFAULT-CDR))
 (54 40 (:REWRITE DEFAULT-+-1))
 (49 13 (:REWRITE DEFAULT-CAR))
 (28 28 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (24 6 (:REWRITE COMMUTATIVITY-OF-+))
 (24 6 (:DEFINITION INTEGER-ABS))
 (19 19 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (18 11 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (12 11 (:REWRITE DEFAULT-<-1))
 (12 3 (:DEFINITION LENGTH))
 (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 3 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (4 4 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (3 3 (:TYPE-PRESCRIPTION ALISTP))
 (3 3 (:REWRITE DEFAULT-REALPART))
 (3 3 (:REWRITE DEFAULT-NUMERATOR))
 (3 3 (:REWRITE DEFAULT-IMAGPART))
 (3 3 (:REWRITE DEFAULT-DENOMINATOR))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (1 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 )
(PSEUDO-TERMP-OF-SKIP-CONJUNCTS-BEFORE
 (959 97 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (437 151 (:REWRITE DEFAULT-CAR))
 (282 150 (:REWRITE DEFAULT-CDR))
 (274 24 (:DEFINITION TRUE-LISTP))
 (209 11 (:DEFINITION SYMBOL-LISTP))
 (206 206 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (124 17 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (104 50 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (98 54 (:REWRITE DEFAULT-<-2))
 (97 97 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (95 51 (:REWRITE DEFAULT-+-2))
 (62 62 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (54 54 (:REWRITE DEFAULT-<-1))
 (51 51 (:REWRITE DEFAULT-+-1))
 (44 22 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (27 27 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (24 24 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (22 22 (:TYPE-PRESCRIPTION ALISTP))
 (22 22 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (22 22 (:REWRITE PSEUDO-TERMP-WHEN-SYMBOLP))
 (22 11 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (22 11 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (20 20 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (16 8 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (16 8 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (16 8 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (14 14 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (12 12 (:REWRITE DEFAULT-COERCE-2))
 (12 12 (:REWRITE DEFAULT-COERCE-1))
 (11 11 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (8 8 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (3 1 (:REWRITE +-COMBINE-CONSTANTS))
 )
(SKIP-CONJUNCTS-BEFORE-CORRECT
 (400 67 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (319 20 (:REWRITE DEFAULT-CAR))
 (166 9 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (155 18 (:REWRITE LEN-OF-CDR))
 (94 14 (:REWRITE DEFAULT-CDR))
 (72 72 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (67 67 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (58 9 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (56 56 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (48 8 (:REWRITE EQUAL-OF-LEN-AND-0))
 (40 9 (:REWRITE IF-AND-NOT-EVAL-OF-QUOTE))
 (40 9 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (37 13 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (34 17 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (26 18 (:REWRITE DEFAULT-+-2))
 (20 5 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 12 (:REWRITE DEFAULT-<-2))
 (17 17 (:TYPE-PRESCRIPTION ALISTP))
 (12 12 (:REWRITE DEFAULT-<-1))
 (12 12 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (9 9 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (9 9 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-IMPLIED-BY-SOME-DISJUNCTIONP))
 (9 9 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (9 9 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (3 3 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (3 1 (:REWRITE +-COMBINE-CONSTANTS))
 (2 1 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (1 1 (:DEFINITION FIX))
 )
(SKIP-CONJUNCTS-LEMMA-HELPER
 (1571 278 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (984 290 (:REWRITE DEFAULT-CDR))
 (423 423 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (218 218 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (90 59 (:REWRITE DEFAULT-+-2))
 (68 34 (:REWRITE DEFAULT-<-2))
 (60 6 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (59 59 (:REWRITE DEFAULT-+-1))
 (48 6 (:LINEAR LEN-OF-CDR-LINEAR))
 (44 44 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (34 34 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(SKIP-CONJUNCTS-LEMMA
 (36 2 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (32 10 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (20 2 (:REWRITE DEFAULT-CAR))
 (12 2 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (10 10 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (9 9 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (8 8 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (8 3 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (8 2 (:REWRITE IF-AND-NOT-EVAL-OF-QUOTE))
 (8 2 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (3 3 (:REWRITE SKIP-CONJUNCTS-BEFORE-CORRECT))
 (2 2 (:TYPE-PRESCRIPTION ALISTP))
 (2 2 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (2 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-IMPLIED-BY-SOME-DISJUNCTIONP))
 (2 2 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (2 2 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(AMONG-CONJUNCTSP
 (87 40 (:REWRITE DEFAULT-+-2))
 (56 25 (:REWRITE DEFAULT-CDR))
 (54 40 (:REWRITE DEFAULT-+-1))
 (49 13 (:REWRITE DEFAULT-CAR))
 (28 28 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (24 6 (:REWRITE COMMUTATIVITY-OF-+))
 (24 6 (:DEFINITION INTEGER-ABS))
 (19 19 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (18 11 (:REWRITE DEFAULT-<-2))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (12 11 (:REWRITE DEFAULT-<-1))
 (12 3 (:DEFINITION LENGTH))
 (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 3 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (4 4 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (3 3 (:TYPE-PRESCRIPTION ALISTP))
 (3 3 (:REWRITE DEFAULT-REALPART))
 (3 3 (:REWRITE DEFAULT-NUMERATOR))
 (3 3 (:REWRITE DEFAULT-IMAGPART))
 (3 3 (:REWRITE DEFAULT-DENOMINATOR))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (1 1 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 )
(AMONG-CONJUNCTSP-BEFORE-CORRECT
 (522 125 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (333 55 (:REWRITE DEFAULT-CAR))
 (240 20 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (210 78 (:REWRITE DEFAULT-CDR))
 (157 157 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (125 125 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (95 20 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (95 3 (:REWRITE IF-AND-NOT-EVAL-OF-CADDDR-WHEN-TERM-IS-CONJUNCTIONP))
 (72 36 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (61 61 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (56 20 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (52 52 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (40 4 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (36 36 (:TYPE-PRESCRIPTION ALISTP))
 (32 4 (:LINEAR LEN-OF-CDR-LINEAR))
 (24 20 (:REWRITE DEFAULT-+-2))
 (20 20 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-IMPLIED-BY-SOME-DISJUNCTIONP))
 (20 20 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (20 20 (:REWRITE DEFAULT-+-1))
 (18 18 (:REWRITE SKIP-CONJUNCTS-BEFORE-CORRECT))
 (18 18 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (18 9 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (9 9 (:REWRITE DEFAULT-<-1))
 )
(CLEARLY-UNIMPLIES-FOR-CONJUNCTIONSP
 (409 164 (:REWRITE DEFAULT-CDR))
 (302 109 (:REWRITE DEFAULT-CAR))
 (208 208 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (158 83 (:REWRITE DEFAULT-+-2))
 (97 83 (:REWRITE DEFAULT-+-1))
 (95 5 (:DEFINITION SYMBOL-LISTP))
 (82 45 (:REWRITE DEFAULT-<-2))
 (56 6 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (46 45 (:REWRITE DEFAULT-<-1))
 (34 34 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (32 16 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (30 3 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (24 6 (:REWRITE COMMUTATIVITY-OF-+))
 (24 6 (:DEFINITION INTEGER-ABS))
 (24 3 (:LINEAR LEN-OF-CDR-LINEAR))
 (18 9 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (18 9 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (18 9 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (16 16 (:TYPE-PRESCRIPTION ALISTP))
 (16 8 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (14 14 (:REWRITE PSEUDO-TERMP-WHEN-SYMBOLP))
 (14 14 (:REWRITE FOLD-CONSTS-IN-+))
 (13 13 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (10 10 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (9 9 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (8 8 (:REWRITE DEFAULT-COERCE-2))
 (8 8 (:REWRITE DEFAULT-COERCE-1))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-REALPART))
 (3 3 (:REWRITE DEFAULT-NUMERATOR))
 (3 3 (:REWRITE DEFAULT-IMAGPART))
 (3 3 (:REWRITE DEFAULT-DENOMINATOR))
 (1 1 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 )
(CLEARLY-UNIMPLIES-FOR-CONJUNCTIONSP-CORRECT
 (1174 165 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (974 56 (:REWRITE DEFAULT-CAR))
 (554 74 (:REWRITE LEN-OF-CDR))
 (369 55 (:REWRITE DEFAULT-CDR))
 (324 20 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (205 205 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (165 165 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (143 143 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (138 69 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (134 21 (:REWRITE EQUAL-OF-LEN-AND-0))
 (130 20 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (98 20 (:REWRITE IF-AND-NOT-EVAL-OF-QUOTE))
 (98 20 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (95 74 (:REWRITE DEFAULT-+-2))
 (92 23 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (74 74 (:REWRITE DEFAULT-+-1))
 (69 69 (:TYPE-PRESCRIPTION ALISTP))
 (61 46 (:REWRITE DEFAULT-<-2))
 (50 50 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (46 46 (:REWRITE DEFAULT-<-1))
 (24 8 (:REWRITE +-COMBINE-CONSTANTS))
 (20 20 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-IMPLIED-BY-SOME-DISJUNCTIONP))
 (20 20 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (20 20 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (16 8 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (14 14 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (13 13 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (8 8 (:DEFINITION FIX))
 (1 1 (:REWRITE SKIP-CONJUNCTS-LEMMA-HELPER))
 )
(CLEARLY-UNIMPLIED-BY-SOME-CONJUNCTIONP)
(IF-AND-NOT-EVAL-WHEN-CLEARLY-UNIMPLIED-BY-SOME-CONJUNCTIONP
 (2302 218 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (1502 65 (:REWRITE DEFAULT-CAR))
 (1348 116 (:REWRITE LEN-OF-CDR))
 (920 80 (:REWRITE DEFAULT-CDR))
 (600 84 (:REWRITE EQUAL-OF-LEN-AND-0))
 (275 275 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (218 218 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (200 116 (:REWRITE DEFAULT-+-2))
 (185 185 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (148 78 (:REWRITE DEFAULT-<-2))
 (130 65 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (116 116 (:REWRITE DEFAULT-+-1))
 (114 43 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (90 5 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (78 78 (:REWRITE DEFAULT-<-1))
 (78 18 (:REWRITE DISJOIN-WHEN-NOT-CONSP))
 (78 9 (:REWRITE NOT-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T))
 (71 71 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (65 65 (:TYPE-PRESCRIPTION ALISTP))
 (39 9 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-NOT-CONSP))
 (32 8 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (30 5 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (24 24 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (20 5 (:REWRITE IF-AND-NOT-EVAL-OF-QUOTE))
 (20 5 (:REWRITE IF-AND-NOT-EVAL-OF-IF-CALL))
 (18 9 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-NIL))
 (18 6 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (6 6 (:REWRITE SKIP-CONJUNCTS-BEFORE-CORRECT))
 (6 6 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-IMPLIED-BY-SOME-DISJUNCTIONP))
 (6 6 (:REWRITE AMONG-CONJUNCTSP-BEFORE-CORRECT))
 (5 5 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (5 5 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 )
(RESOLVE-IFS-IN-TERM
 (2355 1101 (:REWRITE DEFAULT-+-2))
 (1550 379 (:REWRITE DEFAULT-CAR))
 (1523 1101 (:REWRITE DEFAULT-+-1))
 (884 453 (:REWRITE DEFAULT-CDR))
 (800 200 (:REWRITE COMMUTATIVITY-OF-+))
 (800 200 (:DEFINITION INTEGER-ABS))
 (614 386 (:REWRITE DEFAULT-<-2))
 (431 386 (:REWRITE DEFAULT-<-1))
 (400 100 (:DEFINITION LENGTH))
 (353 353 (:REWRITE FOLD-CONSTS-IN-+))
 (200 200 (:REWRITE DEFAULT-UNARY-MINUS))
 (141 141 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (136 68 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (132 132 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (100 100 (:REWRITE DEFAULT-REALPART))
 (100 100 (:REWRITE DEFAULT-NUMERATOR))
 (100 100 (:REWRITE DEFAULT-IMAGPART))
 (100 100 (:REWRITE DEFAULT-DENOMINATOR))
 (100 100 (:REWRITE DEFAULT-COERCE-2))
 (100 100 (:REWRITE DEFAULT-COERCE-1))
 (85 55 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (78 78 (:TYPE-PRESCRIPTION ALISTP))
 (60 6 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (48 6 (:LINEAR LEN-OF-CDR-LINEAR))
 (45 45 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (20 10 (:REWRITE CAR-WHEN-ALISTP-IFF-CHEAP))
 (10 10 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(PSEUDO-TERMP-OF-RESOLVE-IFS-IN-TERM
 (1335 629 (:REWRITE DEFAULT-CAR))
 (1333 691 (:REWRITE DEFAULT-CDR))
 (860 860 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (741 39 (:DEFINITION SYMBOL-LISTP))
 (470 470 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (416 41 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (371 188 (:REWRITE DEFAULT-<-2))
 (300 143 (:REWRITE DEFAULT-+-2))
 (188 188 (:REWRITE DEFAULT-<-1))
 (188 188 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (176 88 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (166 83 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (166 83 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (166 83 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (143 143 (:REWRITE DEFAULT-+-1))
 (134 67 (:REWRITE PSEUDO-TERMP-OF-CAR-WHEN-PSEUDO-TERM-LISTP-CHEAP))
 (115 115 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (98 49 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (94 94 (:TYPE-PRESCRIPTION ALISTP))
 (83 83 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (78 78 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (50 5 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (49 49 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (41 41 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (40 5 (:LINEAR LEN-OF-CDR-LINEAR))
 (39 39 (:REWRITE DEFAULT-COERCE-2))
 (39 39 (:REWRITE DEFAULT-COERCE-1))
 (12 6 (:REWRITE CAR-WHEN-ALISTP-IFF-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION MAKE-IF-TERM))
 )
(RESOLVE-IFS-IN-TERM
 (1127 270 (:REWRITE DEFAULT-CAR))
 (648 245 (:REWRITE DEFAULT-CDR))
 (627 39 (:DEFINITION LENGTH))
 (400 400 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (316 25 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (288 13 (:DEFINITION SYMBOL-LISTP))
 (250 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (246 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (240 122 (:REWRITE DEFAULT-<-2))
 (224 224 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (122 122 (:REWRITE DEFAULT-<-1))
 (121 67 (:REWRITE DEFAULT-+-2))
 (120 120 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (96 48 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (95 95 (:REWRITE PSEUDO-TERMP-WHEN-SYMBOLP))
 (81 81 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (77 77 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (68 34 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP-CHEAP))
 (68 34 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (68 34 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (67 67 (:REWRITE DEFAULT-+-1))
 (47 47 (:TYPE-PRESCRIPTION ALISTP))
 (42 21 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (35 35 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (34 34 (:REWRITE EQUAL-OF-LEN-AND-0))
 (30 30 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (28 28 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (26 13 (:REWRITE CAR-WHEN-ALISTP-IFF-CHEAP))
 (21 21 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (20 20 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (18 6 (:REWRITE +-COMBINE-CONSTANTS))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (13 13 (:REWRITE DEFAULT-COERCE-1))
 )
(RESOLVE-IFS-IN-TERM-CORRECT
 (12808 2223 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (9612 534 (:DEFINITION MEMBER-EQUAL))
 (6338 92 (:REWRITE IF-AND-NOT-EVAL-OF-CADDDR-WHEN-TERM-IS-CONJUNCTIONP))
 (6226 346 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (5054 254 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (4460 1193 (:REWRITE DEFAULT-CAR))
 (4198 346 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (2670 2670 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2476 2476 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2223 2223 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1790 346 (:REWRITE IF-AND-NOT-EVAL-OF-NOT-CALL))
 (1724 970 (:REWRITE DEFAULT-CDR))
 (1416 708 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (1402 1402 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1185 598 (:REWRITE DEFAULT-<-2))
 (990 366 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (748 136 (:REWRITE DISJOIN-WHEN-NOT-CONSP))
 (748 68 (:REWRITE NOT-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T))
 (724 724 (:TYPE-PRESCRIPTION ALISTP))
 (680 68 (:REWRITE ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-WHEN-NOT-CONSP))
 (680 68 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-NOT-CONSP))
 (638 638 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (598 598 (:REWRITE DEFAULT-<-1))
 (281 281 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 (274 274 (:REWRITE SKIP-CONJUNCTS-BEFORE-CORRECT))
 (274 274 (:REWRITE CLEARLY-UNIMPLIES-FOR-CONJUNCTIONSP-CORRECT))
 (274 274 (:REWRITE AMONG-CONJUNCTSP-BEFORE-CORRECT))
 (263 263 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (136 68 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-NIL))
 (99 16 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (55 43 (:REWRITE DEFAULT-+-2))
 (50 5 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (43 43 (:REWRITE DEFAULT-+-1))
 (40 5 (:LINEAR LEN-OF-CDR-LINEAR))
 (32 16 (:REWRITE CAR-WHEN-ALISTP-IFF-CHEAP))
 (16 16 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(RESOLVE-IFS-IN-CLAUSE
 (674 3 (:DEFINITION PSEUDO-TERMP))
 (508 2 (:REWRITE PSEUDO-TERM-LISTP-OF-GET-CONJUNCTS-OF-TERM))
 (181 110 (:REWRITE DEFAULT-CAR))
 (164 140 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (152 76 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (116 58 (:REWRITE DEFAULT-<-2))
 (115 91 (:REWRITE DEFAULT-CDR))
 (114 6 (:DEFINITION BINARY-APPEND))
 (95 5 (:DEFINITION TRUE-LIST-FIX))
 (87 87 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (70 35 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP-CHEAP))
 (70 35 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (66 6 (:DEFINITION TRUE-LISTP))
 (64 64 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (63 3 (:DEFINITION SYMBOL-LISTP))
 (59 59 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (58 58 (:REWRITE DEFAULT-<-1))
 (50 25 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (48 9 (:DEFINITION LENGTH))
 (42 42 (:REWRITE PSEUDO-TERMP-WHEN-SYMBOLP))
 (35 16 (:REWRITE DEFAULT-+-2))
 (33 3 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (31 31 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (25 25 (:TYPE-PRESCRIPTION ALISTP))
 (16 16 (:REWRITE DEFAULT-+-1))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
 (12 6 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (11 11 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (6 6 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (6 6 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (3 3 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (3 3 (:REWRITE DEFAULT-COERCE-2))
 (3 3 (:REWRITE DEFAULT-COERCE-1))
 (3 3 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(RESOLVE-IFS-IN-CLAUSE-CORRECT
 (17480 2098 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (9794 545 (:DEFINITION MEMBER-EQUAL))
 (7244 220 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (4230 3384 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (4054 194 (:REWRITE IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (3852 1747 (:REWRITE DEFAULT-CAR))
 (2725 2725 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (2140 194 (:REWRITE IF-AND-NOT-EVAL-OF-LAMBDA-BETTER))
 (1989 1039 (:REWRITE DEFAULT-<-2))
 (1862 178 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-NOT-CONSP))
 (1859 1683 (:REWRITE DEFAULT-CDR))
 (1456 1456 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (1302 651 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (1130 1130 (:TYPE-PRESCRIPTION RESOLVE-IFS-IN-CLAUSE))
 (1039 1039 (:REWRITE DEFAULT-<-1))
 (926 926 (:TYPE-PRESCRIPTION GET-DISJUNCTS-OF-TERM))
 (765 74 (:REWRITE ALL-EVAL-TO-TRUE-WITH-IF-AND-NOT-EVAL-WHEN-NOT-CONSP))
 (651 651 (:TYPE-PRESCRIPTION ALISTP))
 (625 220 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (540 54 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (447 376 (:REWRITE DEFAULT-+-2))
 (432 54 (:LINEAR LEN-OF-CDR-LINEAR))
 (405 405 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (405 135 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (397 397 (:TYPE-PRESCRIPTION GET-CONJUNCTS-OF-TERM))
 (378 91 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (376 376 (:REWRITE DEFAULT-+-1))
 (220 220 (:REWRITE SKIP-CONJUNCTS-BEFORE-CORRECT))
 (220 220 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-UNIMPLIED-BY-SOME-CONJUNCTIONP))
 (220 220 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-IMPLIED-BY-SOME-DISJUNCTIONP))
 (220 220 (:REWRITE CLEARLY-UNIMPLIES-FOR-CONJUNCTIONSP-CORRECT))
 (220 220 (:REWRITE AMONG-CONJUNCTSP-BEFORE-CORRECT))
 (135 135 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (135 135 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (125 125 (:REWRITE IF-AND-NOT-EVAL-OF-VARIABLE))
 )
(RESOLVE-IFS-IN-CLAUSE-CORRECT-SPECIAL
 (37 4 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (33 10 (:REWRITE DISJOIN-WHEN-NOT-CONSP))
 (23 3 (:REWRITE NOT-IF-AND-NOT-EVAL-WHEN-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-AND-MEMBER-EQUAL))
 (18 1 (:DEFINITION MEMBER-EQUAL))
 (17 17 (:TYPE-PRESCRIPTION LEN))
 (12 4 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (12 3 (:REWRITE ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-NOT-CONSP))
 (9 7 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (9 3 (:REWRITE IF-AND-NOT-EVAL-WHEN-TERM-IS-CONJUNCTIONP))
 (6 6 (:TYPE-PRESCRIPTION TERM-IS-CONJUNCTIONP))
 (6 3 (:REWRITE NOT-ALL-EVAL-TO-FALSE-WITH-IF-AND-NOT-EVAL-WHEN-EQUAL-OF-DISJOIN-AND-QUOTE-T))
 (5 5 (:TYPE-PRESCRIPTION RESOLVE-IFS-IN-CLAUSE))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (4 4 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (3 3 (:REWRITE SKIP-CONJUNCTS-BEFORE-CORRECT))
 (3 3 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-UNIMPLIED-BY-SOME-CONJUNCTIONP))
 (3 3 (:REWRITE IF-AND-NOT-EVAL-WHEN-CLEARLY-IMPLIED-BY-SOME-DISJUNCTIONP))
 (3 3 (:REWRITE CLEARLY-UNIMPLIES-FOR-CONJUNCTIONSP-CORRECT))
 (3 3 (:REWRITE AMONG-CONJUNCTSP-BEFORE-CORRECT))
 (2 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE CONSP-WHEN-LEN-GREATER))
 )
(PSEUDO-TERM-LISTP-OF-RESOLVE-IFS-IN-CLAUSE
 (1006 98 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (608 32 (:DEFINITION BINARY-APPEND))
 (222 136 (:REWRITE DEFAULT-CAR))
 (209 170 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (173 143 (:REWRITE DEFAULT-CDR))
 (139 74 (:REWRITE DEFAULT-<-2))
 (133 69 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (98 98 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (92 46 (:REWRITE PSEUDO-TERM-LISTP-WHEN-SYMBOL-LISTP-CHEAP-2))
 (88 88 (:TYPE-PRESCRIPTION GET-DISJUNCTS-OF-TERM))
 (80 13 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (75 75 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (74 74 (:REWRITE DEFAULT-<-1))
 (56 28 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP-CHEAP))
 (56 28 (:REWRITE PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERMP))
 (48 48 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (47 27 (:REWRITE DEFAULT-+-2))
 (40 40 (:TYPE-PRESCRIPTION GET-CONJUNCTS-OF-TERM))
 (38 38 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (38 2 (:DEFINITION SYMBOL-LISTP))
 (34 17 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP-CHEAP))
 (32 6 (:DEFINITION LENGTH))
 (27 27 (:REWRITE DEFAULT-+-1))
 (21 21 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (17 17 (:TYPE-PRESCRIPTION ALISTP))
 (13 13 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (8 4 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (4 4 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (2 2 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(SIMPLE-SUBSUMPTION-CLAUSE-PROCESSOR)
(SIMPLE-SUBSUMPTION-CLAUSE-PROCESSOR-CORRECT)
