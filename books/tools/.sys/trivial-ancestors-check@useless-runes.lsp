(CHECK-ASSUMED-TRUE-OR-FALSE
 (230 230 (:REWRITE DEFAULT-CDR))
 (172 172 (:REWRITE DEFAULT-CAR))
 (135 27 (:DEFINITION LEN))
 (54 27 (:REWRITE DEFAULT-+-2))
 (27 27 (:REWRITE DEFAULT-+-1))
 (27 9 (:DEFINITION SYMBOL-LISTP))
 (22 11 (:DEFINITION TRUE-LISTP))
 (18 18 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (9 9 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 )
(CHECK-ASSUMED-TRUE-OR-FALSE-OK
 (149 146 (:REWRITE DEFAULT-CAR))
 (38 36 (:REWRITE DEFAULT-CDR))
 )
(TRIVIAL-ANCESTORS-CHECK
 (290 290 (:REWRITE DEFAULT-CDR))
 (212 212 (:REWRITE DEFAULT-CAR))
 (180 36 (:DEFINITION LEN))
 (72 36 (:REWRITE DEFAULT-+-2))
 (40 20 (:DEFINITION TRUE-LISTP))
 (36 36 (:REWRITE DEFAULT-+-1))
 (36 12 (:DEFINITION SYMBOL-LISTP))
 (26 26 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (15 15 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 )
(TRIVIAL-ANCESTORS-CHECK-OK
 (12 3 (:DEFINITION STRIP-ANCESTOR-LITERALS))
 (11 11 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
