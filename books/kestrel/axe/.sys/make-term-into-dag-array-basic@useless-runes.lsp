(MAKE-TERM-INTO-DAG-ARRAY-BASIC
 (192 1 (:DEFINITION PSEUDO-TERMP))
 (53 3 (:DEFINITION LEN))
 (35 1 (:DEFINITION SYMBOL-LISTP))
 (28 2 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (21 15 (:REWRITE DEFAULT-CAR))
 (17 15 (:REWRITE DEFAULT-CDR))
 (12 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (12 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (11 11 (:REWRITE USE-ALL-CONSP-2))
 (11 11 (:REWRITE USE-ALL-CONSP))
 (10 2 (:REWRITE ALL-CONSP-OF-CDR))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (8 8 (:TYPE-PRESCRIPTION ALL-CONSP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (6 6 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (6 6 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (6 2 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (5 5 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2 2 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 1 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (1 1 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (1 1 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 )
(WF-DAGP-OF-MAKE-TERM-INTO-DAG-ARRAY-BASIC
 (192 1 (:DEFINITION PSEUDO-TERMP))
 (53 3 (:DEFINITION LEN))
 (35 1 (:DEFINITION SYMBOL-LISTP))
 (28 2 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (21 15 (:REWRITE DEFAULT-CAR))
 (17 15 (:REWRITE DEFAULT-CDR))
 (12 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (12 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (11 11 (:REWRITE USE-ALL-CONSP-2))
 (11 11 (:REWRITE USE-ALL-CONSP))
 (10 2 (:REWRITE ALL-CONSP-OF-CDR))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (8 8 (:TYPE-PRESCRIPTION ALL-CONSP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (6 6 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (6 6 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (6 2 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (5 5 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2 2 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 1 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (1 1 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (1 1 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 )
(PSEUDO-DAG-ARRAYP-AFTER-MAKE-TERM-INTO-DAG-ARRAY-BASIC
 (106 6 (:DEFINITION LEN))
 (70 2 (:DEFINITION SYMBOL-LISTP))
 (56 4 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (42 30 (:REWRITE DEFAULT-CAR))
 (34 30 (:REWRITE DEFAULT-CDR))
 (24 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (24 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (22 22 (:REWRITE USE-ALL-CONSP-2))
 (22 22 (:REWRITE USE-ALL-CONSP))
 (20 4 (:REWRITE ALL-CONSP-OF-CDR))
 (16 16 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (16 16 (:TYPE-PRESCRIPTION ALL-CONSP))
 (12 12 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (12 12 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (12 6 (:REWRITE DEFAULT-+-2))
 (12 4 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (8 8 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (8 8 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (8 8 (:REWRITE EQUAL-WHEN-BVLT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (8 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 4 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 4 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (4 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (4 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (4 2 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (2 2 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (1 1 (:REWRITE PSEUDO-DAG-ARRAYP-MONOTONE))
 )
(NATP-OF-MV-NTH-3-OF-MAKE-TERM-INTO-DAG-ARRAY-BASIC
 (106 6 (:DEFINITION LEN))
 (70 2 (:DEFINITION SYMBOL-LISTP))
 (56 4 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (42 30 (:REWRITE DEFAULT-CAR))
 (34 30 (:REWRITE DEFAULT-CDR))
 (24 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (24 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (22 22 (:REWRITE USE-ALL-CONSP-2))
 (22 22 (:REWRITE USE-ALL-CONSP))
 (20 4 (:REWRITE ALL-CONSP-OF-CDR))
 (16 16 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (16 16 (:TYPE-PRESCRIPTION ALL-CONSP))
 (12 12 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (12 12 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (12 6 (:REWRITE DEFAULT-+-2))
 (12 4 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (8 8 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (8 8 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (8 8 (:REWRITE EQUAL-WHEN-BVLT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (8 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 4 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 4 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (4 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (4 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (4 2 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (2 2 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (1 1 (:REWRITE USE-ALL-NATP-2))
 (1 1 (:REWRITE USE-ALL-NATP))
 (1 1 (:REWRITE USE-ALL-<=-2))
 (1 1 (:REWRITE USE-ALL-<=))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE BOUND-WHEN-USB))
 (1 1 (:REWRITE <-WHEN-BVLT))
 (1 1 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 )
(<-OF-MV-NTH-3-OF-MAKE-TERM-INTO-DAG-ARRAY-BASIC
 (106 6 (:DEFINITION LEN))
 (70 2 (:DEFINITION SYMBOL-LISTP))
 (56 4 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (42 30 (:REWRITE DEFAULT-CAR))
 (34 30 (:REWRITE DEFAULT-CDR))
 (24 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (24 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (22 22 (:REWRITE USE-ALL-CONSP-2))
 (22 22 (:REWRITE USE-ALL-CONSP))
 (20 4 (:REWRITE ALL-CONSP-OF-CDR))
 (16 16 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (16 16 (:TYPE-PRESCRIPTION ALL-CONSP))
 (12 12 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (12 12 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (12 12 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (12 6 (:REWRITE DEFAULT-+-2))
 (12 4 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (8 8 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (8 8 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (8 8 (:REWRITE EQUAL-WHEN-BVLT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (8 8 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (8 8 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (8 8 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 4 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (4 4 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (4 4 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (4 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (4 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (4 4 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (4 2 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (2 2 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE USE-ALL-<=-2))
 (1 1 (:REWRITE USE-ALL-<=))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE BOUND-WHEN-USB))
 (1 1 (:REWRITE <-WHEN-BVLT))
 (1 1 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (1 1 (:REWRITE <-OF-+-OF-1-STRENGTHEN))
 )
(POSP-OF-MV-NTH-3-OF-MAKE-TERM-INTO-DAG-ARRAY-BASIC
 (192 1 (:DEFINITION PSEUDO-TERMP))
 (53 3 (:DEFINITION LEN))
 (35 1 (:DEFINITION SYMBOL-LISTP))
 (28 2 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (21 15 (:REWRITE DEFAULT-CAR))
 (17 15 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE USE-ALL-CONSP-2))
 (12 12 (:REWRITE USE-ALL-CONSP))
 (12 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (12 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (10 2 (:REWRITE ALL-CONSP-OF-CDR))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (8 8 (:TYPE-PRESCRIPTION ALL-CONSP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (6 6 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (6 6 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (6 2 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (5 5 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2 2 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 1 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (1 1 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (1 1 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 )
(DARGP-OF-MV-NTH-1-OF-MAKE-TERM-INTO-DAG-ARRAY-BASIC
 (192 1 (:DEFINITION PSEUDO-TERMP))
 (53 3 (:DEFINITION LEN))
 (35 1 (:DEFINITION SYMBOL-LISTP))
 (28 2 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (21 15 (:REWRITE DEFAULT-CAR))
 (17 15 (:REWRITE DEFAULT-CDR))
 (12 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (12 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (11 11 (:REWRITE USE-ALL-CONSP-2))
 (11 11 (:REWRITE USE-ALL-CONSP))
 (10 2 (:REWRITE ALL-CONSP-OF-CDR))
 (8 8 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (8 8 (:TYPE-PRESCRIPTION ALL-CONSP))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (6 6 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (6 6 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (6 2 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (5 5 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (4 4 (:REWRITE EQUAL-WHEN-BVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (4 4 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (4 4 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (4 4 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (4 2 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2 2 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (2 2 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 1 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (1 1 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (1 1 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (1 1 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (1 1 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 )
(MYQUOTEP-OF-MV-NTH-1-OF-MAKE-TERM-INTO-DAG-ARRAY-BASIC
 (265 15 (:DEFINITION LEN))
 (175 5 (:DEFINITION SYMBOL-LISTP))
 (140 10 (:REWRITE USE-ALL-CONSP-FOR-CAR))
 (107 77 (:REWRITE DEFAULT-CAR))
 (91 81 (:REWRITE DEFAULT-CDR))
 (60 20 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP))
 (60 10 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (57 57 (:REWRITE USE-ALL-CONSP-2))
 (57 57 (:REWRITE USE-ALL-CONSP))
 (50 10 (:REWRITE ALL-CONSP-OF-CDR))
 (40 40 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (40 40 (:TYPE-PRESCRIPTION ALL-CONSP))
 (30 30 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (30 30 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (30 30 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (30 15 (:REWRITE DEFAULT-+-2))
 (30 10 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (23 23 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (21 21 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (21 21 (:REWRITE EQUAL-WHEN-BVLT))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (21 21 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (21 21 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (20 20 (:REWRITE ALL-CONSP-WHEN-NOT-CONSP-CHEAP))
 (20 10 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (15 15 (:REWRITE DEFAULT-+-1))
 (10 10 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (10 10 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (10 10 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (10 10 (:REWRITE SYMBOLP-OF-CAR-WHEN-BOUNDED-DAG-EXPRP))
 (10 10 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (10 10 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (10 10 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (10 5 (:REWRITE SYMBOLP-OF-CAR-OF-CAR-WHEN-SYMBOL-ALISTP-CHEAP))
 (6 6 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (5 5 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (5 5 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (5 5 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (5 5 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (5 5 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (5 5 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (2 1 (:REWRITE DARGP-WHEN-NATP-CHEAP))
 (2 1 (:REWRITE DARGP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE USE-ALL-NATP-2))
 (1 1 (:REWRITE USE-ALL-NATP))
 (1 1 (:REWRITE USE-ALL-DARGP-2))
 (1 1 (:REWRITE USE-ALL-DARGP))
 (1 1 (:REWRITE USE-ALL-<=-2))
 (1 1 (:REWRITE USE-ALL-<=))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 (1 1 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (1 1 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (1 1 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (1 1 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DARGP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (1 1 (:REWRITE DARGP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE DARGP-WHEN-CONSP-CHEAP))
 (1 1 (:REWRITE BOUND-WHEN-USB))
 (1 1 (:REWRITE <-WHEN-BVLT))
 (1 1 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 )
(MAKE-TERMS-INTO-DAG-ARRAY-BASIC
 (8 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1 1 (:REWRITE USE-ALL-CONSP-2))
 (1 1 (:REWRITE USE-ALL-CONSP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(WF-DAGP-OF-MAKE-TERMS-INTO-DAG-ARRAY-BASIC
 (8 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1 1 (:REWRITE USE-ALL-CONSP-2))
 (1 1 (:REWRITE USE-ALL-CONSP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(BOUNDED-DARG-LISTP-OF-MV-NTH-1-OF-MAKE-TERMS-INTO-DAG-ARRAY-BASIC
 (8 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1 1 (:REWRITE USE-ALL-CONSP-2))
 (1 1 (:REWRITE USE-ALL-CONSP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(ALL-DARGP-OF-MV-NTH-1-OF-MAKE-TERMS-INTO-DAG-ARRAY-BASIC
 (8 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1 1 (:REWRITE USE-ALL-CONSP-2))
 (1 1 (:REWRITE USE-ALL-CONSP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(ALEN1-OF-MV-NTH-4-OF-MAKE-TERMS-INTO-DAG-ARRAY-BASIC
 (76 76 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (4 4 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (1 1 (:REWRITE EQUAL-WHEN-BVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (1 1 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (1 1 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 )
(BOUNDED-DAG-PARENT-ARRAYP-AFTER-OF-MAKE-TERMS-INTO-DAG-ARRAY-BASIC
 (4 4 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE USE-ALL-CONSP-2))
 (2 2 (:REWRITE USE-ALL-CONSP))
 (2 2 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (2 2 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE BOUNDED-DAG-PARENT-ARRAYP-MONOTONE))
 )
(TRUE-LISTP-OF-MV-NTH-1-OF-MAKE-TERMS-INTO-DAG-ARRAY-BASIC
 (8 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1 1 (:REWRITE USE-ALL-CONSP-2))
 (1 1 (:REWRITE USE-ALL-CONSP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(PSEUDO-DAG-ARRAYP-AFTER-MAKE-TERMS-INTO-DAG-ARRAY-BASIC
 (8 1 (:DEFINITION PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (2 2 (:REWRITE SYMBOLP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:TYPE-PRESCRIPTION PSEUDO-TERMP))
 (1 1 (:REWRITE USE-ALL-CONSP-2))
 (1 1 (:REWRITE USE-ALL-CONSP))
 (1 1 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
