(DAG-OK-AFTER-SYMBOLIC-EXECUTION)
(ELIDE-MAKE-FRAME-ARGS
 (192 18 (:REWRITE DEFAULT-CDR))
 (52 52 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (52 52 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (52 52 (:REWRITE LEN-WHEN-EQUAL-TAKE))
 (52 52 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (52 52 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (52 52 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (52 52 (:META LEN-CONS-META-RULE))
 (26 26 (:REWRITE USE-ALL-HEAPREF-TABLE-ENTRYP-2))
 (16 16 (:REWRITE NOT-CONSP-WHEN-NUMBER-OF-ARRAY-DIMENSIONS-IS-0))
 (12 6 (:TYPE-PRESCRIPTION INTEGERP-OF-NTH-WHEN-ALL-NATP))
 (10 10 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (10 10 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (6 6 (:TYPE-PRESCRIPTION ALL-NATP))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE +-OF-MINUS-CONSTANT-VERSION))
 (4 4 (:REWRITE +-OF-MINUS))
 )
(ELIDE-METHOD-INFO-IN-TERM
 (2546 211 (:REWRITE DEFAULT-CDR))
 (387 153 (:REWRITE DEFAULT-+-2))
 (317 317 (:REWRITE USE-ALL-HEAPREF-TABLE-ENTRYP-2))
 (312 309 (:REWRITE ACL2-COUNT-WHEN-STRING))
 (266 266 (:REWRITE NOT-CONSP-WHEN-NUMBER-OF-ARRAY-DIMENSIONS-IS-0))
 (217 153 (:REWRITE DEFAULT-+-1))
 (163 163 (:REWRITE +-OF-MINUS-CONSTANT-VERSION))
 (157 157 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (157 157 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (157 157 (:REWRITE LEN-WHEN-EQUAL-TAKE))
 (157 157 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (157 157 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (157 157 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (157 157 (:META LEN-CONS-META-RULE))
 (123 123 (:REWRITE CAR-WHEN-EQUAL-NTHCDR))
 (76 2 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (70 70 (:REWRITE FOLD-CONSTS-IN-+))
 (69 17 (:REWRITE SET::EMPTY-SET-UNIQUE))
 (68 2 (:LINEAR LEN-OF-CDR-LINEAR))
 (60 60 (:REWRITE HELPER-HELPER2))
 (60 60 (:REWRITE HELPER-HELPER))
 (51 3 (:REWRITE TRUE-LISTP-WHEN-NOT-CONSP))
 (50 1 (:REWRITE NOT-MYQUOTEP-WHEN-LEN-WRONG))
 (45 45 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (45 45 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (44 1 (:REWRITE <-0-+-NEGATIVE-1))
 (36 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (36 4 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (24 24 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (24 24 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (24 12 (:TYPE-PRESCRIPTION INTEGERP-OF-NTH-WHEN-ALL-NATP))
 (24 8 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (24 8 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 (24 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (23 13 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (20 9 (:REWRITE DEFAULT-<-1))
 (18 13 (:REWRITE NOT-EQUAL-WHEN-LESS))
 (18 9 (:REWRITE DEFAULT-<-2))
 (18 6 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (18 6 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (17 17 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (17 17 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (17 17 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (17 17 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (17 17 (:REWRITE CLR-DIFFERENTIAL))
 (13 13 (:REWRITE NOT-EQUAL-WHEN-NOT-EQUAL-BVCHOP))
 (13 13 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM-ALT))
 (13 13 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM))
 (13 13 (:REWRITE NOT-EQUAL-FROM-BOUND))
 (13 13 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P-ALT))
 (13 13 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P))
 (13 13 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-BOUND-FORBIDS-IT2))
 (13 13 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-BOUND-FORBIDS-IT))
 (13 13 (:REWRITE IMPOSSIBLE-VALUE-2))
 (13 13 (:REWRITE IMPOSSIBLE-VALUE-1))
 (13 13 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (13 13 (:REWRITE EQUAL-WHEN-BVLT))
 (13 13 (:REWRITE EQUAL-WHEN-<-OF-+-ALT))
 (13 13 (:REWRITE EQUAL-WHEN-<-OF-+))
 (13 13 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (13 13 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (13 13 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (13 13 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (13 13 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (13 13 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (13 13 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (13 13 (:REWRITE EQUAL-CONSTANT-WHEN-SLICE-EQUAL-CONSTANT))
 (13 13 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SLICE-EQUAL-CONSTANT))
 (13 13 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (13 13 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 12 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (12 12 (:TYPE-PRESCRIPTION ALL-NATP))
 (11 11 (:REWRITE +-OF-MINUS))
 (10 10 (:REWRITE STRENGTHEN-<-OF-CONSTANT-WHEN-NOT-EQUAL))
 (10 10 (:REWRITE CONSP-OF-CAR-WHEN-POSSIBLY-NEGATED-NODENUMSP-WEAKEN-CHEAP))
 (10 10 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (10 10 (:REWRITE <-TRANS))
 (10 2 (:REWRITE JVM::LEN-HACK))
 (9 9 (:REWRITE USE-ALL-<-2))
 (9 9 (:REWRITE USE-ALL-<))
 (9 9 (:REWRITE MY-NON-INTEGERP-<-INTEGERP))
 (9 9 (:REWRITE MY-INTEGERP-<-NON-INTEGERP))
 (9 9 (:REWRITE DROP-LINEAR-HYPS2))
 (9 9 (:REWRITE DROP->-HYPS))
 (9 9 (:REWRITE DROP-<-HYPS))
 (9 9 (:REWRITE BOUND-WHEN-USB2))
 (9 9 (:REWRITE <-WHEN-SBVLT-CONSTANTS))
 (9 9 (:REWRITE <-WHEN-BVLT))
 (9 9 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (9 9 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (9 9 (:REWRITE <-OF-NON-INTEGERP-AND-INTEGERP))
 (9 9 (:REWRITE <-OF-CONSTANT-WHEN-USB2))
 (9 9 (:REWRITE <-LEMMA-FOR-KNOWN-OPERATORS-NON-DAG))
 (9 9 (:REWRITE <-FROM-<=-FREE))
 (8 8 (:TYPE-PRESCRIPTION ELIDE-MAKE-FRAME-ARGS))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:REWRITE USE-ALL-CONSP-2))
 (6 6 (:REWRITE USE-ALL-CONSP))
 (6 6 (:REWRITE SET::SETP-CONSTANT-OPENER))
 (6 6 (:REWRITE LEN-GIVES-CONSP))
 (6 6 (:REWRITE SET::IN-SET))
 (6 6 (:REWRITE SET::EMPTY-CONSTANT-OPENER))
 (6 6 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (6 6 (:REWRITE CONSP-FROM-LEN-BOUND))
 (6 6 (:REWRITE <-OF-0-WHEN-<-FREE))
 (6 3 (:REWRITE TRUE-LISTP-WHEN-POSSIBLY-NEGATED-NODENUMSP))
 (5 5 (:REWRITE LEN->-0-WEAKEN))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 4 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (4 4 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (4 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (4 4 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:TYPE-PRESCRIPTION POSSIBLY-NEGATED-NODENUMSP))
 (3 3 (:REWRITE WFR-HACK5))
 (3 3 (:REWRITE USE-ALL-<=-2))
 (3 3 (:REWRITE USE-ALL-<=))
 (3 3 (:REWRITE USE-<=-PLUS-CONSTANT-BOUND-TO-DROP-<=-HYP))
 (3 3 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (3 3 (:REWRITE NOT-LESS-WHEN->=-MAX-OF-CONTAINING-BAG))
 (3 3 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (3 3 (:REWRITE NOT-<-WHEN-SBVLT))
 (3 3 (:REWRITE INEQ-HACK2))
 (3 3 (:REWRITE INEQ-HACK))
 (3 3 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (3 3 (:REWRITE DROP-LINEAR-HYPS3))
 (3 3 (:REWRITE DROP-<=-HYPS))
 (3 3 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (3 3 (:REWRITE BOUND-WHEN-USB))
 (3 3 (:REWRITE ARRAY-DIM-BOUND))
 (3 3 (:REWRITE <-OF-NEGATIVE-WHEN-USBP))
 (3 3 (:REWRITE <-OF-CONSTANT-WHEN-USB))
 (3 3 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:REWRITE <-OF-CONSTANT-WHEN-<=-OF-FREE))
 (3 3 (:REWRITE <-LEMMA-FOR-KNOWN-OPERATORS-ALT-NON-DAG))
 (2 2 (:REWRITE NO-ROOM-BETWEEN-INTS-LEMMA))
 (2 2 (:REWRITE DROP-LINEAR-HYPS1))
 (2 2 (:REWRITE COLLECT-CONSTANTS-OVER-<-2))
 (2 2 (:REWRITE BOUND-LEMMA))
 (2 2 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (2 2 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (1 1 (:TYPE-PRESCRIPTION ELIDE-METHOD-INFO-IN-TERM))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (1 1 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(PRINT-DAG-WITH-ELIDED-METHOD-INFO-AUX
 (21360 282 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (13447 31 (:REWRITE DEFAULT-CAR))
 (7351 32 (:REWRITE DEFAULT-CDR))
 (1055 1 (:DEFINITION WEAK-DAGP-AUX))
 (787 484 (:REWRITE DEFAULT-+-2))
 (746 2 (:DEFINITION NATP))
 (556 3 (:DEFINITION NAT-LISTP))
 (540 249 (:REWRITE JVM::LEN-HACK))
 (532 532 (:REWRITE +-OF-MINUS-CONSTANT-VERSION))
 (532 253 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP))
 (532 253 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (530 530 (:REWRITE +-OF-MINUS))
 (526 526 (:REWRITE LEN-WHEN-PSEUDO-DAGP-AUX))
 (526 526 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (526 526 (:REWRITE LEN-WHEN-EQUAL-TAKE))
 (526 526 (:REWRITE LEN-WHEN-DARGP-LESS-THAN))
 (526 526 (:REWRITE LEN-WHEN-BV-ARRAYP))
 (526 526 (:REWRITE LEN-WHEN-BOUNDED-DAG-EXPRP-AND-QUOTEP))
 (526 526 (:META LEN-CONS-META-RULE))
 (520 520 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN-STRONG))
 (520 520 (:REWRITE LEN-OF-CAR-WHEN-ITEMS-HAVE-LEN))
 (506 253 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (484 484 (:REWRITE DEFAULT-+-1))
 (443 427 (:REWRITE SET::EMPTY-SET-UNIQUE))
 (427 427 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER-ALT))
 (427 427 (:REWRITE REFS-DIFFER-WHEN-ARRAY-DIMENSIONS-DIFFER))
 (427 427 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (427 427 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (427 427 (:REWRITE CLR-DIFFERENTIAL))
 (418 10 (:REWRITE USE-ALL-<-FOR-CAR))
 (376 14 (:REWRITE <-0-+-NEGATIVE-1))
 (336 5 (:REWRITE WEAK-DAGP-AUX-WHEN-PSEUDO-DAGP-AUX-2))
 (336 5 (:REWRITE ALL-NATP-WHEN-NAT-LISTP))
 (286 286 (:TYPE-PRESCRIPTION PSEUDO-DAGP))
 (282 282 (:REWRITE USE-ALL-HEAPREF-TABLE-ENTRYP-2))
 (282 282 (:REWRITE NOT-CONSP-WHEN-NUMBER-OF-ARRAY-DIMENSIONS-IS-0))
 (282 282 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (273 273 (:REWRITE USE-ALL-CONSP-2))
 (273 273 (:REWRITE USE-ALL-CONSP))
 (273 273 (:REWRITE LEN-GIVES-CONSP))
 (273 273 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (273 273 (:REWRITE CONSP-FROM-LEN-BOUND))
 (272 272 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (258 258 (:REWRITE CONSP-OF-CAR-WHEN-POSSIBLY-NEGATED-NODENUMSP-WEAKEN-CHEAP))
 (255 130 (:REWRITE NOT-EQUAL-WHEN-LESS))
 (253 253 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (253 253 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (253 253 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (253 253 (:REWRITE CONSP-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (251 251 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (248 2 (:REWRITE ALL-<-OF-0-WHEN-NAT-LISTP))
 (245 5 (:DEFINITION TOP-NODENUM))
 (231 231 (:REWRITE LEN-OF-CDDR-WHEN-EQUAL-OF-LEN))
 (225 2 (:REWRITE USE-ALL-NATP-FOR-CAR))
 (194 4 (:REWRITE NATP-WHEN-INTEGERP-CHEAP))
 (145 29 (:REWRITE HACK1))
 (145 6 (:REWRITE NAT-LISTP-WHEN-ALL-NATP))
 (132 130 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (130 130 (:REWRITE NOT-EQUAL-WHEN-NOT-EQUAL-BVCHOP))
 (130 130 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM-ALT))
 (130 130 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM))
 (130 130 (:REWRITE NOT-EQUAL-FROM-BOUND))
 (130 130 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P-ALT))
 (130 130 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P))
 (130 130 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-BOUND-FORBIDS-IT2))
 (130 130 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-BOUND-FORBIDS-IT))
 (130 130 (:REWRITE IMPOSSIBLE-VALUE-2))
 (130 130 (:REWRITE IMPOSSIBLE-VALUE-1))
 (130 130 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (130 130 (:REWRITE EQUAL-WHEN-BVLT))
 (130 130 (:REWRITE EQUAL-WHEN-<-OF-+-ALT))
 (130 130 (:REWRITE EQUAL-WHEN-<-OF-+))
 (130 130 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (130 130 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (130 130 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (130 130 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (130 130 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (130 130 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (130 130 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (130 130 (:REWRITE EQUAL-CONSTANT-WHEN-SLICE-EQUAL-CONSTANT))
 (130 130 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SLICE-EQUAL-CONSTANT))
 (130 130 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (130 130 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (124 124 (:REWRITE EQUAL-OF-IF-CONSTANTS))
 (123 123 (:REWRITE NOT-0-WHEN-BIT-NOT-0))
 (123 123 (:REWRITE EQUAL-OF-0-WHEN-BVLT-OF-SLICE))
 (123 123 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (122 10 (:REWRITE INEQ-HACK2))
 (122 10 (:REWRITE INEQ-HACK))
 (122 2 (:REWRITE ALL-<-OF-0-WHEN-ALL-NATP))
 (121 19 (:REWRITE +-COMBINE-CONSTANTS))
 (119 18 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (116 5 (:REWRITE ALL-NATP-WHEN-NOT-CONSP))
 (68 2 (:REWRITE PSEUDO-DAGP-AUX-OF-CDR))
 (64 32 (:TYPE-PRESCRIPTION INTEGERP-OF-NTH-WHEN-ALL-NATP))
 (57 47 (:REWRITE <-TRANS))
 (52 52 (:TYPE-PRESCRIPTION ALL-NATP))
 (50 1 (:REWRITE NOT-MYQUOTEP-WHEN-LEN-WRONG))
 (48 48 (:REWRITE EQUAL-CONSTANT-+))
 (48 16 (:REWRITE <-OF-LEN-WHEN-NTH-NON-NIL))
 (48 16 (:REWRITE <-OF-LEN-WHEN-INTEGERP-OF-NTH))
 (47 47 (:REWRITE STRENGTHEN-<-OF-CONSTANT-WHEN-NOT-EQUAL))
 (47 47 (:REWRITE <-WHEN-BOUNDED-AXE-TREEP))
 (44 33 (:REWRITE DEFAULT-<-2))
 (44 2 (:REWRITE INTEGERP-IMPLIES-ACL2-NUMBERP))
 (42 2 (:REWRITE INTEGERP-OF-IF))
 (36 36 (:TYPE-PRESCRIPTION ELIDE-MAKE-FRAME-ARGS))
 (33 33 (:REWRITE USE-ALL-<-2))
 (33 33 (:REWRITE USE-ALL-<))
 (33 33 (:REWRITE MY-NON-INTEGERP-<-INTEGERP))
 (33 33 (:REWRITE MY-INTEGERP-<-NON-INTEGERP))
 (33 33 (:REWRITE DROP-LINEAR-HYPS2))
 (33 33 (:REWRITE DROP->-HYPS))
 (33 33 (:REWRITE DROP-<-HYPS))
 (33 33 (:REWRITE DEFAULT-<-1))
 (33 33 (:REWRITE BOUND-WHEN-USB2))
 (33 33 (:REWRITE <-WHEN-SBVLT-CONSTANTS))
 (33 33 (:REWRITE <-WHEN-BVLT))
 (33 33 (:REWRITE <-WHEN-BOUNDED-DARG-LISTP-GEN))
 (33 33 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (33 33 (:REWRITE <-OF-NON-INTEGERP-AND-INTEGERP))
 (33 33 (:REWRITE <-OF-CONSTANT-WHEN-USB2))
 (33 33 (:REWRITE <-LEMMA-FOR-KNOWN-OPERATORS-NON-DAG))
 (33 33 (:REWRITE <-FROM-<=-FREE))
 (31 31 (:REWRITE CAR-WHEN-EQUAL-NTHCDR))
 (30 2 (:REWRITE TRUE-LISTP-WHEN-NOT-CONSP))
 (27 27 (:TYPE-PRESCRIPTION NAT-LISTP))
 (27 9 (:REWRITE PSEUDO-DAGP-OF-CDR-WHEN-PSEUDO-DAGP))
 (26 26 (:TYPE-PRESCRIPTION ALL-<))
 (26 13 (:REWRITE PLUS-OF-MINUS-3-BV-5))
 (23 23 (:REWRITE <-OF-0-WHEN-<-FREE))
 (21 7 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 (21 5 (:REWRITE WEAK-DAGP-AUX-WHEN-PSEUDO-DAGP))
 (21 1 (:REWRITE BOUNDED-DAG-EXPRP-OF-CDR-OF-CAR-WHEN-WEAK-DAGP-AUX))
 (20 10 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (19 19 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (19 19 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (16 10 (:REWRITE NOT-<-WHEN-SBVLT))
 (14 14 (:TYPE-PRESCRIPTION PSEUDO-DAGP-AUX))
 (11 11 (:REWRITE WFR-HACK5))
 (11 11 (:REWRITE CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (10 10 (:REWRITE USE-ALL-<=-2))
 (10 10 (:REWRITE USE-ALL-<=))
 (10 10 (:REWRITE USE-<=-PLUS-CONSTANT-BOUND-TO-DROP-<=-HYP))
 (10 10 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (10 10 (:REWRITE NOT-LESS-WHEN->=-MAX-OF-CONTAINING-BAG))
 (10 10 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (10 10 (:REWRITE NOT-<-OF-CAR-WHEN-BOUNDED-DARG-LISTP-2))
 (10 10 (:REWRITE DROP-LINEAR-HYPS3))
 (10 10 (:REWRITE DROP-<=-HYPS))
 (10 10 (:REWRITE BOUND-WHEN-USB))
 (10 10 (:REWRITE ARRAY-DIM-BOUND))
 (10 10 (:REWRITE <-OF-NEGATIVE-WHEN-USBP))
 (10 10 (:REWRITE <-OF-CONSTANT-WHEN-USB))
 (10 10 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (10 10 (:REWRITE <-OF-CONSTANT-WHEN-<=-OF-FREE))
 (10 10 (:REWRITE <-LEMMA-FOR-KNOWN-OPERATORS-ALT-NON-DAG))
 (10 5 (:REWRITE ALL-NATP-WHEN-NAT-LISTP-CHEAP))
 (9 1 (:REWRITE ALL-NATP-OF-CDR))
 (8 8 (:REWRITE LEN->-0-WEAKEN))
 (8 4 (:REWRITE INTEGERP-OF-CAR-WHEN-NAT-LISTP-CHEAP))
 (8 4 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-NATP-CHEAP))
 (8 4 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (8 4 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-CHEAP))
 (8 4 (:REWRITE INTEGERP-OF-CAR-OF-CAR-WHEN-WEAK-DAGP-AUX-CHEAP))
 (8 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (7 7 (:REWRITE PSEUDO-DAGP-AUX-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE NONNEG-WHEN-DARGP-LESS-THAN))
 (6 6 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (6 6 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (6 6 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (6 6 (:REWRITE ALL-<-TRANSITIVE))
 (6 6 (:REWRITE <-OF-0-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (6 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE WEAK-DAGP-AUX-WHEN-PSEUDO-DAGP-AUX))
 (5 5 (:REWRITE WEAK-DAGP-AUX-WHEN-BOUNDED-WEAK-DAGP-AUX))
 (5 5 (:REWRITE ALL-NATP-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION WEAK-DAGP))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (4 4 (:REWRITE QUOTE-LEMMA-FOR-BOUNDED-DARG-LISTP-GEN-ALT))
 (4 4 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-BOUNDED-UNDO-PAIRSP))
 (4 4 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (4 4 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE))
 (4 4 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-FORCED-FREE))
 (4 4 (:REWRITE INTEGERP-WHEN-SIGNED-BYTE-P))
 (4 4 (:REWRITE INTEGERP-WHEN-DARGP-LESS-THAN))
 (4 4 (:REWRITE INTEGERP-OF-CAR-WHEN-POSSIBLY-NEGATED-NODENUMSP-WEAKEN-CHEAP))
 (4 4 (:REWRITE INTEGERP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (4 4 (:REWRITE INTEGERP-OF-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (4 4 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 4 (:REWRITE ARRAY-DIM-IS-INTEGERP))
 (4 2 (:REWRITE TRUE-LISTP-WHEN-POSSIBLY-NEGATED-NODENUMSP))
 (3 3 (:REWRITE PSEUDO-DAGP-AUX-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:TYPE-PRESCRIPTION POSSIBLY-NEGATED-NODENUMSP))
 (2 2 (:REWRITE USE-ALL-RATIONALP-2))
 (2 2 (:REWRITE USE-ALL-RATIONALP))
 (2 2 (:REWRITE USE-ALL-NATP-2))
 (2 2 (:REWRITE USE-ALL-NATP))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-PSEUDO-DAGP-AUX))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-BV-ARRAYP))
 (2 2 (:REWRITE TRUE-LISTP-OF-CAR-WHEN-BOUNDED-DARG-LISTP))
 (2 2 (:REWRITE SET::SETP-CONSTANT-OPENER))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (2 2 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE NATP-WHEN-BOUNDED-DARG-LISTP-GEN))
 (2 2 (:REWRITE NATP-OF-CAR-OF-CAR-WHEN-PSEUDO-DAGP-AUX-2))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE SET::EMPTY-CONSTANT-OPENER))
 (2 2 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 1 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-MYQUOTEP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION MYQUOTEP))
 (1 1 (:TYPE-PRESCRIPTION BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-DARGP-LESS-THAN))
 (1 1 (:REWRITE MYQUOTEP-WHEN-BOUNDED-DAG-EXPRP))
 (1 1 (:REWRITE MYQUOTEP-WHEN-AXE-TREEP))
 (1 1 (:REWRITE EQUAL-OF-NON-NATP-AND-CAAR-WHEN-WHEN-BOUNDED-NATP-ALISTP))
 (1 1 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-SYMBOLP-CHEAP))
 (1 1 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE BOUNDED-DAG-EXPRP-WHEN-EQUAL-OF-QUOTE-AND-CAR-CHEAP))
 (1 1 (:REWRITE BOUNDED-DAG-EXPRP-MONOTONE))
 )
(PRINT-DAG-WITH-ELIDED-METHOD-INFO)
(REPEATEDLY-RUN)
(UNROLL-JAVA-CODE-FN-AUX)
(UNROLL-JAVA-CODE-FN)
