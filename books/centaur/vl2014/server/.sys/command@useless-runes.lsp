(VL2014::VLS-FAIL-FN)
(VL2014::STRINGP-OF-VLS-FAIL-FN)
(VL2014::VLS-SUCCESS-FN
 (86 1 (:REWRITE VL2014::STRINGP-WHEN-TRUE-LISTP))
 (30 1 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (17 1 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (14 1 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (12 1 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (6 6 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (6 1 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (4 2 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (4 1 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (3 3 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (3 1 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (2 2 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (2 2 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE))
 (2 2 (:REWRITE STRINGP-WHEN-MEMBER-EQUAL-OF-STRING-LISTP))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (2 1 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (2 1 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (2 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 1 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LIST*P))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LIST*P))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LIST*P))
 (1 1 (:TYPE-PRESCRIPTION STR::OCT-DIGIT-CHAR-LIST*P))
 (1 1 (:TYPE-PRESCRIPTION STR::HEX-DIGIT-CHAR-LIST*P))
 (1 1 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (1 1 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LIST*P))
 (1 1 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION BOOLEAN-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (1 1 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (1 1 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (1 1 (:REWRITE SET::IN-SET))
 (1 1 (:REWRITE FN-CHECK-DEF-FORMALS))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (1 1 (:REWRITE CONSP-BY-LEN))
 (1 1 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 )
(VL2014::STRINGP-OF-VLS-SUCCESS)
(VL2014::VLS-COMMANDTYPE-P)
(VL2014::TYPE-WHEN-VLS-COMMANDTYPE-P)
(VL2014::VLS-COMMANDTYPE-P-POSSIBILITIES)
(VL2014::VLS-COMMANDTYPE-FIX$INLINE)
(VL2014::RETURN-TYPE-OF-VLS-COMMANDTYPE-FIX)
(VL2014::VLS-COMMANDTYPE-FIX-IDEMPOTENT)
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(VL2014::VLS-COMMANDTYPE-EQUIV$INLINE)
(VL2014::VLS-COMMANDTYPE-EQUIV-IS-AN-EQUIVALENCE)
(VL2014::VLS-COMMANDTYPE-EQUIV-IMPLIES-EQUAL-VLS-COMMANDTYPE-FIX-1)
(VL2014::VLS-COMMANDTYPE-FIX-UNDER-VLS-COMMANDTYPE-EQUIV)
(VL2014::VLS-COMMANDINFO-P
 (3 3 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 )
(VL2014::VLS-COMMANDINFO)
(VL2014::HONSED-VLS-COMMANDINFO)
(VL2014::VLS-COMMANDINFO->FN$INLINE
 (3 3 (:DEFINITION ASSOC-EQUAL))
 )
(VL2014::VLS-COMMANDINFO->ARGS$INLINE
 (3 3 (:DEFINITION ASSOC-EQUAL))
 )
(VL2014::VLS-COMMANDINFO->TYPE$INLINE
 (3 3 (:DEFINITION ASSOC-EQUAL))
 )
(VL2014::CONSP-OF-VLS-COMMANDINFO)
(VL2014::BOOLEANP-OF-VLS-COMMANDINFO-P)
(VL2014::VLS-COMMANDINFO-P-OF-VLS-COMMANDINFO)
(VL2014::CONSP-WHEN-VLS-COMMANDINFO-P)
(VL2014::VLS-COMMANDINFO->FN-OF-VLS-COMMANDINFO)
(VL2014::VLS-COMMANDINFO->ARGS-OF-VLS-COMMANDINFO)
(VL2014::VLS-COMMANDINFO->TYPE-OF-VLS-COMMANDINFO)
(VL2014::RETURN-TYPE-OF-VLS-COMMANDINFO->FN)
(VL2014::RETURN-TYPE-OF-VLS-COMMANDINFO->ARGS)
(VL2014::RETURN-TYPE-OF-VLS-COMMANDINFO->TYPE)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(VL2014::VLS-COMMANDINFOLIST-P)
(VL2014::VLS-COMMANDINFOLIST-P-OF-CONS)
(VL2014::VLS-COMMANDINFOLIST-P-OF-CDR-WHEN-VLS-COMMANDINFOLIST-P)
(VL2014::VLS-COMMANDINFOLIST-P-WHEN-NOT-CONSP)
(VL2014::VLS-COMMANDINFO-P-OF-CAR-WHEN-VLS-COMMANDINFOLIST-P)
(VL2014::VLS-COMMANDINFOLIST-P-OF-APPEND)
(VL2014::VLS-COMMANDINFOLIST-P-OF-LIST-FIX)
(VL2014::VLS-COMMANDINFOLIST-P-OF-SFIX)
(VL2014::VLS-COMMANDINFOLIST-P-OF-INSERT)
(VL2014::VLS-COMMANDINFOLIST-P-OF-DELETE)
(VL2014::VLS-COMMANDINFOLIST-P-OF-MERGESORT)
(VL2014::VLS-COMMANDINFOLIST-P-OF-UNION)
(VL2014::VLS-COMMANDINFOLIST-P-OF-INTERSECT-1)
(VL2014::VLS-COMMANDINFOLIST-P-OF-INTERSECT-2)
(VL2014::VLS-COMMANDINFOLIST-P-OF-DIFFERENCE)
(VL2014::VLS-COMMANDINFOLIST-P-OF-DUPLICATED-MEMBERS)
(VL2014::VLS-COMMANDINFOLIST-P-OF-REV)
(VL2014::VLS-COMMANDINFOLIST-P-OF-RCONS)
(VL2014::VLS-COMMANDINFO-P-WHEN-MEMBER-EQUAL-OF-VLS-COMMANDINFOLIST-P)
(VL2014::VLS-COMMANDINFOLIST-P-WHEN-SUBSETP-EQUAL)
(VL2014::VLS-COMMANDINFOLIST-P-SET-EQUIV-CONGRUENCE)
(VL2014::VLS-COMMANDINFOLIST-P-OF-SET-DIFFERENCE-EQUAL)
(VL2014::VLS-COMMANDINFOLIST-P-OF-INTERSECTION-EQUAL-1)
(VL2014::VLS-COMMANDINFOLIST-P-OF-INTERSECTION-EQUAL-2)
(VL2014::VLS-COMMANDINFOLIST-P-OF-UNION-EQUAL)
(VL2014::VLS-COMMANDINFOLIST-P-OF-TAKE)
(VL2014::VLS-COMMANDINFOLIST-P-OF-REPEAT)
(VL2014::VLS-COMMANDINFO-P-OF-NTH-WHEN-VLS-COMMANDINFOLIST-P)
(VL2014::VLS-COMMANDINFOLIST-P-OF-UPDATE-NTH)
(VL2014::VLS-COMMANDINFOLIST-P-OF-BUTLAST)
(VL2014::VLS-COMMANDINFOLIST-P-OF-NTHCDR)
(VL2014::VLS-COMMANDINFOLIST-P-OF-LAST)
(VL2014::VLS-COMMANDINFOLIST-P-OF-REMOVE)
(VL2014::VLS-COMMANDINFOLIST-P-OF-REVAPPEND)
(VL2014::GET-VLS-COMMANDS)
(VL2014::VLS-COMMAND-ARG-TO-EFORMAL)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-EXEC)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-NREV)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-NIL-PRESERVINGP-LEMMA)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-OF-UPDATE-NTH
 (10 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (10 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (10 5 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (5 5 (:REWRITE CONSP-BY-LEN))
 (5 5 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (2 2 (:REWRITE CONSP-OF-CDR-BY-LEN))
 )
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-OF-REVAPPEND)
(VL2014::NTHCDR-OF-VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::NTH-OF-VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-NREV-REMOVAL
 (262 5 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (231 3 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
 (93 3 (:REWRITE |(equal 0 (len x))|))
 (90 3 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (90 3 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (90 3 (:REWRITE LEN-WHEN-ATOM))
 (51 3 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (42 3 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (36 3 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (34 34 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (34 34 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (34 17 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (26 26 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (18 3 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (17 17 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (17 17 (:REWRITE CONSP-BY-LEN))
 (12 6 (:REWRITE SYMBOL-LISTP-WHEN-SUBSETP-EQUAL))
 (12 3 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (9 3 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (6 6 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (6 6 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (6 6 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (6 6 (:REWRITE VL2014::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE))
 (6 6 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (6 6 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:LINEAR LOWER-BOUND-OF-LEN-WHEN-SUBLISTP))
 (6 6 (:LINEAR LISTPOS-UPPER-BOUND-STRONG-2))
 (6 6 (:LINEAR LEN-WHEN-PREFIXP))
 (6 3 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (6 3 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (6 3 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (6 3 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LIST*P))
 (6 3 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LIST*P))
 (6 3 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LIST*P))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (3 3 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 3 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (3 3 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (3 3 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (3 3 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (3 3 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (3 3 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE SET::IN-SET))
 (3 3 (:REWRITE FN-CHECK-DEF-FORMALS))
 (3 3 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (3 3 (:LINEAR LEQ-POSITION-EQUAL-LEN))
 (3 3 (:LINEAR VL2014::LEN-WHEN-VL-MATCHES-STRING-P-FC))
 (3 3 (:LINEAR INDEX-OF-<-LEN))
 (3 3 (:LINEAR STR::COUNT-LEADING-CHARSET-LEN))
 (2 2 (:TYPE-PRESCRIPTION TYPE-OF-RCONS))
 (2 2 (:REWRITE CONSP-OF-CDR-BY-LEN))
 )
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-EXEC-REMOVAL
 (10 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (10 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (10 5 (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
 (5 5 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (5 5 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (5 5 (:REWRITE CONSP-BY-LEN))
 (5 5 (:REWRITE CAR-WHEN-ALL-EQUALP))
 (2 2 (:REWRITE CONSP-OF-CDR-BY-LEN))
 )
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-OF-TAKE)
(VL2014::SET-EQUIV-CONGRUENCE-OVER-VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::SUBSETP-OF-VLS-COMMAND-ARGS-TO-EFORMALS-WHEN-SUBSETP)
(VL2014::MEMBER-OF-VLS-COMMAND-ARG-TO-EFORMAL-IN-VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-OF-REV)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-OF-LIST-FIX)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-OF-APPEND)
(VL2014::CDR-OF-VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::CAR-OF-VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-UNDER-IFF)
(VL2014::CONSP-OF-VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::LEN-OF-VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::TRUE-LISTP-OF-VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-WHEN-NOT-CONSP)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-OF-CONS)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-NREV
 (37 1 (:REWRITE TRUE-LISTP-WHEN-ATOM))
 (20 6 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (19 1 (:REWRITE TRUE-LISTP-WHEN-SYMBOL-LISTP-REWRITE-BACKCHAIN-1))
 (14 1 (:REWRITE TRUE-LISTP-WHEN-STRING-LISTP-REWRITE))
 (12 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (12 1 (:REWRITE TRUE-LISTP-WHEN-CHARACTER-LISTP-REWRITE))
 (11 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (8 2 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (7 6 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (6 1 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-VALS))
 (4 4 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (4 4 (:REWRITE VL2014::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE))
 (4 2 (:REWRITE VL2014::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (4 1 (:REWRITE VL2014::STRING-LISTP-WHEN-NO-NILS-IN-VL-MAYBE-STRING-LISTP))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:REWRITE VL2014::TRUE-LISTP-WHEN-MEMBER-EQUAL-OF-TRUE-LIST-LISTP))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (2 2 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE STRING-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE VL2014::STRING-LISTP-WHEN-MEMBER-EQUAL-OF-STRING-LIST-LISTP))
 (2 2 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (2 2 (:REWRITE FN-CHECK-DEF-FORMALS))
 (2 2 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-CONS-LISTP))
 (2 2 (:REWRITE CHARACTER-LISTP-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE BOOLEAN-LISTP-WHEN-SUBSETP-EQUAL))
 (2 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LIST*P))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LIST*P))
 (2 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LIST*P))
 (2 1 (:REWRITE ALIST-VALS-WHEN-ATOM))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-FULL-KEYWORD-TABLE))
 (1 1 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (1 1 (:TYPE-PRESCRIPTION CONSP-MEMBER-EQUAL))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (1 1 (:REWRITE TRUE-LISTP-WHEN-SIGNED-BYTE-LISTP))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 2))
 (1 1 (:REWRITE VL2014::STRING-LISTP-WHEN-SUBSETP-EQUAL-OF-STRING-LISTP . 1))
 (1 1 (:REWRITE STRING-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE MEMBER-SELF))
 (1 1 (:REWRITE SET::IN-SET))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEITEM-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-SCOPEDEF-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-REPORTCARD-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-IMPORTRESULT-ALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-GENCASELIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-FILEMAP-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DESCALIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-DEPGRAPH-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-COMMENTMAP-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-CASELIST-P . 1))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 2))
 (1 1 (:REWRITE VL2014::CONSP-WHEN-MEMBER-EQUAL-OF-VL-ATTS-P . 1))
 (1 1 (:REWRITE CONSP-BY-LEN))
 (1 1 (:REWRITE CHARACTER-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE BOOLEAN-LISTP-WHEN-NOT-CONSP))
 )
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS)
(VL2014::VLS-COMMAND-ARGS-TO-EFORMALS-EXEC
 (11 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (11 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (8 1 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 1))
 (6 1 (:REWRITE SYMBOL-LISTP-WHEN-BOOLEAN-LISTP))
 (4 4 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-VALS))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP-MEMBER-EQUAL))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-MEMBER-EQUAL-OF-SYMBOL-LIST-LISTP))
 (2 2 (:REWRITE VL2014::SYMBOL-LISTP-OF-ALIST-VALS-OF-VL-FULL-KEYWORD-TABLE))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE BOOLEAN-LISTP-WHEN-SUBSETP-EQUAL))
 (2 1 (:REWRITE VL2014::MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-UNDER-IFF))
 (2 1 (:REWRITE ALIST-VALS-WHEN-ATOM))
 (1 1 (:TYPE-PRESCRIPTION VL2014::VL-FULL-KEYWORD-TABLE))
 (1 1 (:REWRITE VL2014::SYMBOL-LISTP-WHEN-SUBSETP-EQUAL-OF-SYMBOL-LISTP . 2))
 (1 1 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-MEMBER . 2))
 (1 1 (:REWRITE SUBSETP-MEMBER . 1))
 (1 1 (:REWRITE MEMBER-SELF))
 (1 1 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
 (1 1 (:REWRITE FN-CHECK-DEF-FORMALS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE BOOLEAN-LISTP-WHEN-NOT-CONSP))
 )
(VL2014::DEFINE-VLS-COMMAND-FN)
(VL2014::TESTCMD0)
(VL2014::STRINGP-OF-TESTCMD0)
(VL2014::TESTCMD1)
(VL2014::STRINGP-OF-TESTCMD1)
(VL2014::TESTCMD2)
(VL2014::STRINGP-OF-TESTCMD2)
