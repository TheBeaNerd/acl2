(YUL::IS-TREE-RULENAME?)
(YUL::BOOLEANP-OF-IS-TREE-RULENAME?)
(YUL::CHECK-AND-DEREF-TREE-LEXEME?
 (56 4 (:DEFINITION LEN))
 (23 2 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (12 12 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-REPETITION-SYMBOL-ALISTP . 2))
 (12 12 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-REPETITION-SYMBOL-ALISTP . 1))
 (12 12 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-ALTERNATION-SYMBOL-ALISTP . 2))
 (12 12 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-ALTERNATION-SYMBOL-ALISTP . 1))
 (8 8 (:REWRITE ABNF::TREEP-WHEN-MEMBER-EQUAL-OF-TREE-LISTP))
 (8 4 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (7 7 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (7 7 (:REWRITE YUL::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P))
 (4 4 (:REWRITE ABNF::TREE-LISTP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LISTP))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE YUL::ABNF-TREE-LISTP-WHEN-ABNF-TREE-LIST-WITH-ROOT-P))
 )
(YUL::TREE-RESULTP-OF-CHECK-AND-DEREF-TREE-LEXEME?)
(YUL::CHECK-AND-DEREF-TREE-TOKEN?
 (56 4 (:DEFINITION LEN))
 (23 2 (:REWRITE DEFAULT-CAR))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (12 12 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (12 12 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-REPETITION-SYMBOL-ALISTP . 2))
 (12 12 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-REPETITION-SYMBOL-ALISTP . 1))
 (12 12 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-ALTERNATION-SYMBOL-ALISTP . 2))
 (12 12 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-ALTERNATION-SYMBOL-ALISTP . 1))
 (8 8 (:REWRITE ABNF::TREEP-WHEN-MEMBER-EQUAL-OF-TREE-LISTP))
 (8 4 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (7 7 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (7 7 (:REWRITE YUL::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P))
 (4 4 (:REWRITE ABNF::TREE-LISTP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LISTP))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE YUL::ABNF-TREE-LISTP-WHEN-ABNF-TREE-LIST-WITH-ROOT-P))
 )
(YUL::TREE-RESULTP-OF-CHECK-AND-DEREF-TREE-TOKEN?)
(YUL::FILTER-AND-REDUCE-LEXEME-TREE-TO-SUBTOKEN-TREES
 (154 8 (:REWRITE ABNF::TREEP-WHEN-TREE-OPTIONP))
 (143 4 (:REWRITE ABNF::TREE-OPTIONP-WHEN-TREEP))
 (132 1 (:DEFINITION YUL::FILTER-AND-REDUCE-LEXEME-TREE-TO-SUBTOKEN-TREES))
 (72 6 (:DEFINITION MEMBER-EQUAL))
 (67 13 (:REWRITE FTY::RESULTERRP-WHEN-RESULTERR-OPTIONP))
 (48 6 (:REWRITE FTY::RESULTERR-OPTIONP-WHEN-RESULTERRP))
 (31 4 (:REWRITE ABNF::TREE-LISTP-WHEN-NOT-CONSP))
 (24 3 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (20 20 (:REWRITE ABNF::TREE-LISTP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LISTP))
 (18 18 (:TYPE-PRESCRIPTION FTY::RESULTERR-OPTIONP))
 (14 14 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (14 14 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (14 14 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-REPETITION-SYMBOL-ALISTP . 2))
 (14 14 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-REPETITION-SYMBOL-ALISTP . 1))
 (14 14 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-ALTERNATION-SYMBOL-ALISTP . 2))
 (14 14 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-ALTERNATION-SYMBOL-ALISTP . 1))
 (12 12 (:REWRITE SUBSETP-MEMBER . 2))
 (12 12 (:REWRITE SUBSETP-MEMBER . 1))
 (11 11 (:TYPE-PRESCRIPTION ABNF::TREE-OPTIONP))
 (10 10 (:REWRITE YUL::ABNF-TREE-LISTP-WHEN-ABNF-TREE-LIST-WITH-ROOT-P))
 (9 9 (:REWRITE SUBSETP-TRANS2))
 (9 9 (:REWRITE SUBSETP-TRANS))
 (8 8 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (8 8 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (8 8 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE YUL::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P))
 (3 3 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 )
(YUL::TREE-LIST-RESULTP-OF-FILTER-AND-REDUCE-LEXEME-TREE-TO-SUBTOKEN-TREES
 (281 51 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (243 51 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (225 15 (:DEFINITION MEMBER-EQUAL))
 (224 16 (:REWRITE ABNF::TREEP-WHEN-MEMBER-EQUAL-OF-TREE-LISTP))
 (124 124 (:REWRITE ABNF::TREE-LISTP-WHEN-MEMBER-EQUAL-OF-TREE-LIST-LISTP))
 (112 112 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 2))
 (112 112 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-SYMBOL-SYMBOL-ALISTP . 1))
 (112 112 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-REPETITION-SYMBOL-ALISTP . 2))
 (112 112 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-REPETITION-SYMBOL-ALISTP . 1))
 (112 112 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-ALTERNATION-SYMBOL-ALISTP . 2))
 (112 112 (:REWRITE ABNF::CONSP-WHEN-MEMBER-EQUAL-OF-ALTERNATION-SYMBOL-ALISTP . 1))
 (78 78 (:REWRITE DEFAULT-CAR))
 (71 2 (:REWRITE SUBSETP-OF-CONS))
 (63 63 (:REWRITE SUBSETP-TRANS2))
 (63 63 (:REWRITE SUBSETP-TRANS))
 (62 62 (:REWRITE YUL::ABNF-TREE-LISTP-WHEN-ABNF-TREE-LIST-WITH-ROOT-P))
 (61 61 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (32 32 (:REWRITE DEFAULT-CDR))
 (30 30 (:REWRITE SUBSETP-MEMBER . 2))
 (30 30 (:REWRITE SUBSETP-MEMBER . 1))
 (10 10 (:REWRITE ABNF::TREEP-WHEN-PARSE-TREEP))
 (10 10 (:REWRITE ABNF::TREEP-WHEN-IN-TREE-SETP-BINDS-FREE-X))
 (10 10 (:REWRITE YUL::ABNF-TREEP-WHEN-ABNF-TREE-WITH-ROOT-P))
 )
(YUL::TOKENIZE-YUL)
(YUL::TREE-LIST-RESULTP-OF-TOKENIZE-YUL)
(YUL::TOKENIZE-YUL-BYTES)
(YUL::TREE-LIST-RESULTP-OF-TOKENIZE-YUL-BYTES)
(YUL::SUBTOKEN-TREEP)
(YUL::SUBTOKEN-TREE-LISTP)
