(BOOLIF)
(BOOLEANP-OF-BOOLIF)
(BOOLIF-WHEN-QUOTEP-ARG1
 (6 2 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(BOOLIF-OF-T-AND-NIL-WHEN-BOOLEANP
 (1 1 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-OF-T-AND-NIL
 (3 1 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-OF-NIL-AND-T
 (1 1 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-SAME-BRANCHES
 (3 1 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-SAME-ARG1-ARG2
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-X-Y-X
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-OF-NOT
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(NOT-OF-BOOLIF
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-OF-BOOL-FIX-ARG1
 (3 1 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-OF-BOOL-FIX-ARG2
 (6 2 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-OF-BOOL-FIX-ARG3
 (6 2 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-OF-NOT-SAME-ARG3-ALT
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-OF-NOT-SAME-ARG2-ALT
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(IF-BECOMES-BOOLIF
 (1 1 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(IFF-IMPLIES-EQUAL-BOOLIF-1
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(IFF-IMPLIES-EQUAL-BOOLIF-2
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(IFF-IMPLIES-EQUAL-BOOLIF-3
 (2 2 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-WHEN-NOT-NIL
 (4 2 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(BOOLIF-WHEN-NIL
 (4 2 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(BOOLIF-OF-IF-ARG1)
(BOOLIF-OF-IF-ARG2
 (8 4 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(BOOLIF-OF-IF-ARG3
 (8 4 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(BOOLIF-OF-EQUAL-AND-NIL-AND-EQUAL-DIFF
 (1 1 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
(BOOLIF-OF-BOOLIF-OF-T-AND-NIL
 (3 1 (:REWRITE BOOL-FIX-WHEN-BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE BOOLIF-SAME-ARG1-ARG2))
 )
(BOOLIF-COMBINE-1
 (6 6 (:REWRITE BOOLIF-WHEN-QUOTEP-ARG1))
 )
