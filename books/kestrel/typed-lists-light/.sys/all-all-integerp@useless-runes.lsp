(ALL-ALL-INTEGERP)
(ALL-ALL-INTEGERP-OF-CONS)
(USE-ALL-ALL-INTEGERP-FOR-CAR)
(USE-ALL-ALL-INTEGERP-FOR-CAR-OF-LAST)
(ALL-ALL-INTEGERP-OF-APPEND)
(ALL-ALL-INTEGERP-OF-UNION-EQUAL)
(ALL-ALL-INTEGERP-WHEN-NOT-CONSP)
(ALL-ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP)
(ALL-ALL-INTEGERP-OF-REVAPPEND)
(ALL-ALL-INTEGERP-OF-CDR)
(ALL-ALL-INTEGERP-OF-NTHCDR)
(ALL-ALL-INTEGERP-OF-FIRSTN)
(ALL-ALL-INTEGERP-OF-REMOVE1-EQUAL)
(ALL-ALL-INTEGERP-OF-REMOVE-EQUAL)
(ALL-ALL-INTEGERP-OF-LAST)
(ALL-ALL-INTEGERP-OF-TAKE)
(ALL-ALL-INTEGERP-WHEN-PERM)
(ALL-ALL-INTEGERP-OF-TRUE-LIST-FIX)
(PERM-IMPLIES-EQUAL-ALL-ALL-INTEGERP-1)
(USE-ALL-ALL-INTEGERP)
(USE-ALL-ALL-INTEGERP-2)
(ALL-ALL-INTEGERP-OF-ADD-TO-SET-EQUAL)
(ALL-INTEGERP-OF-CAR
 (6 2 (:REWRITE USE-ALL-ALL-INTEGERP))
 (4 4 (:TYPE-PRESCRIPTION MEMBERP))
 (2 2 (:REWRITE USE-ALL-ALL-INTEGERP-FOR-CAR))
 (2 2 (:REWRITE USE-ALL-ALL-INTEGERP-2))
 (2 2 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE ALL-ALL-INTEGERP-WHEN-NOT-CONSP))
 )
