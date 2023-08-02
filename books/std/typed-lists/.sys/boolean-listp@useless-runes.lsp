(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(BOOLEAN-LISTP-OF-CONS)
(BOOLEAN-LISTP-OF-CDR-WHEN-BOOLEAN-LISTP)
(BOOLEAN-LISTP-WHEN-NOT-CONSP)
(BOOLEANP-OF-CAR-WHEN-BOOLEAN-LISTP
 (3 3 (:REWRITE BOOLEAN-LISTP-WHEN-NOT-CONSP))
 )
(TRUE-LISTP-WHEN-BOOLEAN-LISTP-COMPOUND-RECOGNIZER)
(BOOLEAN-LISTP-OF-LIST-FIX)
(BOOLEAN-LISTP-OF-SFIX)
(BOOLEAN-LISTP-OF-INSERT)
(BOOLEAN-LISTP-OF-DELETE)
(BOOLEAN-LISTP-OF-MERGESORT)
(BOOLEAN-LISTP-OF-UNION)
(BOOLEAN-LISTP-OF-INTERSECT-1)
(BOOLEAN-LISTP-OF-INTERSECT-2)
(BOOLEAN-LISTP-OF-DIFFERENCE)
(BOOLEAN-LISTP-OF-DUPLICATED-MEMBERS)
(BOOLEAN-LISTP-OF-REV)
(BOOLEAN-LISTP-OF-APPEND)
(BOOLEAN-LISTP-OF-RCONS)
(BOOLEANP-WHEN-MEMBER-EQUAL-OF-BOOLEAN-LISTP)
(BOOLEAN-LISTP-WHEN-SUBSETP-EQUAL)
(BOOLEAN-LISTP-OF-SET-DIFFERENCE-EQUAL)
(BOOLEAN-LISTP-OF-INTERSECTION-EQUAL-1)
(BOOLEAN-LISTP-OF-INTERSECTION-EQUAL-2)
(BOOLEAN-LISTP-OF-UNION-EQUAL)
(BOOLEAN-LISTP-OF-TAKE)
(BOOLEAN-LISTP-OF-REPEAT)
(BOOLEANP-OF-NTH-WHEN-BOOLEAN-LISTP
 (12 12 (:REWRITE BOOLEAN-LISTP-WHEN-SUBSETP-EQUAL))
 (6 6 (:REWRITE BOOLEAN-LISTP-WHEN-NOT-CONSP))
 (2 2 (:REWRITE BOOLEANP-WHEN-MEMBER-EQUAL-OF-BOOLEAN-LISTP))
 )
(BOOLEAN-LISTP-OF-UPDATE-NTH)
(BOOLEAN-LISTP-OF-BUTLAST)
(BOOLEAN-LISTP-OF-NTHCDR)
(BOOLEAN-LISTP-OF-LAST)
(BOOLEAN-LISTP-OF-REMOVE)
(BOOLEAN-LISTP-OF-REVAPPEND)
(BOOLEAN-LISTP-OF-REMOVE-EQUAL)
(BOOLEAN-LISTP-OF-MAKE-LIST-AC
 (17 17 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (17 1 (:DEFINITION BINARY-APPEND))
 (16 4 (:REWRITE BOOLEANP-WHEN-MEMBER-EQUAL-OF-BOOLEAN-LISTP))
 (12 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (10 4 (:REWRITE CONSP-OF-REPEAT))
 (8 1 (:DEFINITION MEMBER-EQUAL))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE BOOLEAN-LISTP-WHEN-SUBSETP-EQUAL))
 (5 5 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (5 2 (:REWRITE DEFAULT-CDR))
 (5 2 (:REWRITE DEFAULT-CAR))
 (4 4 (:TYPE-PRESCRIPTION MAKE-LIST-AC))
 (4 1 (:REWRITE REPEAT-WHEN-ZP))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE BOOLEAN-LISTP-WHEN-NOT-CONSP))
 )
(EQABLE-LISTP-WHEN-BOOLEAN-LISTP)
(SYMBOL-LISTP-WHEN-BOOLEAN-LISTP)
