(ALISTS-EQUIV-ON
 (28 14 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (14 14 (:TYPE-PRESCRIPTION ALISTP))
 )
(ALISTS-EQUIV-ON-SAME
 (56 11 (:REWRITE DEFAULT-CDR))
 (30 3 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (18 9 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (18 3 (:DEFINITION ALISTP))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 )
(ALISTS-EQUIV-ON-OF-UNION-EQUAL
 (3552 1731 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (2776 419 (:REWRITE DEFAULT-CDR))
 (1550 150 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (900 150 (:DEFINITION ALISTP))
 (318 314 (:REWRITE DEFAULT-CAR))
 (159 159 (:TYPE-PRESCRIPTION UNION-EQUAL))
 (150 150 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 )
(ALISTS-EQUIV-ON-OF-CONS-AND-CONS-SAME
 (328 46 (:REWRITE DEFAULT-CDR))
 (140 14 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (84 14 (:DEFINITION ALISTP))
 (45 45 (:REWRITE DEFAULT-CAR))
 (26 26 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 )
(ALISTS-EQUIV-ON-OF-CONS-AND-CONS-SAME-2
 (1314 211 (:REWRITE DEFAULT-CDR))
 (688 66 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (396 66 (:DEFINITION ALISTP))
 (78 78 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 )
(EQUAL-OF-CDR-OF-ASSOC-EQUAL-AND-CDR-OF-ASSOC-EQUAL-WHEN-ALISTS-EQUIV-ON
 (732 366 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (312 42 (:REWRITE DEFAULT-CDR))
 (180 18 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (108 18 (:DEFINITION ALISTP))
 (30 30 (:REWRITE DEFAULT-CAR))
 (18 18 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 )
(CDR-REMOVE-CAAR-INDUCT)
(ALISTS-EQUIV-ON-OF-APPEND-AND-APPEND-SAME
 (1390 308 (:REWRITE DEFAULT-CDR))
 (690 11 (:DEFINITION REMOVE-EQUAL))
 (596 54 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (454 64 (:DEFINITION MEMBER-EQUAL))
 (388 305 (:REWRITE DEFAULT-CAR))
 (336 32 (:REWRITE CONSP-OF-SET-DIFFERENCE-EQUAL))
 (288 32 (:DEFINITION SUBSETP-EQUAL))
 (224 16 (:REWRITE CAR-OF-SET-DIFFERENCE-EQUAL-WHEN-NOT-MEMBER-EQUAL-OF-CAR))
 (191 23 (:REWRITE EQUAL-OF-CDR-OF-ASSOC-EQUAL-AND-CDR-OF-ASSOC-EQUAL-WHEN-ALISTS-EQUIV-ON))
 (190 190 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (170 170 (:TYPE-PRESCRIPTION STRIP-CARS))
 (74 62 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (72 72 (:TYPE-PRESCRIPTION SET-DIFFERENCE-EQUAL))
 (64 32 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (54 2 (:REWRITE MEMBER-EQUAL-OF-SET-DIFFERENCE-EQUAL))
 (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (32 32 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (18 4 (:REWRITE ASSOC-EQUAL-OF-APPEND-2))
 (16 16 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (16 4 (:REWRITE ASSOC-EQUAL-OF-APPEND-1))
 (12 6 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 )
(ALISTS-EQUIV-ON-OF-CONS-SAME
 (659 83 (:REWRITE DEFAULT-CDR))
 (340 34 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (204 34 (:DEFINITION ALISTP))
 (82 64 (:REWRITE DEFAULT-CAR))
 (42 42 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE EQUAL-OF-CDR-OF-ASSOC-EQUAL-AND-CDR-OF-ASSOC-EQUAL-WHEN-ALISTS-EQUIV-ON))
 )
