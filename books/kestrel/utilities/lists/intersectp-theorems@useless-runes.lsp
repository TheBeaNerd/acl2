(INTERSECTP-APPEND-LEFT
     (369 28 (:DEFINITION MEMBER-EQUAL))
     (186 5 (:REWRITE MEMBER-OF-APPEND))
     (80 40
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (68 68 (:REWRITE INTERSECTP-MEMBER . 1))
     (65 65
         (:REWRITE INTERSECTP-EQUAL-OF-ATOM-RIGHT))
     (63 42 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (61 61 (:REWRITE SUBSETP-MEMBER . 2))
     (61 61 (:REWRITE SUBSETP-MEMBER . 1))
     (58 58 (:REWRITE DEFAULT-CDR))
     (48 48 (:REWRITE DEFAULT-CAR))
     (44 44 (:REWRITE SUBSETP-TRANS2))
     (44 44 (:REWRITE SUBSETP-TRANS))
     (42 42 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (42 3
         (:REWRITE SUBSETP-OF-APPEND-WHEN-SUBSET-OF-EITHER))
     (40 40 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (40 40 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (30 30
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (20 20 (:REWRITE CONSP-OF-APPEND))
     (13 13 (:REWRITE SUBSETP-MEMBER . 4))
     (13 13 (:REWRITE INTERSECTP-MEMBER . 2))
     (12 12 (:REWRITE MEMBER-WHEN-ATOM)))
(INTERSECTP-APPEND-RIGHT
     (453 32 (:DEFINITION MEMBER-EQUAL))
     (262 6 (:REWRITE MEMBER-OF-APPEND))
     (259 68 (:REWRITE INTERSECTP-MEMBER . 1))
     (132 70 (:REWRITE SUBSETP-MEMBER . 1))
     (90 62 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (84 42
         (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (70 70 (:REWRITE SUBSETP-MEMBER . 2))
     (70 5
         (:REWRITE SUBSETP-OF-APPEND-WHEN-SUBSET-OF-EITHER))
     (64 64 (:REWRITE SUBSETP-TRANS2))
     (64 64 (:REWRITE SUBSETP-TRANS))
     (64 64
         (:REWRITE INTERSECTP-EQUAL-OF-ATOM-LEFT))
     (62 62 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (62 62 (:REWRITE DEFAULT-CDR))
     (52 52 (:REWRITE DEFAULT-CAR))
     (42 42 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (42 42 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (30 30
         (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (21 21 (:REWRITE CONSP-OF-APPEND))
     (14 14 (:REWRITE INTERSECTP-MEMBER . 3))
     (13 13 (:REWRITE SUBSETP-MEMBER . 4))
     (12 12 (:REWRITE MEMBER-WHEN-ATOM)))
