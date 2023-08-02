(CAR-OF-APPEND
 (69 69 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (45 15 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
(CDR-OF-APPEND
 (54 27 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (27 27 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (27 27 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (16 7 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(LEN-OF-APPEND
 (48 24 (:REWRITE DEFAULT-+-2))
 (31 24 (:REWRITE DEFAULT-+-1))
 (26 23 (:REWRITE DEFAULT-CDR))
 (24 4 (:REWRITE CDR-OF-APPEND))
 (20 10 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (7 7 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(APPEND-OF-NIL-ARG1
 (22 11 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (11 11 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (11 11 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(APPEND-WHEN-NOT-CONSP-ARG1
 (38 19 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (19 19 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (19 19 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(APPEND-WHEN-NOT-CONSP-ARG1-CHEAP
 (38 19 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (19 19 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (19 19 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(APPEND-OF-NIL-ARG2
 (62 12 (:DEFINITION TRUE-LISTP))
 (54 54 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (45 5 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (45 5 (:REWRITE APPEND-TO-NIL))
 (18 18 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(TRUE-LISTP-OF-APPEND
 (230 115 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (115 115 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (20 20 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-CAR))
 )
(APPEND-ASSOCIATIVE
 (1550 625 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (827 625 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (625 625 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (27 24 (:REWRITE DEFAULT-CAR))
 (23 20 (:REWRITE DEFAULT-CDR))
 (20 5 (:REWRITE CDR-OF-APPEND))
 (15 5 (:REWRITE CAR-OF-APPEND))
 )
(CONSP-OF-APPEND
 (224 112 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (112 112 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (112 112 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
(APPEND-OF-CONS-ARG1
 (22 22 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (6 6 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(TRUE-LIST-FIX-OF-APPEND
 (93 9 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (52 52 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (40 8 (:DEFINITION TRUE-LISTP))
 (28 4 (:REWRITE TRUE-LISTP-OF-APPEND))
 (21 9 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (12 12 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 )
(APPEND-IFF
 (176 88 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (88 88 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (8 8 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE DEFAULT-CDR))
 )
(NOT-EQUAL-WHEN-LENS-NOT-EQUAL)
(EQUAL-OF-APPEND-SAME-ARG1-WHEN-TRUE-LISTP
 (16 13 (:REWRITE DEFAULT-CDR))
 (10 7 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 )
(EQUAL-OF-APPEND-SAME-ARG2
 (64 32 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (32 32 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (19 9 (:REWRITE DEFAULT-+-2))
 (12 9 (:REWRITE DEFAULT-CDR))
 (11 9 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(EQUAL-OF-APPEND-AND-APPEND-SAME-ARG1
 (636 318 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (318 318 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (318 318 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (18 12 (:REWRITE DEFAULT-CAR))
 (16 10 (:REWRITE DEFAULT-CDR))
 )
(NTHCDR-OF-LEN-AND-APPEND
 (44 22 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (25 5 (:DEFINITION LEN))
 (22 22 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (15 9 (:REWRITE DEFAULT-+-2))
 (15 1 (:DEFINITION NTHCDR))
 (10 9 (:REWRITE DEFAULT-+-1))
 (8 6 (:REWRITE DEFAULT-<-1))
 (8 1 (:REWRITE NTHCDR-OF-LEN-SAME-WHEN-TRUE-LISTP))
 (7 6 (:REWRITE DEFAULT-<-2))
 (5 1 (:DEFINITION TRUE-LISTP))
 (4 1 (:DEFINITION POSP))
 (4 1 (:DEFINITION NTH))
 (3 3 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (3 1 (:REWRITE COMMUTATIVITY-OF-+))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(TAKE-OF-LEN-AND-APPEND
 (20 4 (:DEFINITION LEN))
 (18 4 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 5 (:REWRITE DEFAULT-+-2))
 (10 2 (:DEFINITION TRUE-LISTP))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (4 2 (:REWRITE DEFAULT-<-1))
 (4 1 (:DEFINITION BINARY-APPEND))
 (3 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (2 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(APPEND-OF-TRUE-LIST-FIX-ARG1
 (159 159 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (45 5 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (31 6 (:DEFINITION TRUE-LISTP))
 (11 11 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 )
(EQUAL-OF-APPEND
 (2253 788 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (315 63 (:DEFINITION LEN))
 (187 21 (:REWRITE NTHCDR-WHEN-NOT-POSP))
 (153 20 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (129 8 (:REWRITE TAKE-DOES-NOTHING))
 (128 64 (:REWRITE DEFAULT-+-2))
 (124 14 (:DEFINITION POSP))
 (95 19 (:DEFINITION TRUE-LISTP))
 (82 82 (:REWRITE DEFAULT-CDR))
 (65 64 (:REWRITE DEFAULT-+-1))
 (48 36 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (47 24 (:REWRITE DEFAULT-<-2))
 (35 24 (:REWRITE DEFAULT-<-1))
 (21 21 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (21 21 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (20 20 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (14 14 (:TYPE-PRESCRIPTION POSP))
 )
(EQUAL-OF-APPEND-AND-APPEND-WHEN-EQUAL-OF-LEN-AND-LEN
 (80 40 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (50 50 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (40 40 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (18 4 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (16 8 (:REWRITE DEFAULT-+-2))
 (10 2 (:DEFINITION TRUE-LISTP))
 (9 9 (:REWRITE DEFAULT-CDR))
 (9 8 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (3 1 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (2 1 (:REWRITE DEFAULT-<-2))
 )
(LAST-OF-APPEND
 (122 16 (:REWRITE CDR-OF-APPEND))
 (75 50 (:REWRITE DEFAULT-CAR))
 )
(EQUAL-OF-APPEND-AND-APPEND-SAME-ARG2
 (275 26 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (191 96 (:REWRITE DEFAULT-+-2))
 (125 25 (:DEFINITION TRUE-LISTP))
 (110 96 (:REWRITE DEFAULT-+-1))
 (100 100 (:REWRITE DEFAULT-CDR))
 (74 3 (:REWRITE TRUE-LISTP-OF-NTHCDR-3))
 (70 41 (:REWRITE DEFAULT-<-1))
 (69 41 (:REWRITE DEFAULT-<-2))
 (62 7 (:DEFINITION POSP))
 (35 26 (:REWRITE TRUE-LIST-FIX-WHEN-NOT-CONS-CHEAP))
 (22 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (22 1 (:REWRITE EQUAL-OF-APPEND-AND-APPEND-WHEN-EQUAL-OF-LEN-AND-LEN))
 (9 9 (:REWRITE NTHCDR-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:REWRITE NTHCDR-WHEN-EQUAL-OF-LEN))
 (7 7 (:TYPE-PRESCRIPTION POSP))
 (7 4 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 )
(<=-OF-ACL2-COUNT-OF-APPEND-LINEAR
 (518 253 (:REWRITE DEFAULT-+-2))
 (362 253 (:REWRITE DEFAULT-+-1))
 (135 27 (:DEFINITION LEN))
 (89 66 (:REWRITE DEFAULT-<-1))
 (79 66 (:REWRITE DEFAULT-<-2))
 (69 66 (:REWRITE DEFAULT-CDR))
 (67 67 (:REWRITE FOLD-CONSTS-IN-+))
 (54 54 (:REWRITE DEFAULT-UNARY-MINUS))
 (48 24 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (48 2 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (44 7 (:REWRITE CDR-OF-APPEND))
 (43 40 (:REWRITE DEFAULT-CAR))
 (27 27 (:REWRITE DEFAULT-NUMERATOR))
 (27 27 (:REWRITE DEFAULT-DENOMINATOR))
 (27 27 (:REWRITE DEFAULT-COERCE-2))
 (27 27 (:REWRITE DEFAULT-COERCE-1))
 (26 26 (:REWRITE DEFAULT-REALPART))
 (26 26 (:REWRITE DEFAULT-IMAGPART))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (24 24 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (19 7 (:REWRITE CAR-OF-APPEND))
 (7 7 (:REWRITE CONSP-OF-APPEND))
 )
(ACL2-COUNT-OF-APPEND-OF-CONS)
(ACL2-COUNT-OF-APPEND-OF-CONS-LINEAR)
