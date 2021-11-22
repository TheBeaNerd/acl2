(SYMBOL-BTREEP
 (332 146 (:REWRITE DEFAULT-+-2))
 (206 146 (:REWRITE DEFAULT-+-1))
 (80 20 (:DEFINITION INTEGER-ABS))
 (80 10 (:DEFINITION LENGTH))
 (56 56 (:REWRITE DEFAULT-CDR))
 (50 10 (:DEFINITION LEN))
 (49 49 (:REWRITE DEFAULT-CAR))
 (41 27 (:REWRITE DEFAULT-<-2))
 (32 27 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (10 10 (:REWRITE DEFAULT-REALPART))
 (10 10 (:REWRITE DEFAULT-NUMERATOR))
 (10 10 (:REWRITE DEFAULT-IMAGPART))
 (10 10 (:REWRITE DEFAULT-DENOMINATOR))
 (10 10 (:REWRITE DEFAULT-COERCE-2))
 (10 10 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-BTREE-UPDATE
 (1418 654 (:REWRITE DEFAULT-+-2))
 (920 654 (:REWRITE DEFAULT-+-1))
 (560 140 (:DEFINITION INTEGER-ABS))
 (560 70 (:DEFINITION LENGTH))
 (350 70 (:DEFINITION LEN))
 (214 162 (:REWRITE DEFAULT-<-2))
 (180 162 (:REWRITE DEFAULT-<-1))
 (144 28 (:REWRITE SYMBOL<-ASYMMETRIC))
 (140 140 (:REWRITE DEFAULT-UNARY-MINUS))
 (82 54 (:REWRITE SYMBOL<-TRICHOTOMY))
 (70 70 (:TYPE-PRESCRIPTION LEN))
 (70 70 (:REWRITE DEFAULT-REALPART))
 (70 70 (:REWRITE DEFAULT-NUMERATOR))
 (70 70 (:REWRITE DEFAULT-IMAGPART))
 (70 70 (:REWRITE DEFAULT-DENOMINATOR))
 (70 70 (:REWRITE DEFAULT-COERCE-2))
 (70 70 (:REWRITE DEFAULT-COERCE-1))
 (54 54 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOL-BTREEP-SYMBOL-BTREE-UPDATE
 (187 143 (:REWRITE DEFAULT-CDR))
 (58 58 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOL-BTREE-FIND
 (1418 654 (:REWRITE DEFAULT-+-2))
 (920 654 (:REWRITE DEFAULT-+-1))
 (560 140 (:DEFINITION INTEGER-ABS))
 (560 70 (:DEFINITION LENGTH))
 (350 70 (:DEFINITION LEN))
 (214 162 (:REWRITE DEFAULT-<-2))
 (180 162 (:REWRITE DEFAULT-<-1))
 (144 28 (:REWRITE SYMBOL<-ASYMMETRIC))
 (140 140 (:REWRITE DEFAULT-UNARY-MINUS))
 (82 54 (:REWRITE SYMBOL<-TRICHOTOMY))
 (70 70 (:TYPE-PRESCRIPTION LEN))
 (70 70 (:REWRITE DEFAULT-REALPART))
 (70 70 (:REWRITE DEFAULT-NUMERATOR))
 (70 70 (:REWRITE DEFAULT-IMAGPART))
 (70 70 (:REWRITE DEFAULT-DENOMINATOR))
 (70 70 (:REWRITE DEFAULT-COERCE-2))
 (70 70 (:REWRITE DEFAULT-COERCE-1))
 (54 54 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOL-BTREE-LOOKUP)
(SYMBOL-BTREE-FIND-SYMBOL-BTREE-UPDATE)
(SYMBOL-BTREE-TO-ALIST-AUX
 (394 182 (:REWRITE DEFAULT-+-2))
 (254 182 (:REWRITE DEFAULT-+-1))
 (144 36 (:REWRITE COMMUTATIVITY-OF-+))
 (144 36 (:DEFINITION INTEGER-ABS))
 (144 18 (:DEFINITION LENGTH))
 (90 18 (:DEFINITION LEN))
 (62 46 (:REWRITE DEFAULT-<-2))
 (54 46 (:REWRITE DEFAULT-<-1))
 (36 36 (:REWRITE DEFAULT-UNARY-MINUS))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (18 18 (:REWRITE DEFAULT-REALPART))
 (18 18 (:REWRITE DEFAULT-NUMERATOR))
 (18 18 (:REWRITE DEFAULT-IMAGPART))
 (18 18 (:REWRITE DEFAULT-DENOMINATOR))
 (18 18 (:REWRITE DEFAULT-COERCE-2))
 (18 18 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-BTREE-TO-ALIST
 (394 182 (:REWRITE DEFAULT-+-2))
 (254 182 (:REWRITE DEFAULT-+-1))
 (144 36 (:REWRITE COMMUTATIVITY-OF-+))
 (144 36 (:DEFINITION INTEGER-ABS))
 (144 18 (:DEFINITION LENGTH))
 (90 18 (:DEFINITION LEN))
 (62 46 (:REWRITE DEFAULT-<-2))
 (54 46 (:REWRITE DEFAULT-<-1))
 (36 36 (:REWRITE DEFAULT-UNARY-MINUS))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (18 18 (:REWRITE DEFAULT-REALPART))
 (18 18 (:REWRITE DEFAULT-NUMERATOR))
 (18 18 (:REWRITE DEFAULT-IMAGPART))
 (18 18 (:REWRITE DEFAULT-DENOMINATOR))
 (18 18 (:REWRITE DEFAULT-COERCE-2))
 (18 18 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-BTREE-TO-ALIST-AUX-IS-SYMBOL-BTREE-TO-ALIST)
(TRUE-LISTP-SYMBOL-BTREE-TO-ALIST)
(SYMBOL-ALISTP-SYMBOL-BTREE-TO-ALIST
 (425 337 (:REWRITE DEFAULT-CAR))
 (346 302 (:REWRITE DEFAULT-CDR))
 )
(ALISTP-SYMBOL-BTREE-TO-ALIST)
(SYMBOL-BTREE-TO-ALIST
 (68 68 (:REWRITE DEFAULT-CDR))
 (55 55 (:REWRITE DEFAULT-CAR))
 )
(SYMBOL-ALIST-SORTEDP
 (705 288 (:REWRITE DEFAULT-+-2))
 (419 288 (:REWRITE DEFAULT-+-1))
 (184 46 (:DEFINITION INTEGER-ABS))
 (184 23 (:DEFINITION LENGTH))
 (115 23 (:DEFINITION LEN))
 (74 74 (:REWRITE DEFAULT-CDR))
 (67 52 (:REWRITE DEFAULT-<-2))
 (63 52 (:REWRITE DEFAULT-<-1))
 (46 46 (:REWRITE DEFAULT-UNARY-MINUS))
 (30 6 (:REWRITE SYMBOL<-ASYMMETRIC))
 (23 23 (:TYPE-PRESCRIPTION LEN))
 (23 23 (:REWRITE DEFAULT-REALPART))
 (23 23 (:REWRITE DEFAULT-NUMERATOR))
 (23 23 (:REWRITE DEFAULT-IMAGPART))
 (23 23 (:REWRITE DEFAULT-DENOMINATOR))
 (23 23 (:REWRITE DEFAULT-COERCE-2))
 (23 23 (:REWRITE DEFAULT-COERCE-1))
 (12 12 (:REWRITE SYMBOL<-TRICHOTOMY))
 (12 12 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOL-BTREE-FIND-THM-CAR
 (318 69 (:REWRITE SYMBOL<-ASYMMETRIC))
 (257 145 (:REWRITE SYMBOL<-TRANSITIVE))
 (199 145 (:REWRITE SYMBOL<-TRICHOTOMY))
 (36 36 (:REWRITE DEFAULT-CDR))
 )
(ASSOC-EQUAL-OF-APPEND
 (124 112 (:REWRITE DEFAULT-CAR))
 (50 25 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (40 34 (:REWRITE DEFAULT-CDR))
 (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (25 25 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(EQUAL-OF-BOOLEANS)
(SYMBOL-ALIST-SORTEDP-APPEND
 (132 132 (:TYPE-PRESCRIPTION LAST))
 )
(SYMBOL-ALIST-SORTEDP-AND-SYMBOL<-LAST-IMPLIES-NOT-ASSOC
 (151 151 (:TYPE-PRESCRIPTION LAST))
 (150 150 (:REWRITE DEFAULT-CDR))
 )
(SYMBOL-ALIST-SORTEDP-AND-SYMBOL<-FIRST-IMPLIES-NOT-ASSOC
 (969 54 (:REWRITE SYMBOL-ALIST-SORTEDP-AND-SYMBOL<-LAST-IMPLIES-NOT-ASSOC))
 (255 255 (:REWRITE DEFAULT-CDR))
 (131 43 (:DEFINITION LAST))
 (112 112 (:TYPE-PRESCRIPTION LAST))
 )
(SYMBOLP-CAAR-LAST-OF-SYMBOL-ALISTP
 (45 25 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE DEFAULT-CDR))
 )
(ASSOC-WHEN-NOT-SYMBOLP-KEY
 (172 10 (:DEFINITION SYMBOL-ALIST-SORTEDP))
 (143 8 (:REWRITE SYMBOL-ALIST-SORTEDP-AND-SYMBOL<-LAST-IMPLIES-NOT-ASSOC))
 (143 8 (:REWRITE SYMBOL-ALIST-SORTEDP-AND-SYMBOL<-FIRST-IMPLIES-NOT-ASSOC))
 (107 107 (:REWRITE DEFAULT-CAR))
 (48 48 (:REWRITE DEFAULT-CDR))
 (46 46 (:TYPE-PRESCRIPTION SYMBOL-ALIST-SORTEDP))
 (28 28 (:TYPE-PRESCRIPTION SYMBOL<))
 (14 14 (:REWRITE SYMBOL<-TRICHOTOMY))
 (14 14 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOL-BTREE-FIND-WHEN-NOT-SYMBOLP-KEY
 (110 22 (:REWRITE SYMBOL<-ASYMMETRIC))
 (53 44 (:REWRITE SYMBOL<-TRANSITIVE))
 (50 47 (:REWRITE SYMBOL<-TRICHOTOMY))
 (47 47 (:REWRITE DEFAULT-CDR))
 )
(ASSOC-IN-SYMBOL-BTREE-TO-ALIST-WHEN-SYMBOLP-KEY
 (318 318 (:REWRITE SYMBOL-BTREE-FIND-WHEN-NOT-SYMBOLP-KEY))
 (170 170 (:REWRITE ASSOC-WHEN-NOT-SYMBOLP-KEY))
 (136 96 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (8 8 (:REWRITE SYMBOL<-IRREFLEXIVE))
 )
(ASSOC-IN-SYMBOL-BTREE-TO-ALIST
 (104 2 (:DEFINITION SYMBOL-BTREE-FIND))
 (84 4 (:DEFINITION SYMBOL-BTREE-TO-ALIST))
 (78 60 (:REWRITE DEFAULT-CDR))
 (72 2 (:DEFINITION SYMBOL-ALIST-SORTEDP))
 (68 56 (:REWRITE DEFAULT-CAR))
 (60 10 (:REWRITE SYMBOL<-ASYMMETRIC))
 (52 18 (:REWRITE SYMBOL<-TRICHOTOMY))
 (40 8 (:DEFINITION BINARY-APPEND))
 (36 36 (:TYPE-PRESCRIPTION SYMBOL<))
 (22 2 (:DEFINITION SYMBOL-BTREEP))
 (18 18 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(CONSP-SYMBOL-BTREE-TO-ALIST
 (99 99 (:REWRITE DEFAULT-CAR))
 (85 19 (:DEFINITION BINARY-APPEND))
 (79 79 (:REWRITE DEFAULT-CDR))
 )
(CAR-APPEND
 (69 69 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (45 15 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE DEFAULT-CDR))
 )
(NOT-SYMBOL<-TRANSITIVE1
 (13 9 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(NOT-SYMBOL<-TRANSITIVE2
 (12 12 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOL<-TRANSITIVE1
 (2 2 (:REWRITE NOT-SYMBOL<-TRANSITIVE2))
 (1 1 (:REWRITE SYMBOL<-TRICHOTOMY))
 (1 1 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOL<-TRANSITIVE2
 (2 2 (:REWRITE SYMBOL<-TRANSITIVE1))
 (1 1 (:REWRITE SYMBOL<-TRICHOTOMY))
 (1 1 (:REWRITE SYMBOL<-TRANSITIVE))
 (1 1 (:REWRITE NOT-SYMBOL<-TRANSITIVE1))
 )
(SYMBOL<=/<-TRANSITIVE2
 (2 2 (:REWRITE SYMBOL<-TRANSITIVE2))
 (2 2 (:REWRITE SYMBOL<-TRANSITIVE1))
 (2 2 (:REWRITE NOT-SYMBOL<-TRANSITIVE2))
 (1 1 (:REWRITE SYMBOL<-TRICHOTOMY))
 (1 1 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOL</<=-TRANSITIVE1)
(SYMBOL</<=-TRANSITIVE2
 (1 1 (:REWRITE SYMBOL<=/<-TRANSITIVE2))
 (1 1 (:REWRITE SYMBOL</<=-TRANSITIVE1))
 )
(SYMBOL<=/<-TRANSITIVE1
 (1 1 (:REWRITE SYMBOL<=/<-TRANSITIVE2))
 (1 1 (:REWRITE SYMBOL</<=-TRANSITIVE2))
 (1 1 (:REWRITE SYMBOL</<=-TRANSITIVE1))
 )
(SYMBOLP-CAAR-SYMBOL-BTREE-TO-ALIST
 (164 90 (:REWRITE DEFAULT-CAR))
 (135 9 (:DEFINITION BINARY-APPEND))
 (64 61 (:REWRITE DEFAULT-CDR))
 )
(NOT-SYMBOL<-LAST-SORTED
 (313 98 (:REWRITE SYMBOL<-TRICHOTOMY))
 (101 101 (:REWRITE DEFAULT-CDR))
 )
(CAAR-SYMBOL-BTREE-UPDATE-TO-ALIST-SORTED
 (236 35 (:DEFINITION SYMBOL-ALISTP))
 (28 28 (:DEFINITION LAST))
 )
(LAST-APPEND)
(CAAR-LAST-SYMBOL-BTREE-UPDATE-TO-ALIST-SORTED
 (436 60 (:DEFINITION SYMBOL-ALISTP))
 (272 148 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (148 148 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (124 124 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(SYMBOL-ALIST-SORTEDP-SYMBOL-BTREE-UPDATE
 (134 3 (:DEFINITION SYMBOL-ALISTP))
 )
(FLOOR-X-2-NATP
 (1 1 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (1 1 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (1 1 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 )
(FLOOR-X-2-<=-X
 (26 26 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (26 26 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-*-1))
 (6 1 (:REWRITE FLOOR-=-X/Y . 3))
 (6 1 (:REWRITE FLOOR-=-X/Y . 2))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (3 1 (:REWRITE FLOOR-TYPE-4 . 2))
 (3 1 (:REWRITE FLOOR-TYPE-3 . 3))
 (3 1 (:REWRITE FLOOR-TYPE-3 . 2))
 (3 1 (:LINEAR FLOOR-TYPE-2 . 2))
 (3 1 (:LINEAR FLOOR-TYPE-2 . 1))
 (3 1 (:LINEAR FLOOR-TYPE-1 . 2))
 (1 1 (:REWRITE FLOOR-TYPE-4 . 3))
 (1 1 (:LINEAR FLOOR-TYPE-1 . 1))
 )
(FLOOR-X-2-<-X
 (26 26 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (26 26 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (12 2 (:REWRITE FLOOR-=-X/Y . 3))
 (12 2 (:REWRITE FLOOR-=-X/Y . 2))
 (10 10 (:REWRITE DEFAULT-*-2))
 (10 10 (:REWRITE DEFAULT-*-1))
 (6 2 (:REWRITE FLOOR-TYPE-3 . 2))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (3 3 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-<-1))
 (3 1 (:LINEAR FLOOR-TYPE-2 . 1))
 (2 2 (:REWRITE FLOOR-TYPE-4 . 3))
 (2 2 (:REWRITE FLOOR-TYPE-4 . 2))
 (2 2 (:REWRITE FLOOR-TYPE-3 . 3))
 (1 1 (:LINEAR FLOOR-TYPE-2 . 2))
 (1 1 (:LINEAR FLOOR-TYPE-1 . 2))
 (1 1 (:LINEAR FLOOR-TYPE-1 . 1))
 )
(SYMBOL-ALIST-TO-BTREE-AUX
 (13 6 (:REWRITE DEFAULT-<-1))
 (12 6 (:REWRITE DEFAULT-+-2))
 (7 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE ZP-OPEN))
 )
(NTHCDR-CDR
 (9 9 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (5 4 (:REWRITE DEFAULT-<-1))
 (5 2 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(CDR-NTHCDR
 (34 34 (:REWRITE DEFAULT-+-2))
 (34 34 (:REWRITE DEFAULT-+-1))
 (30 30 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (19 16 (:REWRITE ZP-OPEN))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(CAR-NTHCDR
 (59 14 (:REWRITE DEFAULT-CAR))
 (48 48 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (47 47 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (44 14 (:REWRITE ZP-OPEN))
 (38 32 (:REWRITE DEFAULT-+-2))
 (34 32 (:REWRITE DEFAULT-+-1))
 (18 6 (:REWRITE FOLD-CONSTS-IN-+))
 (18 6 (:REWRITE <-0-+-NEGATIVE-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 )
(NTHCDR-NTHCDR
 (104 104 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (72 27 (:REWRITE DEFAULT-CDR))
 (68 66 (:REWRITE DEFAULT-+-2))
 (67 66 (:REWRITE DEFAULT-+-1))
 (40 26 (:REWRITE ZP-OPEN))
 (29 23 (:REWRITE DEFAULT-<-1))
 (23 23 (:REWRITE DEFAULT-<-2))
 (10 8 (:REWRITE FOLD-CONSTS-IN-+))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 1 (:REWRITE <-0-+-NEGATIVE-1))
 )
(NTHCDR-FUDGE
 (31 31 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(SYMBOL-ALIST-TO-BTREE-AUX-IS-NTHCDR
 (337 26 (:REWRITE NTHCDR-FUDGE))
 (302 93 (:REWRITE DEFAULT-+-2))
 (292 18 (:REWRITE ZP-OPEN))
 (116 93 (:REWRITE DEFAULT-+-1))
 (89 22 (:REWRITE DEFAULT-CAR))
 (69 31 (:REWRITE DEFAULT-<-2))
 (62 4 (:REWRITE ASSOCIATIVITY-OF-+))
 (56 25 (:REWRITE DEFAULT-UNARY-MINUS))
 (47 31 (:REWRITE DEFAULT-<-1))
 (20 6 (:REWRITE <-0-+-NEGATIVE-1))
 (16 10 (:LINEAR FLOOR-X-2-<=-X))
 (4 4 (:REWRITE EQUAL-CONSTANT-+))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 )
(SYMBOL-ALISTP-NTHCDR
 (39 39 (:REWRITE DEFAULT-CAR))
 (18 16 (:REWRITE DEFAULT-+-2))
 (18 16 (:REWRITE DEFAULT-+-1))
 (18 8 (:REWRITE ZP-OPEN))
 (16 16 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (10 10 (:REWRITE DEFAULT-CDR))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:REWRITE <-0-+-NEGATIVE-1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(ALISTP-NTHCDR
 (13 13 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (12 12 (:REWRITE DEFAULT-CAR))
 (12 11 (:REWRITE DEFAULT-+-2))
 (12 11 (:REWRITE DEFAULT-+-1))
 (11 6 (:REWRITE ZP-OPEN))
 (9 9 (:REWRITE DEFAULT-CDR))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1 (:REWRITE <-0-+-NEGATIVE-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(LEN-NTHCDR
 (248 154 (:REWRITE DEFAULT-+-2))
 (173 154 (:REWRITE DEFAULT-+-1))
 (93 58 (:REWRITE DEFAULT-<-1))
 (62 58 (:REWRITE DEFAULT-<-2))
 (40 40 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (14 13 (:REWRITE DEFAULT-UNARY-MINUS))
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE EQUAL-CONSTANT-+))
 )
(SYMBOL-ALIST-SORTEDP-NTHCDR
 (148 52 (:REWRITE DEFAULT-CAR))
 (100 13 (:REWRITE SYMBOL<-ASYMMETRIC))
 (80 80 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (74 26 (:REWRITE SYMBOL<-TRICHOTOMY))
 (6 6 (:REWRITE ZP-OPEN))
 (6 2 (:REWRITE COMMUTATIVITY-OF-+))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(CONSP-NTHCDR-WHEN-ALISTP
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 )
(CONSP-CAR-NTHCDR-WHEN-ALISTP
 (219 27 (:REWRITE DEFAULT-CAR))
 (156 14 (:REWRITE CONSP-NTHCDR-WHEN-ALISTP))
 (74 74 (:REWRITE DEFAULT-+-2))
 (74 74 (:REWRITE DEFAULT-+-1))
 (58 28 (:REWRITE ZP-OPEN))
 (30 10 (:REWRITE FOLD-CONSTS-IN-+))
 (15 15 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 )
(SYMBOL-ALIST-TO-BTREE-AUX
 (59 10 (:REWRITE ZP-OPEN))
 (47 32 (:REWRITE DEFAULT-+-2))
 (35 32 (:REWRITE DEFAULT-+-1))
 (21 21 (:REWRITE DEFAULT-CDR))
 (21 14 (:REWRITE DEFAULT-<-2))
 (18 14 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 2 (:REWRITE CONSP-CAR-NTHCDR-WHEN-ALISTP))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(SYMBOLP-CAR-NTH-OF-SYMBOL-ALIST
 (26 26 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(CONSP-NTH-OF-SYMBOL-ALIST
 (32 32 (:REWRITE DEFAULT-CAR))
 (19 12 (:REWRITE DEFAULT-<-2))
 (18 11 (:REWRITE DEFAULT-+-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE ZP-OPEN))
 )
(SYMBOL-BTREEP-SYMBOL-ALIST-TO-BTREE-AUX
 (212 28 (:REWRITE ZP-OPEN))
 (104 73 (:REWRITE DEFAULT-<-2))
 (103 73 (:REWRITE DEFAULT-<-1))
 (89 12 (:DEFINITION NTH))
 (32 21 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 6 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(CONS-NTH-TAKE-NTHCDR
 (96 6 (:REWRITE TAKE-OF-LEN-FREE))
 (87 21 (:REWRITE DEFAULT-CDR))
 (52 8 (:DEFINITION LEN))
 (50 8 (:REWRITE NTHCDR-WHEN-ZP))
 (48 24 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (45 3 (:REWRITE CONSP-OF-NTHCDR))
 (37 28 (:REWRITE DEFAULT-+-2))
 (35 14 (:REWRITE ZP-OPEN))
 (29 28 (:REWRITE DEFAULT-+-1))
 (25 21 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (24 24 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (24 1 (:REWRITE LEN-OF-NTHCDR))
 (20 17 (:REWRITE DEFAULT-<-2))
 (19 17 (:REWRITE DEFAULT-<-1))
 (19 5 (:DEFINITION NFIX))
 (18 3 (:DEFINITION NTH))
 (17 5 (:REWRITE DEFAULT-CAR))
 (9 9 (:TYPE-PRESCRIPTION ZP))
 (9 3 (:REWRITE <-0-+-NEGATIVE-1))
 (8 8 (:REWRITE NTHCDR-WHEN-ATOM))
 (4 4 (:REWRITE OPEN-SMALL-NTHCDR))
 (4 1 (:REWRITE <-+-NEGATIVE-0-1))
 (3 3 (:REWRITE EQUAL-CONSTANT-+))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(TAKE-APPEND
 (407 25 (:REWRITE TAKE-OF-LEN-FREE))
 (215 31 (:DEFINITION LEN))
 (197 65 (:REWRITE DEFAULT-CDR))
 (181 181 (:TYPE-PRESCRIPTION LEN))
 (174 174 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (126 81 (:REWRITE DEFAULT-+-2))
 (123 24 (:REWRITE ZP-OPEN))
 (87 3 (:REWRITE CONSP-OF-NTHCDR))
 (85 8 (:REWRITE NTHCDR-WHEN-ZP))
 (84 81 (:REWRITE DEFAULT-+-1))
 (51 17 (:REWRITE <-0-+-NEGATIVE-1))
 (46 18 (:REWRITE DEFAULT-CAR))
 (37 34 (:REWRITE DEFAULT-<-2))
 (37 34 (:REWRITE DEFAULT-<-1))
 (34 18 (:REWRITE FOLD-CONSTS-IN-+))
 (26 4 (:REWRITE CONSP-OF-TAKE))
 (25 5 (:DEFINITION NFIX))
 (18 2 (:REWRITE CAR-OF-TAKE))
 (17 17 (:REWRITE EQUAL-CONSTANT-+))
 (15 5 (:REWRITE <-+-NEGATIVE-0-1))
 (8 8 (:REWRITE NTHCDR-WHEN-ATOM))
 (3 3 (:REWRITE NATP-RW))
 (2 2 (:TYPE-PRESCRIPTION NFIX))
 )
(CONSP-NTH-SYMBOL-ALIST
 (66 66 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (32 32 (:REWRITE DEFAULT-CAR))
 (19 12 (:REWRITE DEFAULT-<-2))
 (18 11 (:REWRITE DEFAULT-+-2))
 (13 12 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE ZP-OPEN))
 )
(CONSP-NTH-ALIST
 (60 60 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (44 4 (:REWRITE CONSP-NTH-SYMBOL-ALIST))
 (32 4 (:DEFINITION SYMBOL-ALISTP))
 (28 28 (:REWRITE DEFAULT-CAR))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (19 12 (:REWRITE DEFAULT-<-2))
 (18 11 (:REWRITE DEFAULT-+-2))
 (13 13 (:REWRITE DEFAULT-CDR))
 (13 12 (:REWRITE DEFAULT-<-1))
 (11 11 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE ZP-OPEN))
 )
(SYMBOL-BTREE-TO-ALIST-OF-SYMBOL-ALIST-TO-BTREE-AUX
 (723 39 (:REWRITE TAKE-OF-LEN-FREE))
 (102 88 (:REWRITE FOLD-CONSTS-IN-+))
 (87 51 (:REWRITE DEFAULT-UNARY-MINUS))
 (84 6 (:REWRITE CONSP-SYMBOL-BTREE-TO-ALIST))
 (81 37 (:REWRITE NTHCDR-WHEN-ZP))
 (65 20 (:DEFINITION NTH))
 (62 62 (:DEFINITION LEN))
 (54 6 (:DEFINITION SYMBOL-BTREEP))
 (48 48 (:TYPE-PRESCRIPTION SYMBOL-BTREEP))
 (37 37 (:REWRITE OPEN-SMALL-NTHCDR))
 (37 37 (:REWRITE NTHCDR-WHEN-ATOM))
 (36 22 (:LINEAR FLOOR-X-2-<=-X))
 (25 25 (:REWRITE EQUAL-CONSTANT-+))
 (24 6 (:REWRITE CONSP-OF-TAKE))
 (18 6 (:REWRITE CAR-OF-TAKE))
 (14 5 (:REWRITE UNICITY-OF-0))
 (12 12 (:DEFINITION SYMBOL-ALISTP))
 (12 6 (:REWRITE SYMBOL-BTREEP-SYMBOL-ALIST-TO-BTREE-AUX))
 (12 6 (:REWRITE CONSP-NTH-SYMBOL-ALIST))
 (2 2 (:REWRITE <-+-NEGATIVE-0-2))
 )
(LEN-EVENS-<
 (47 25 (:REWRITE DEFAULT-+-2))
 (25 25 (:REWRITE DEFAULT-+-1))
 (6 3 (:REWRITE DEFAULT-<-1))
 (5 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(LEN-EVENS-<=
 (20 10 (:REWRITE DEFAULT-+-2))
 (10 10 (:REWRITE DEFAULT-+-1))
 (6 4 (:LINEAR LEN-EVENS-<))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(MERGE-SYMBOL-ALIST-<
 (52 25 (:REWRITE DEFAULT-+-2))
 (34 25 (:REWRITE DEFAULT-+-1))
 (31 31 (:REWRITE DEFAULT-CAR))
 (28 14 (:TYPE-PRESCRIPTION TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION))
 (27 27 (:REWRITE DEFAULT-CDR))
 (12 6 (:DEFINITION TRUE-LISTP))
 (8 2 (:REWRITE SYMBOL<-ASYMMETRIC))
 (6 2 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE SYMBOL<-TRICHOTOMY))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 )
(MERGE-SORT-SYMBOL-ALIST-<
 (38 19 (:REWRITE DEFAULT-+-2))
 (32 32 (:REWRITE DEFAULT-CDR))
 (20 5 (:DEFINITION EVENS))
 (19 19 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-CAR))
 (4 2 (:REWRITE DEFAULT-<-2))
 (4 2 (:REWRITE DEFAULT-<-1))
 )
(SYMBOL-ALISTP-MERGE-SYMBOL-ALIST-<
 (152 38 (:REWRITE SYMBOL<-ASYMMETRIC))
 (129 115 (:REWRITE DEFAULT-CDR))
 (76 76 (:REWRITE SYMBOL<-TRICHOTOMY))
 )
(SYMBOL-ALISTP-EVENS
 (51 45 (:REWRITE DEFAULT-CAR))
 (25 22 (:REWRITE DEFAULT-CDR))
 )
(SYMBOL-ALISTP-MERGE-SORT-SYMBOL-ALIST-<
 (136 8 (:DEFINITION MERGE-SYMBOL-ALIST-<))
 (129 129 (:REWRITE DEFAULT-CAR))
 (95 83 (:REWRITE DEFAULT-CDR))
 (52 12 (:DEFINITION EVENS))
 (32 8 (:REWRITE SYMBOL<-ASYMMETRIC))
 (24 24 (:TYPE-PRESCRIPTION SYMBOL<))
 (22 22 (:TYPE-PRESCRIPTION EVENS))
 (22 2 (:REWRITE SYMBOL-ALISTP-MERGE-SYMBOL-ALIST-<))
 (16 16 (:REWRITE SYMBOL<-TRICHOTOMY))
 (16 16 (:DEFINITION REVAPPEND))
 )
(MERGE-SORT-SYMBOL-ALIST-<
 (39 1 (:DEFINITION MERGE-SORT-SYMBOL-ALIST-<))
 (28 28 (:REWRITE DEFAULT-CAR))
 (28 22 (:REWRITE DEFAULT-CDR))
 (18 4 (:DEFINITION EVENS))
 (17 1 (:DEFINITION MERGE-SYMBOL-ALIST-<))
 (10 10 (:TYPE-PRESCRIPTION EVENS))
 (4 1 (:REWRITE SYMBOL<-ASYMMETRIC))
 (3 3 (:TYPE-PRESCRIPTION SYMBOL<))
 (2 2 (:REWRITE SYMBOL<-TRICHOTOMY))
 (2 2 (:DEFINITION REVAPPEND))
 )
(ALISTP-WHEN-SYMBOL-ALISTP)
(SYMBOL-ALIST-TO-BTREE)
(REBALANCE-SYMBOL-BTREE)
(SYMBOL-BTREEP-REBALANCE
 (379 1 (:DEFINITION SYMBOL-ALIST-TO-BTREE-AUX))
 (268 2 (:REWRITE SYMBOL-ALIST-TO-BTREE-AUX-IS-NTHCDR))
 (202 1 (:REWRITE NTHCDR-OF-CDR))
 (174 174 (:TYPE-PRESCRIPTION FLOOR-X-2-NATP))
 (144 33 (:REWRITE DEFAULT-CDR))
 (139 1 (:REWRITE NTHCDR-OF-NTHCDR))
 (122 8 (:REWRITE ZP-OPEN))
 (98 2 (:DEFINITION NTHCDR))
 (96 4 (:REWRITE NTHCDR-WHEN-ZP))
 (77 2 (:REWRITE CONSP-OF-NTHCDR))
 (59 1 (:DEFINITION SYMBOL-BTREE-TO-ALIST))
 (54 18 (:REWRITE CONSP-SYMBOL-BTREE-TO-ALIST))
 (48 2 (:DEFINITION BINARY-APPEND))
 (43 3 (:DEFINITION SYMBOL-BTREEP))
 (40 4 (:DEFINITION LEN))
 (35 18 (:REWRITE DEFAULT-<-2))
 (35 4 (:DEFINITION NFIX))
 (32 23 (:REWRITE DEFAULT-CAR))
 (30 18 (:REWRITE DEFAULT-<-1))
 (29 16 (:REWRITE DEFAULT-+-2))
 (25 1 (:REWRITE CAR-OF-NTHCDR))
 (24 1 (:DEFINITION NTH))
 (20 16 (:REWRITE DEFAULT-+-1))
 (18 4 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (14 3 (:REWRITE COMMUTATIVITY-OF-+))
 (13 4 (:REWRITE NTHCDR-WHEN-ATOM))
 (8 4 (:LINEAR FLOOR-X-2-<-X))
 (8 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (7 4 (:LINEAR FLOOR-X-2-<=-X))
 (6 1 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE OPEN-SMALL-NTHCDR))
 )
(TAKE-OF-OWN-LEN)
(SYMBOL-BTREE-TO-ALIST-OF-REBALANCE-SYMBOL-BTREE
 (379 1 (:DEFINITION SYMBOL-ALIST-TO-BTREE-AUX))
 (268 2 (:REWRITE SYMBOL-ALIST-TO-BTREE-AUX-IS-NTHCDR))
 (202 1 (:REWRITE NTHCDR-OF-CDR))
 (174 174 (:TYPE-PRESCRIPTION FLOOR-X-2-NATP))
 (162 51 (:REWRITE DEFAULT-CDR))
 (139 1 (:REWRITE NTHCDR-OF-NTHCDR))
 (122 8 (:REWRITE ZP-OPEN))
 (118 2 (:DEFINITION SYMBOL-BTREE-TO-ALIST))
 (98 2 (:DEFINITION NTHCDR))
 (96 4 (:REWRITE NTHCDR-WHEN-ZP))
 (96 4 (:DEFINITION BINARY-APPEND))
 (92 20 (:REWRITE CONSP-SYMBOL-BTREE-TO-ALIST))
 (77 2 (:REWRITE CONSP-OF-NTHCDR))
 (75 5 (:DEFINITION SYMBOL-BTREEP))
 (46 37 (:REWRITE DEFAULT-CAR))
 (40 4 (:DEFINITION LEN))
 (36 19 (:REWRITE DEFAULT-<-2))
 (32 19 (:REWRITE DEFAULT-<-1))
 (29 16 (:REWRITE DEFAULT-+-2))
 (25 1 (:REWRITE CAR-OF-NTHCDR))
 (24 1 (:DEFINITION NTH))
 (20 16 (:REWRITE DEFAULT-+-1))
 (18 4 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (14 3 (:REWRITE COMMUTATIVITY-OF-+))
 (13 4 (:REWRITE NTHCDR-WHEN-ATOM))
 (8 4 (:LINEAR FLOOR-X-2-<-X))
 (8 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (7 4 (:LINEAR FLOOR-X-2-<=-X))
 (6 1 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (4 2 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE FOLD-CONSTS-IN-+))
 (2 2 (:REWRITE OPEN-SMALL-NTHCDR))
 )
(SYMBOL-BTREE-FIND-REBALANCE
 (168 2 (:DEFINITION SYMBOL-BTREE-TO-ALIST))
 (124 16 (:REWRITE CONSP-SYMBOL-BTREE-TO-ALIST))
 (121 4 (:DEFINITION BINARY-APPEND))
 (96 6 (:DEFINITION SYMBOL-BTREEP))
 (91 61 (:REWRITE DEFAULT-CAR))
 (78 60 (:REWRITE DEFAULT-CDR))
 (50 4 (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
 (45 1 (:DEFINITION ASSOC-EQUAL))
 (44 2 (:REWRITE SYMBOL-ALIST-SORTEDP-AND-SYMBOL<-LAST-IMPLIES-NOT-ASSOC))
 (31 1 (:DEFINITION SYMBOL-BTREE-FIND))
 (30 2 (:REWRITE SYMBOL-ALIST-SORTEDP-AND-SYMBOL<-FIRST-IMPLIES-NOT-ASSOC))
 (20 2 (:DEFINITION SYMBOL-ALISTP))
 (15 3 (:REWRITE SYMBOL<-ASYMMETRIC))
 (14 8 (:REWRITE SYMBOL<-TRICHOTOMY))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL-ALISTP))
 (12 6 (:TYPE-PRESCRIPTION LAST))
 (11 1 (:DEFINITION LAST))
 (5 5 (:REWRITE SYMBOL-BTREE-FIND-WHEN-NOT-SYMBOLP-KEY))
 (2 2 (:REWRITE SYMBOLP-CAAR-SYMBOL-BTREE-TO-ALIST))
 (2 2 (:REWRITE SYMBOL-ALISTP-SYMBOL-BTREE-TO-ALIST))
 (2 2 (:REWRITE ASSOC-WHEN-NOT-SYMBOLP-KEY))
 (1 1 (:REWRITE ASSOC-IN-SYMBOL-BTREE-TO-ALIST-WHEN-SYMBOLP-KEY))
 )
(SYMBOL-BTREE-KEY-DEPTH
 (1418 654 (:REWRITE DEFAULT-+-2))
 (920 654 (:REWRITE DEFAULT-+-1))
 (560 140 (:DEFINITION INTEGER-ABS))
 (560 70 (:DEFINITION LENGTH))
 (350 70 (:DEFINITION LEN))
 (214 162 (:REWRITE DEFAULT-<-2))
 (180 162 (:REWRITE DEFAULT-<-1))
 (140 140 (:REWRITE DEFAULT-UNARY-MINUS))
 (116 28 (:REWRITE SYMBOL<-ASYMMETRIC))
 (76 54 (:REWRITE SYMBOL<-TRICHOTOMY))
 (70 70 (:TYPE-PRESCRIPTION LEN))
 (70 70 (:REWRITE DEFAULT-REALPART))
 (70 70 (:REWRITE DEFAULT-NUMERATOR))
 (70 70 (:REWRITE DEFAULT-IMAGPART))
 (70 70 (:REWRITE DEFAULT-DENOMINATOR))
 (70 70 (:REWRITE DEFAULT-COERCE-2))
 (70 70 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-BTREE-FIND/DEPTH-AUX
 (1418 654 (:REWRITE DEFAULT-+-2))
 (920 654 (:REWRITE DEFAULT-+-1))
 (560 140 (:DEFINITION INTEGER-ABS))
 (560 70 (:DEFINITION LENGTH))
 (350 70 (:DEFINITION LEN))
 (220 168 (:REWRITE DEFAULT-<-2))
 (186 168 (:REWRITE DEFAULT-<-1))
 (140 140 (:REWRITE DEFAULT-UNARY-MINUS))
 (116 28 (:REWRITE SYMBOL<-ASYMMETRIC))
 (76 54 (:REWRITE SYMBOL<-TRICHOTOMY))
 (70 70 (:TYPE-PRESCRIPTION LEN))
 (70 70 (:REWRITE DEFAULT-REALPART))
 (70 70 (:REWRITE DEFAULT-NUMERATOR))
 (70 70 (:REWRITE DEFAULT-IMAGPART))
 (70 70 (:REWRITE DEFAULT-DENOMINATOR))
 (70 70 (:REWRITE DEFAULT-COERCE-2))
 (70 70 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-BTREE-FIND/DEPTH-AUX-REDEF
 (408 102 (:REWRITE SYMBOL<-ASYMMETRIC))
 (374 207 (:REWRITE DEFAULT-+-2))
 (242 224 (:REWRITE DEFAULT-CDR))
 (227 207 (:REWRITE DEFAULT-+-1))
 (204 204 (:REWRITE SYMBOL<-TRICHOTOMY))
 (196 64 (:REWRITE FOLD-CONSTS-IN-+))
 (98 98 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (96 96 (:TYPE-PRESCRIPTION SYMBOL-BTREE-KEY-DEPTH))
 (52 52 (:REWRITE SYMBOL-BTREE-FIND-WHEN-NOT-SYMBOLP-KEY))
 )
(SYMBOL-BTREE-FIND/DEPTH
 (1973 933 (:REWRITE DEFAULT-+-2))
 (1199 933 (:REWRITE DEFAULT-+-1))
 (560 140 (:DEFINITION INTEGER-ABS))
 (560 70 (:DEFINITION LENGTH))
 (350 70 (:DEFINITION LEN))
 (214 162 (:REWRITE DEFAULT-<-2))
 (180 162 (:REWRITE DEFAULT-<-1))
 (140 140 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (140 140 (:REWRITE DEFAULT-UNARY-MINUS))
 (87 87 (:REWRITE SYMBOL-BTREE-FIND-WHEN-NOT-SYMBOLP-KEY))
 (70 70 (:TYPE-PRESCRIPTION LEN))
 (70 70 (:REWRITE DEFAULT-REALPART))
 (70 70 (:REWRITE DEFAULT-NUMERATOR))
 (70 70 (:REWRITE DEFAULT-IMAGPART))
 (70 70 (:REWRITE DEFAULT-DENOMINATOR))
 (70 70 (:REWRITE DEFAULT-COERCE-2))
 (70 70 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-BTREE-FIND/DEPTH-REDEF
 (2080 520 (:REWRITE SYMBOL<-ASYMMETRIC))
 (1308 654 (:REWRITE DEFAULT-+-2))
 (1040 1040 (:REWRITE SYMBOL<-TRICHOTOMY))
 (654 654 (:REWRITE DEFAULT-+-1))
 (300 300 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (204 204 (:REWRITE SYMBOL-BTREE-FIND-WHEN-NOT-SYMBOLP-KEY))
 )
(SYMBOL-BTREE-UPDATE/DEPTH
 (1544 725 (:REWRITE DEFAULT-+-2))
 (991 725 (:REWRITE DEFAULT-+-1))
 (560 140 (:DEFINITION INTEGER-ABS))
 (560 70 (:DEFINITION LENGTH))
 (350 70 (:DEFINITION LEN))
 (214 162 (:REWRITE DEFAULT-<-2))
 (180 162 (:REWRITE DEFAULT-<-1))
 (140 140 (:REWRITE DEFAULT-UNARY-MINUS))
 (75 75 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (70 70 (:TYPE-PRESCRIPTION LEN))
 (70 70 (:REWRITE DEFAULT-REALPART))
 (70 70 (:REWRITE DEFAULT-NUMERATOR))
 (70 70 (:REWRITE DEFAULT-IMAGPART))
 (70 70 (:REWRITE DEFAULT-DENOMINATOR))
 (70 70 (:REWRITE DEFAULT-COERCE-2))
 (70 70 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-BTREE-UPDATE/DEPTH-REDEF
 (2080 520 (:REWRITE SYMBOL<-ASYMMETRIC))
 (1308 654 (:REWRITE DEFAULT-+-2))
 (1040 1040 (:REWRITE SYMBOL<-TRICHOTOMY))
 (654 654 (:REWRITE DEFAULT-+-1))
 (300 300 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(SYMBOL-BTREE-UPDATE/FIND/DEPTH
 (1544 725 (:REWRITE DEFAULT-+-2))
 (991 725 (:REWRITE DEFAULT-+-1))
 (560 140 (:DEFINITION INTEGER-ABS))
 (560 70 (:DEFINITION LENGTH))
 (350 70 (:DEFINITION LEN))
 (214 162 (:REWRITE DEFAULT-<-2))
 (180 162 (:REWRITE DEFAULT-<-1))
 (140 140 (:REWRITE DEFAULT-UNARY-MINUS))
 (75 75 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (70 70 (:TYPE-PRESCRIPTION LEN))
 (70 70 (:REWRITE DEFAULT-REALPART))
 (70 70 (:REWRITE DEFAULT-NUMERATOR))
 (70 70 (:REWRITE DEFAULT-IMAGPART))
 (70 70 (:REWRITE DEFAULT-DENOMINATOR))
 (70 70 (:REWRITE DEFAULT-COERCE-2))
 (70 70 (:REWRITE DEFAULT-COERCE-1))
 )
(SYMBOL-BTREE-UPDATE/FIND/DEPTH-REDEF
 (4200 1050 (:REWRITE SYMBOL<-ASYMMETRIC))
 (2100 2100 (:REWRITE SYMBOL<-TRICHOTOMY))
 (1888 944 (:REWRITE DEFAULT-+-2))
 (944 944 (:REWRITE DEFAULT-+-1))
 (524 524 (:REWRITE SYMBOL-BTREE-FIND-WHEN-NOT-SYMBOLP-KEY))
 (498 498 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
