(MEMBERP)
(|(memberp e (list x))|
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(ARG1)
(ARG2)
(NON-QUOTEP-ADDENDS
 (322 154 (:REWRITE DEFAULT-+-2))
 (207 154 (:REWRITE DEFAULT-+-1))
 (104 26 (:REWRITE COMMUTATIVITY-OF-+))
 (104 26 (:DEFINITION INTEGER-ABS))
 (104 13 (:DEFINITION LENGTH))
 (65 13 (:DEFINITION LEN))
 (63 63 (:REWRITE DEFAULT-CDR))
 (43 43 (:REWRITE FOLD-CONSTS-IN-+))
 (41 41 (:REWRITE DEFAULT-CAR))
 (30 28 (:REWRITE DEFAULT-<-2))
 (30 28 (:REWRITE DEFAULT-<-1))
 (26 26 (:REWRITE DEFAULT-UNARY-MINUS))
 (13 13 (:TYPE-PRESCRIPTION LEN))
 (13 13 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (13 13 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (13 13 (:REWRITE DEFAULT-REALPART))
 (13 13 (:REWRITE DEFAULT-NUMERATOR))
 (13 13 (:REWRITE DEFAULT-IMAGPART))
 (13 13 (:REWRITE DEFAULT-DENOMINATOR))
 (13 13 (:REWRITE DEFAULT-COERCE-2))
 (13 13 (:REWRITE DEFAULT-COERCE-1))
 )
(REWRITING-GOAL-LITERAL)
(TERM-EQUAL)
(PRESENT-IN-HYPS)
(DISJOINT-BAGS-P)
(DISJOINTP-1)
(DISJOINTP)
(DISJOINTP-THM-1
 (583 583 (:REWRITE DEFAULT-CAR))
 (526 526 (:REWRITE DEFAULT-CDR))
 )
(CROCK-1
 (29 29 (:REWRITE DEFAULT-CAR))
 (13 13 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE ZP-OPEN))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(CROCK-2
 (111 111 (:REWRITE DEFAULT-CAR))
 (94 94 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(DISJOINT-THM-2
 (176 16 (:DEFINITION DISJOINTP-1))
 (120 120 (:REWRITE DEFAULT-CDR))
 (116 116 (:REWRITE DEFAULT-CAR))
 (112 16 (:DEFINITION DISJOINT-BAGS-P))
 (33 28 (:REWRITE ZP-OPEN))
 (27 26 (:REWRITE DEFAULT-+-2))
 (26 26 (:REWRITE DEFAULT-+-1))
 (20 20 (:REWRITE NATP-RW))
 (16 16 (:TYPE-PRESCRIPTION DISJOINT-BAGS-P))
 (14 14 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (3 1 (:REWRITE POSP-RW))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (3 1 (:REWRITE <-0-+-NEGATIVE-1))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE NATP-POSP))
 )
(RANGE-1
 (51 51 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (7 5 (:REWRITE DEFAULT-<-2))
 (7 5 (:REWRITE DEFAULT-<-1))
 (7 5 (:REWRITE DEFAULT-+-2))
 (6 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(RANGE)
(CROCK-1-1
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (12 10 (:REWRITE DEFAULT-CDR))
 (12 10 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE DEFAULT-+-2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(CROCK-1
 (68 68 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (20 18 (:REWRITE DEFAULT-<-1))
 (20 17 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-<-2))
 (18 17 (:REWRITE DEFAULT-+-1))
 (16 16 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (15 2 (:REWRITE COMMUTATIVITY-OF-+))
 (13 11 (:REWRITE DEFAULT-CAR))
 (12 10 (:REWRITE DEFAULT-CDR))
 (10 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 3 (:REWRITE FOLD-CONSTS-IN-+))
 (4 1 (:REWRITE <-+-NEGATIVE-0-1))
 (2 2 (:REWRITE CDR-CONS))
 )
(|(memberp e (range base offset length))|
 (75 1 (:DEFINITION RANGE-1))
 (51 6 (:REWRITE COMMUTATIVITY-2-OF-+))
 (33 28 (:REWRITE DEFAULT-+-2))
 (30 28 (:REWRITE DEFAULT-+-1))
 (15 13 (:REWRITE FOLD-CONSTS-IN-+))
 (5 1 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 1 (:REWRITE <-+-NEGATIVE-0-1))
 (2 2 (:DEFINITION FIX))
 (2 1 (:REWRITE UNICITY-OF-0))
 (2 1 (:REWRITE MINUS-CANCELLATION-ON-LEFT))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (1 1 (:REWRITE INVERSE-OF-+))
 )
(SUBRANGEP)
(|(disjointp subrange1 subrange2)|
 (304 304 (:REWRITE DEFAULT-CAR))
 (262 262 (:REWRITE DEFAULT-CDR))
 )
(RANGE-1-V2
 (53 53 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (13 8 (:REWRITE DEFAULT-+-2))
 (9 8 (:REWRITE DEFAULT-+-1))
 (7 5 (:REWRITE DEFAULT-<-2))
 (7 5 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE FOLD-CONSTS-IN-+))
 (4 3 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(RANGE-V2)
(CROCK-1-1-1
 (117 93 (:REWRITE DEFAULT-+-2))
 (103 93 (:REWRITE DEFAULT-+-1))
 (44 30 (:REWRITE FOLD-CONSTS-IN-+))
 (32 32 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (25 25 (:REWRITE DEFAULT-UNARY-MINUS))
 (25 17 (:REWRITE DEFAULT-CDR))
 (25 17 (:REWRITE DEFAULT-CAR))
 (24 20 (:REWRITE DEFAULT-<-1))
 (20 20 (:REWRITE DEFAULT-<-2))
 )
(CROCK-1-1
 (25 23 (:REWRITE DEFAULT-+-2))
 (24 23 (:REWRITE DEFAULT-+-1))
 (15 2 (:REWRITE COMMUTATIVITY-OF-+))
 (14 13 (:REWRITE DEFAULT-<-1))
 (13 13 (:REWRITE DEFAULT-<-2))
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (11 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 1 (:REWRITE <-+-NEGATIVE-0-1))
 (3 3 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
(CROCK-1
 (158 2 (:DEFINITION RANGE-1-V2))
 (114 12 (:REWRITE COMMUTATIVITY-2-OF-+))
 (60 44 (:REWRITE DEFAULT-+-2))
 (60 44 (:REWRITE DEFAULT-+-1))
 (26 26 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 20 (:REWRITE FOLD-CONSTS-IN-+))
 (14 2 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (12 12 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (10 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 4 (:DEFINITION FIX))
 (6 2 (:REWRITE UNICITY-OF-0))
 (6 2 (:REWRITE <-+-NEGATIVE-0-1))
 (4 2 (:REWRITE MINUS-CANCELLATION-ON-LEFT))
 (2 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (2 2 (:REWRITE INVERSE-OF-+))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 )
(CROCK-2-2
 (19 18 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE DEFAULT-<-2))
 (18 15 (:REWRITE DEFAULT-+-2))
 (17 17 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (15 15 (:REWRITE DEFAULT-+-1))
 (7 5 (:REWRITE DEFAULT-CAR))
 (7 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 4 (:REWRITE DEFAULT-CDR))
 (5 3 (:REWRITE FOLD-CONSTS-IN-+))
 (4 1 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (4 1 (:REWRITE <-+-NEGATIVE-0-1))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(CROCK-2
 (34 30 (:REWRITE DEFAULT-<-2))
 (31 30 (:REWRITE DEFAULT-<-1))
 (30 27 (:REWRITE DEFAULT-+-2))
 (27 27 (:REWRITE DEFAULT-+-1))
 (17 17 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (13 13 (:REWRITE DEFAULT-UNARY-MINUS))
 (7 1 (:REWRITE COMMUTATIVITY-2-OF-+))
 (6 5 (:REWRITE DEFAULT-CDR))
 (6 5 (:REWRITE DEFAULT-CAR))
 (5 3 (:REWRITE FOLD-CONSTS-IN-+))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 1 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (4 1 (:REWRITE <-+-NEGATIVE-0-1))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(|(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|
 (284 4 (:DEFINITION RANGE-1-V2))
 (204 24 (:REWRITE COMMUTATIVITY-2-OF-+))
 (116 100 (:REWRITE DEFAULT-+-2))
 (108 100 (:REWRITE DEFAULT-+-1))
 (44 44 (:REWRITE FOLD-CONSTS-IN-+))
 (20 4 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (15 1 (:DEFINITION SUBRANGEP))
 (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 10 (:REWRITE DEFAULT-<-2))
 (12 10 (:REWRITE DEFAULT-<-1))
 (12 4 (:REWRITE <-+-NEGATIVE-0-1))
 (9 1 (:REWRITE CROCK-2-2))
 (8 8 (:DEFINITION FIX))
 (8 4 (:REWRITE UNICITY-OF-0))
 (8 4 (:REWRITE MINUS-CANCELLATION-ON-LEFT))
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (4 4 (:REWRITE INVERSE-OF-+))
 (3 3 (:TYPE-PRESCRIPTION RANGE-1-V2))
 (1 1 (:TYPE-PRESCRIPTION MEMBERP))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(|(subrangep (list x) (range base offset length))|
 (29 29 (:REWRITE DEFAULT-+-2))
 (29 29 (:REWRITE DEFAULT-+-1))
 (10 8 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE DEFAULT-<-2))
 (4 4 (:TYPE-PRESCRIPTION RANGE))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE |(subrangep (range base1 offset1 length1) (range base2 offset2 length2))|))
 )
(|(subrangep (range base offset length) (list x)|
 (40 34 (:REWRITE DEFAULT-+-2))
 (36 34 (:REWRITE DEFAULT-+-1))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (2 2 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(|(subrangep (list x) (list y)|
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(CROCK-1
 (50 50 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE CDR-CONS))
 (2 2 (:REWRITE CAR-CONS))
 )
(|(subrangep x x)|
 (17 17 (:REWRITE DEFAULT-CAR))
 )
(DISJOINT-THMS-BIND-FREE-FN-4)
(DISJOINT-THMS-BIND-FREE-FN-3
 (326 155 (:REWRITE DEFAULT-+-2))
 (209 155 (:REWRITE DEFAULT-+-1))
 (112 28 (:REWRITE COMMUTATIVITY-OF-+))
 (112 28 (:DEFINITION INTEGER-ABS))
 (112 14 (:DEFINITION LENGTH))
 (70 70 (:REWRITE DEFAULT-CDR))
 (70 14 (:DEFINITION LEN))
 (40 40 (:REWRITE DEFAULT-CAR))
 (35 31 (:REWRITE DEFAULT-<-2))
 (33 31 (:REWRITE DEFAULT-<-1))
 (28 28 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:TYPE-PRESCRIPTION LEN))
 (14 14 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (14 14 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (14 14 (:REWRITE DEFAULT-REALPART))
 (14 14 (:REWRITE DEFAULT-NUMERATOR))
 (14 14 (:REWRITE DEFAULT-IMAGPART))
 (14 14 (:REWRITE DEFAULT-DENOMINATOR))
 (14 14 (:REWRITE DEFAULT-COERCE-2))
 (14 14 (:REWRITE DEFAULT-COERCE-1))
 )
(DISJOINT-THMS-BIND-FREE-FN-2)
(DISJOINT-THMS-BIND-FREE-FN-1)
(DISJOINT-THMS-BIND-FREE-FN)
(|(not (equal x y)) --- disjointp|)
(CROCK-1-1
 (38 38 (:REWRITE DEFAULT-CAR))
 (30 30 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(CROCK-1-2
 (5 5 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(CROCK-1-3
 (437 437 (:REWRITE DEFAULT-CAR))
 (255 255 (:REWRITE DEFAULT-CDR))
 )
(CROCK-1
 (108 108 (:REWRITE DEFAULT-CDR))
 (99 99 (:REWRITE DEFAULT-CAR))
 (87 24 (:DEFINITION MEMBERP))
 (47 17 (:REWRITE ZP-OPEN))
 (33 33 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (29 23 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE DEFAULT-+-1))
 (18 6 (:REWRITE FOLD-CONSTS-IN-+))
 (18 6 (:REWRITE <-0-+-NEGATIVE-1))
 (9 9 (:REWRITE NATP-RW))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 )
(DISJOINT-SYNTAXP-FN)
(|(disjointp (list x y)) --- disjoint super-ranges|
 (48 8 (:DEFINITION NTH))
 (40 40 (:REWRITE DEFAULT-CDR))
 (33 33 (:REWRITE DEFAULT-CAR))
 (21 7 (:DEFINITION MEMBERP))
 (8 8 (:REWRITE ZP-OPEN))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE |(disjointp subrange1 subrange2)|))
 (2 2 (:REWRITE NATP-RW))
 (1 1 (:TYPE-PRESCRIPTION DISJOINTP-1))
 )
(DISJOINT-3-ITEMS
 (24 24 (:REWRITE DEFAULT-CDR))
 (15 15 (:REWRITE DEFAULT-CAR))
 (13 5 (:REWRITE |(disjointp subrange1 subrange2)|))
 (7 7 (:TYPE-PRESCRIPTION SUBRANGEP))
 (5 5 (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (1 1 (:REWRITE |(subrangep x x)|))
 )
(DISJOINT-4-ITEMS
 (72 72 (:TYPE-PRESCRIPTION SUBRANGEP))
 (67 10 (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (50 50 (:REWRITE DEFAULT-CDR))
 (46 10 (:REWRITE |(disjointp subrange1 subrange2)|))
 (31 31 (:REWRITE DEFAULT-CAR))
 (17 17 (:REWRITE |(subrangep x x)|))
 )
(DISJOINT-5-ITEMS
 (200 200 (:TYPE-PRESCRIPTION SUBRANGEP))
 (157 17 (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (119 17 (:REWRITE |(disjointp subrange1 subrange2)|))
 (86 86 (:REWRITE DEFAULT-CDR))
 (53 53 (:REWRITE DEFAULT-CAR))
 (35 35 (:REWRITE |(subrangep x x)|))
 )
(DISJOINT-6-ITEMS
 (452 452 (:TYPE-PRESCRIPTION SUBRANGEP))
 (322 26 (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (256 26 (:REWRITE |(disjointp subrange1 subrange2)|))
 (132 132 (:REWRITE DEFAULT-CDR))
 (81 81 (:REWRITE DEFAULT-CAR))
 (63 63 (:REWRITE |(subrangep x x)|))
 )
(DISJOINT-7-ITEMS
 (889 889 (:TYPE-PRESCRIPTION SUBRANGEP))
 (595 37 (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (487 37 (:REWRITE |(disjointp subrange1 subrange2)|))
 (188 188 (:REWRITE DEFAULT-CDR))
 (115 115 (:REWRITE DEFAULT-CAR))
 (103 103 (:REWRITE |(subrangep x x)|))
 )
(DISJOINT-8-ITEMS
 (1584 1584 (:TYPE-PRESCRIPTION SUBRANGEP))
 (1015 50 (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (848 50 (:REWRITE |(disjointp subrange1 subrange2)|))
 (254 254 (:REWRITE DEFAULT-CDR))
 (157 157 (:REWRITE |(subrangep x x)|))
 (155 155 (:REWRITE DEFAULT-CAR))
 )
(DISJOINT-9-ITEMS
 (2622 2622 (:TYPE-PRESCRIPTION SUBRANGEP))
 (1627 65 (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (1381 65 (:REWRITE |(disjointp subrange1 subrange2)|))
 (330 330 (:REWRITE DEFAULT-CDR))
 (227 227 (:REWRITE |(subrangep x x)|))
 (201 201 (:REWRITE DEFAULT-CAR))
 )
(DISJOINT-10-ITEMS
 (4100 4100 (:TYPE-PRESCRIPTION SUBRANGEP))
 (2482 82 (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (2134 82 (:REWRITE |(disjointp subrange1 subrange2)|))
 (416 416 (:REWRITE DEFAULT-CDR))
 (315 315 (:REWRITE |(subrangep x x)|))
 (253 253 (:REWRITE DEFAULT-CAR))
 )
(CROCK-1-1
 (437 437 (:REWRITE DEFAULT-CAR))
 (255 255 (:REWRITE DEFAULT-CDR))
 )
(CROCK-1-2
 (20 14 (:REWRITE DEFAULT-<-1))
 (19 17 (:REWRITE DEFAULT-CDR))
 (19 17 (:REWRITE DEFAULT-CAR))
 (19 14 (:REWRITE DEFAULT-<-2))
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 7 (:REWRITE DEFAULT-+-2))
 (7 7 (:REWRITE DEFAULT-+-1))
 (6 6 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(CROCK-1-3-1
 (515 515 (:REWRITE DEFAULT-CAR))
 (273 273 (:REWRITE DEFAULT-CDR))
 )
(CROCK-1-3
 (49 11 (:DEFINITION MEMBERP))
 (24 22 (:REWRITE DEFAULT-CDR))
 (24 22 (:REWRITE DEFAULT-CAR))
 (23 5 (:REWRITE CROCK-1-2))
 (17 12 (:REWRITE DEFAULT-<-1))
 (16 16 (:TYPE-PRESCRIPTION RANGE-1))
 (15 12 (:REWRITE DEFAULT-<-2))
 (10 10 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(CROCK-1
 (101 70 (:REWRITE DEFAULT-<-1))
 (96 70 (:REWRITE DEFAULT-<-2))
 (58 58 (:REWRITE DEFAULT-+-2))
 (58 58 (:REWRITE DEFAULT-+-1))
 (57 57 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (33 33 (:REWRITE DEFAULT-UNARY-MINUS))
 (25 25 (:REWRITE DEFAULT-CDR))
 (25 25 (:REWRITE DEFAULT-CAR))
 (18 18 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (18 18 (:TYPE-PRESCRIPTION RANGE-1))
 (10 10 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(CROCK-2
 (2 2 (:REWRITE CROCK-1-3))
 )
(|(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|
 (41 27 (:REWRITE DEFAULT-+-1))
 (38 27 (:REWRITE DEFAULT-+-2))
 (23 23 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (13 13 (:REWRITE FOLD-CONSTS-IN-+))
 (5 5 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE |(disjointp subrange1 subrange2)|))
 (1 1 (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 )
(|(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 2|
 (42 27 (:REWRITE DEFAULT-+-2))
 (39 27 (:REWRITE DEFAULT-+-1))
 (21 21 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (15 15 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE CROCK-1-3))
 (6 6 (:REWRITE DEFAULT-CAR))
 (6 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE |(disjointp subrange1 subrange2)|))
 (2 2 (:REWRITE |(disjointp (list x y)) --- disjoint super-ranges|))
 (2 2 (:REWRITE |(disjointp (list (range base1 offset1 length1) (range base2 offset2 length2))) --- 1|))
 )
(ANCESTORS-CHECK-DISJOINTP-HACK
 (360 358 (:REWRITE DEFAULT-CDR))
 (260 259 (:REWRITE DEFAULT-CAR))
 (220 44 (:DEFINITION LEN))
 (116 1 (:DEFINITION VAR-FN-COUNT-1))
 (105 1 (:DEFINITION FN-COUNT-EVG-REC))
 (102 53 (:REWRITE DEFAULT-+-2))
 (53 53 (:REWRITE DEFAULT-+-1))
 (46 23 (:DEFINITION TRUE-LISTP))
 (42 14 (:DEFINITION SYMBOL-LISTP))
 (32 32 (:REWRITE TERMP-IMPLIES-PSEUDO-TERMP))
 (24 4 (:DEFINITION MIN-FIXNAT$INLINE))
 (20 20 (:REWRITE TERM-LISTP-IMPLIES-PSEUDO-TERM-LISTP))
 (16 2 (:DEFINITION LENGTH))
 (13 5 (:REWRITE UNICITY-OF-0))
 (12 9 (:REWRITE DEFAULT-<-2))
 (11 9 (:REWRITE DEFAULT-<-1))
 (8 5 (:DEFINITION FIX))
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (4 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:TYPE-PRESCRIPTION FN-COUNT-EVG-REC-TYPE-PRESCRIPTION))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 (2 2 (:REWRITE DEFAULT-*-1))
 (1 1 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (1 1 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-SYMBOL-NAME))
 (1 1 (:REWRITE DEFAULT-REALPART))
 (1 1 (:REWRITE DEFAULT-NUMERATOR))
 (1 1 (:REWRITE DEFAULT-IMAGPART))
 (1 1 (:REWRITE DEFAULT-DENOMINATOR))
 )
(ANCESTORS-CHECK-DISJOINTP-HACK-CONSTRAINT
 (4418 21 (:DEFINITION ANCESTORS-CHECK1))
 (4200 40 (:DEFINITION FN-COUNT-EVG-REC))
 (2095 2051 (:REWRITE DEFAULT-CDR))
 (1858 42 (:DEFINITION EARLIER-ANCESTOR-BIGGERP))
 (1429 1395 (:REWRITE DEFAULT-CAR))
 (1041 676 (:REWRITE DEFAULT-<-2))
 (1040 1040 (:TYPE-PRESCRIPTION LEN))
 (960 160 (:DEFINITION MIN-FIXNAT$INLINE))
 (907 676 (:REWRITE DEFAULT-<-1))
 (720 440 (:REWRITE DEFAULT-+-2))
 (640 80 (:DEFINITION LENGTH))
 (520 200 (:REWRITE UNICITY-OF-0))
 (441 63 (:DEFINITION INTERSECTP-EQUAL))
 (440 440 (:REWRITE DEFAULT-+-1))
 (400 80 (:DEFINITION LEN))
 (372 348 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (320 200 (:DEFINITION FIX))
 (160 160 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (160 80 (:REWRITE DEFAULT-*-2))
 (80 80 (:TYPE-PRESCRIPTION FN-COUNT-EVG-REC-TYPE-PRESCRIPTION))
 (80 80 (:REWRITE DEFAULT-COERCE-2))
 (80 80 (:REWRITE DEFAULT-COERCE-1))
 (80 80 (:REWRITE DEFAULT-*-1))
 (63 63 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (63 63 (:TYPE-PRESCRIPTION INTERSECTP-EQUAL))
 (42 42 (:TYPE-PRESCRIPTION EARLIER-ANCESTOR-BIGGERP))
 (40 40 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (40 40 (:REWRITE INTEGERP==>DENOMINATOR=1))
 (40 40 (:REWRITE DEFAULT-UNARY-MINUS))
 (40 40 (:REWRITE DEFAULT-SYMBOL-NAME))
 (40 40 (:REWRITE DEFAULT-REALPART))
 (40 40 (:REWRITE DEFAULT-NUMERATOR))
 (40 40 (:REWRITE DEFAULT-IMAGPART))
 (40 40 (:REWRITE DEFAULT-DENOMINATOR))
 (24 6 (:DEFINITION STRIP-ANCESTOR-LITERALS))
 )
