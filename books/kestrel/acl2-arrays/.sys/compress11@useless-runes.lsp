(NOT-EQUAL-OF-CAR-OF-ASSOC-EQUAL
 (38 19 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (6 6 (:REWRITE DEFAULT-CAR))
 (4 4 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(ASSOC-EQUAL-OF-HEADER-AND-COMPRESS11
 (51 40 (:REWRITE DEFAULT-+-2))
 (51 40 (:REWRITE DEFAULT-+-1))
 (31 22 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (22 22 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 10 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 (11 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 )
(HEADER-OF-COMPRESS11
 (32 1 (:DEFINITION COMPRESS11))
 (13 4 (:REWRITE COMMUTATIVITY-OF-+))
 (9 8 (:REWRITE DEFAULT-+-2))
 (9 8 (:REWRITE DEFAULT-+-1))
 (4 1 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 )
(DIMENSIONS-OF-COMPRESS11
 (32 1 (:DEFINITION COMPRESS11))
 (13 4 (:REWRITE COMMUTATIVITY-OF-+))
 (9 8 (:REWRITE DEFAULT-+-2))
 (9 8 (:REWRITE DEFAULT-+-1))
 (4 1 (:REWRITE ZP-OPEN))
 (2 2 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 )
(DEFAULT-OF-COMPRESS11
 (32 1 (:DEFINITION COMPRESS11))
 (13 4 (:REWRITE COMMUTATIVITY-OF-+))
 (9 8 (:REWRITE DEFAULT-+-2))
 (9 8 (:REWRITE DEFAULT-+-1))
 (4 1 (:REWRITE ZP-OPEN))
 (2 2 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 )
(ALISTP-OF-COMPRESS11
 (254 187 (:REWRITE DEFAULT-+-2))
 (220 187 (:REWRITE DEFAULT-+-1))
 (144 48 (:REWRITE DEFAULT-CDR))
 (128 128 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (126 45 (:REWRITE FOLD-CONSTS-IN-+))
 (87 9 (:REWRITE COMMUTATIVITY-2-OF-+))
 (82 10 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (68 40 (:REWRITE DEFAULT-UNARY-MINUS))
 (42 9 (:REWRITE DISTRIBUTIVITY-OF-MINUS-OVER-+))
 (31 29 (:REWRITE DEFAULT-CAR))
 (29 29 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (15 15 (:REWRITE DEFAULT-<-2))
 (15 15 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(ASSOC-EQUAL-OF-COMPRESS11-WHEN-TOO-SMALL
 (97 14 (:REWRITE DEFAULT-CDR))
 (70 7 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (67 67 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (60 40 (:REWRITE DEFAULT-+-2))
 (60 40 (:REWRITE DEFAULT-+-1))
 (42 7 (:DEFINITION ALISTP))
 (24 12 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 (22 14 (:REWRITE DEFAULT-<-2))
 (22 14 (:REWRITE DEFAULT-<-1))
 (22 11 (:REWRITE DEFAULT-UNARY-MINUS))
 (12 12 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (7 7 (:REWRITE DEFAULT-CAR))
 )
(BOUNDED-INTEGER-ALISTP-OF-COMPRESS11
 (58 58 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (53 37 (:REWRITE DEFAULT-<-2))
 (48 32 (:REWRITE DEFAULT-+-2))
 (48 32 (:REWRITE DEFAULT-+-1))
 (45 45 (:REWRITE DEFAULT-CAR))
 (37 37 (:REWRITE DEFAULT-<-1))
 (36 36 (:REWRITE DEFAULT-CDR))
 (20 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (6 3 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(ASSOC-EQUAL-OF-COMPRESS11
 (246 196 (:REWRITE DEFAULT-+-2))
 (237 196 (:REWRITE DEFAULT-+-1))
 (197 37 (:REWRITE DEFAULT-CDR))
 (120 20 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (115 115 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (102 78 (:REWRITE DEFAULT-<-2))
 (78 78 (:REWRITE DEFAULT-<-1))
 (54 27 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 (53 53 (:REWRITE DEFAULT-UNARY-MINUS))
 (39 21 (:REWRITE FOLD-CONSTS-IN-+))
 (27 27 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(ASSOC-EQUAL-OF-COMPRESS11-TOO-HIGH
 (72 56 (:REWRITE DEFAULT-+-2))
 (72 56 (:REWRITE DEFAULT-+-1))
 (50 39 (:REWRITE DEFAULT-<-2))
 (43 43 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (39 39 (:REWRITE DEFAULT-<-1))
 (28 14 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 (16 16 (:REWRITE DEFAULT-UNARY-MINUS))
 (14 14 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (11 11 (:REWRITE DEFAULT-CDR))
 )
(ASSOC-EQUAL-OF-COMPRESS11-BOTH
 (32 24 (:REWRITE DEFAULT-<-2))
 (28 4 (:REWRITE DEFAULT-CDR))
 (24 24 (:REWRITE DEFAULT-<-1))
 (23 23 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (23 15 (:REWRITE DEFAULT-+-2))
 (22 15 (:REWRITE DEFAULT-+-1))
 (21 16 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (18 3 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (8 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 3 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(NORMALIZE-COMPRESS11-NAME
 (138 20 (:REWRITE DEFAULT-CDR))
 (134 67 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (100 10 (:REWRITE CONSP-OF-ASSOC-EQUAL-GEN))
 (87 58 (:REWRITE DEFAULT-+-2))
 (87 58 (:REWRITE DEFAULT-+-1))
 (75 75 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (60 10 (:DEFINITION ALISTP))
 (34 17 (:REWRITE DEFAULT-UNARY-MINUS))
 (16 16 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (10 10 (:REWRITE DEFAULT-CAR))
 (7 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE DEFAULT-<-1))
 )
(NO-DUPLICATESP-OF-STRIP-CARS-OF-COMPRESS11
 (49 38 (:REWRITE DEFAULT-+-2))
 (49 38 (:REWRITE DEFAULT-+-1))
 (42 39 (:REWRITE DEFAULT-CDR))
 (34 32 (:REWRITE DEFAULT-CAR))
 (24 24 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (21 7 (:DEFINITION MEMBER-EQUAL))
 (14 14 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (12 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 8 (:REWRITE DEFAULT-<-2))
 (8 8 (:REWRITE DEFAULT-<-1))
 (4 2 (:REWRITE ASSOC-EQUAL-WHEN-MEMBER-EQUAL-OF-STRIP-CARS-IFF-CHEAP))
 (2 2 (:REWRITE FOLD-CONSTS-IN-+))
 )
