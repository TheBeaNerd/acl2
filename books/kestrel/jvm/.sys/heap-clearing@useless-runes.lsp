(CLR-OF-SET-FIELD
 (176 5 (:REWRITE CLR-WHEN-NOT-IN-RKEYS))
 (88 1 (:REWRITE RKEYS-S-TWO))
 (55 1 (:REWRITE IN-OF-IF))
 (55 1 (:DEFINITION SET::DELETE))
 (50 2 (:REWRITE S-SAME-G-STRONG))
 (34 34 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (32 1 (:REWRITE S==R))
 (31 10 (:REWRITE SET::IN-TAIL))
 (30 2 (:REWRITE SET::DELETE-NONMEMBER-CANCEL))
 (28 2 (:REWRITE SET::DELETE-IN))
 (26 26 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (24 24 (:REWRITE SET::SUBSET-IN))
 (24 1 (:REWRITE SET::IN-INSERT))
 (17 6 (:REWRITE SET::NEVER-IN-EMPTY))
 (16 8 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (16 2 (:REWRITE SET::INSERT-IDENTITY))
 (14 14 (:REWRITE SET::SUBSET-IN-2))
 (10 5 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (10 2 (:REWRITE SET::INSERT-WHEN-EMPTY))
 (10 1 (:REWRITE EQUAL-EQUAL-A-HEAD-HACK))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (8 8 (:REWRITE SET::SUBSET-IN-2-ALT))
 (8 8 (:REWRITE CLR-DIFFERENTIAL))
 (8 4 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (8 2 (:REWRITE INSERT-WHEN-EMPTY))
 (7 7 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (7 7 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (7 7 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (6 2 (:REWRITE SET::DELETE-PRESERVES-EMPTY))
 (6 1 (:REWRITE EQUAL-S-RECORD-EQUALITY))
 (5 5 (:REWRITE NOT-CLR-WHEN-NOT-S))
 (4 1 (:REWRITE TAG-LOCATION-ELIMINATION))
 (4 1 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (2 2 (:REWRITE SET::TAIL-PRESERVES-EMPTY))
 (2 2 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (2 2 (:REWRITE SET::HEAD-WHEN-EMPTY))
 (2 2 (:REWRITE HEAD-WHEN-EMPTY))
 (1 1 (:REWRITE SET::HEAD-UNIQUE))
 )
(CLEAR-FIELD)
(CLEAR-FIELD-OF-NIL)
(EQUAL-SET-FIELD-DESTRUCT
 (716 23 (:REWRITE CLR-WHEN-NOT-IN-RKEYS))
 (264 3 (:REWRITE RKEYS-S-TWO))
 (222 9 (:REWRITE EQUAL-S-RECORD-EQUALITY))
 (165 3 (:REWRITE IN-OF-IF))
 (165 3 (:DEFINITION SET::DELETE))
 (144 144 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (117 42 (:REWRITE SET::IN-TAIL))
 (112 6 (:REWRITE S-SAME-G-STRONG))
 (102 102 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (96 96 (:REWRITE SET::SUBSET-IN))
 (90 6 (:REWRITE SET::DELETE-NONMEMBER-CANCEL))
 (87 30 (:REWRITE SET::NEVER-IN-EMPTY))
 (84 6 (:REWRITE SET::DELETE-IN))
 (72 3 (:REWRITE SET::IN-INSERT))
 (66 66 (:REWRITE SET::SUBSET-IN-2))
 (48 6 (:REWRITE SET::INSERT-IDENTITY))
 (45 45 (:TYPE-PRESCRIPTION BOOLEANP))
 (45 45 (:REWRITE CLR-DIFFERENTIAL))
 (42 21 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (36 36 (:REWRITE SET::SUBSET-IN-2-ALT))
 (33 33 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (33 33 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (33 33 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (30 6 (:REWRITE SET::INSERT-WHEN-EMPTY))
 (30 3 (:REWRITE EQUAL-EQUAL-A-HEAD-HACK))
 (24 12 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (24 6 (:REWRITE INSERT-WHEN-EMPTY))
 (23 23 (:REWRITE NOT-CLR-WHEN-NOT-S))
 (18 6 (:REWRITE SET::DELETE-PRESERVES-EMPTY))
 (10 4 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (6 6 (:REWRITE SET::TAIL-PRESERVES-EMPTY))
 (6 6 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (6 6 (:REWRITE SET::HEAD-WHEN-EMPTY))
 (6 6 (:REWRITE HEAD-WHEN-EMPTY))
 (3 3 (:REWRITE SET::HEAD-UNIQUE))
 )
(CLEAR-FIELD-OF-SET-FIELD-BOTH
 (2945 70 (:REWRITE CLR-WHEN-NOT-IN-RKEYS))
 (1532 33 (:REWRITE S-SAME-G-STRONG))
 (989 17 (:DEFINITION SET::DELETE))
 (976 9 (:REWRITE RKEYS-S-TWO))
 (815 12 (:REWRITE IN-OF-IF))
 (723 37 (:REWRITE SET::DELETE-IN))
 (574 34 (:REWRITE SET::DELETE-NONMEMBER-CANCEL))
 (564 8 (:REWRITE RKEYS-OF-CLR))
 (490 6 (:REWRITE CLR-OVER-CLR))
 (487 177 (:REWRITE SET::IN-TAIL))
 (412 412 (:REWRITE SET::SUBSET-IN))
 (387 12 (:REWRITE SET::IN-INSERT))
 (368 368 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (274 113 (:REWRITE SET::NEVER-IN-EMPTY))
 (246 246 (:REWRITE SET::SUBSET-IN-2))
 (246 26 (:REWRITE SET::INSERT-IDENTITY))
 (242 121 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (224 17 (:REWRITE EQUAL-EQUAL-A-HEAD-HACK))
 (178 89 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (159 15 (:REWRITE EQUAL-S-RECORD-EQUALITY))
 (146 26 (:REWRITE SET::INSERT-WHEN-EMPTY))
 (141 141 (:REWRITE SET::SUBSET-IN-2-ALT))
 (130 130 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (130 130 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (130 130 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (121 121 (:TYPE-PRESCRIPTION BOOLEANP))
 (121 121 (:REWRITE CLR-DIFFERENTIAL))
 (116 64 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (112 26 (:REWRITE INSERT-WHEN-EMPTY))
 (102 34 (:REWRITE SET::DELETE-PRESERVES-EMPTY))
 (70 70 (:REWRITE NOT-CLR-WHEN-NOT-S))
 (34 34 (:REWRITE SET::TAIL-PRESERVES-EMPTY))
 (34 34 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (34 34 (:REWRITE SET::HEAD-WHEN-EMPTY))
 (34 34 (:REWRITE HEAD-WHEN-EMPTY))
 (24 8 (:REWRITE G-OF-CLR))
 (19 5 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (17 17 (:REWRITE SET::HEAD-UNIQUE))
 (8 2 (:REWRITE GET-FIELD-OF-S-DIFF))
 )
(CLEAR-FIELD-OF-SET-FIELD-DIFF
 (2471 48 (:REWRITE CLR-WHEN-NOT-IN-RKEYS))
 (1322 12 (:REWRITE RKEYS-S-TWO))
 (1253 15 (:REWRITE EQUAL-S-RECORD-EQUALITY))
 (993 18 (:REWRITE IN-OF-IF))
 (742 12 (:DEFINITION SET::DELETE))
 (573 30 (:REWRITE SET::DELETE-IN))
 (481 18 (:REWRITE SET::IN-INSERT))
 (469 21 (:REWRITE S-SAME-G-STRONG))
 (462 138 (:REWRITE SET::IN-TAIL))
 (462 24 (:REWRITE SET::DELETE-NONMEMBER-CANCEL))
 (352 352 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (336 336 (:REWRITE SET::SUBSET-IN))
 (286 143 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (274 24 (:REWRITE SET::INSERT-IDENTITY))
 (234 78 (:REWRITE SET::NEVER-IN-EMPTY))
 (202 12 (:REWRITE EQUAL-EQUAL-A-HEAD-HACK))
 (184 184 (:REWRITE SET::SUBSET-IN-2))
 (143 143 (:TYPE-PRESCRIPTION BOOLEANP))
 (143 143 (:REWRITE CLR-DIFFERENTIAL))
 (138 69 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (120 56 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (120 24 (:REWRITE SET::INSERT-WHEN-EMPTY))
 (106 106 (:REWRITE SET::SUBSET-IN-2-ALT))
 (96 24 (:REWRITE INSERT-WHEN-EMPTY))
 (94 94 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (94 94 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (94 94 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (72 24 (:REWRITE SET::DELETE-PRESERVES-EMPTY))
 (48 48 (:REWRITE NOT-CLR-WHEN-NOT-S))
 (30 8 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (24 24 (:REWRITE SET::TAIL-PRESERVES-EMPTY))
 (24 24 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (24 24 (:REWRITE SET::HEAD-WHEN-EMPTY))
 (24 24 (:REWRITE HEAD-WHEN-EMPTY))
 (15 5 (:REWRITE G-OF-CLR))
 (12 12 (:REWRITE SET::HEAD-UNIQUE))
 (10 4 (:REWRITE GET-FIELD-OF-S-DIFF))
 )
(CLEAR-FIELD-OF-SET-FIELD-SAME)
(GET-CLASS-OF-CLEAR-FIELD-IRREL-PAIR
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (4 1 (:REWRITE GET-FIELD-OF-SET-FIELD-DIFF-1))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (2 2 (:REWRITE CLR-DIFFERENTIAL))
 (1 1 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 )
(CLEAR-FIELD-OF-S
 (162 3 (:REWRITE CLR-WHEN-NOT-IN-RKEYS))
 (88 1 (:REWRITE RKEYS-S-TWO))
 (55 1 (:REWRITE IN-OF-IF))
 (55 1 (:DEFINITION SET::DELETE))
 (30 9 (:REWRITE SET::IN-TAIL))
 (30 2 (:REWRITE SET::DELETE-NONMEMBER-CANCEL))
 (28 28 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (28 2 (:REWRITE SET::DELETE-IN))
 (26 26 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (24 1 (:REWRITE SET::IN-INSERT))
 (22 22 (:REWRITE SET::SUBSET-IN))
 (16 5 (:REWRITE SET::NEVER-IN-EMPTY))
 (16 2 (:REWRITE SET::INSERT-IDENTITY))
 (12 12 (:REWRITE SET::SUBSET-IN-2))
 (10 2 (:REWRITE SET::INSERT-WHEN-EMPTY))
 (10 1 (:REWRITE EQUAL-EQUAL-A-HEAD-HACK))
 (8 4 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (8 2 (:REWRITE INSERT-WHEN-EMPTY))
 (7 7 (:REWRITE SET::SUBSET-IN-2-ALT))
 (6 6 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (6 6 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (6 6 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (6 2 (:REWRITE SET::DELETE-PRESERVES-EMPTY))
 (6 1 (:REWRITE S-SAME-G-STRONG))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (3 3 (:REWRITE NOT-CLR-WHEN-NOT-S))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (2 2 (:REWRITE SET::TAIL-PRESERVES-EMPTY))
 (2 2 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (2 2 (:REWRITE SET::HEAD-WHEN-EMPTY))
 (2 2 (:REWRITE HEAD-WHEN-EMPTY))
 (2 2 (:REWRITE CLR-DIFFERENTIAL))
 (2 1 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (1 1 (:REWRITE SET::HEAD-UNIQUE))
 )
(CLEAR-BINDING)
(CLEAR-BINDING-NIL)
(CLEAR-BINDING-OF-NOT-CONSP)
(CLEAR-BINDING-DOES-NOTHING
 (142 14 (:REWRITE TRUE-LIST-FIX-WHEN-TRUE-LISTP))
 (106 20 (:DEFINITION TRUE-LISTP))
 (87 18 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (82 82 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (68 2 (:DEFINITION SUBSETP-EQUAL))
 (63 61 (:REWRITE DEFAULT-CDR))
 (57 25 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (50 2 (:REWRITE MEMBER-EQUAL-BECOMES-MEMBERP))
 (42 21 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (38 38 (:TYPE-PRESCRIPTION STRIP-CARS))
 (36 18 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (36 18 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (36 18 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (30 15 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (25 25 (:REWRITE CLR-DIFFERENTIAL))
 (23 23 (:REWRITE WFR-HACK5))
 (21 21 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (18 18 (:TYPE-PRESCRIPTION BOOLEANP))
 (18 18 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (18 18 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (18 18 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (18 18 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (15 15 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (11 11 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (10 10 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:REWRITE MEMBERP-OF-CAR-SAME))
 )
(CLEAR-BINDING-OF-CONS
 (461 15 (:REWRITE CLEAR-BINDING-DOES-NOTHING))
 (120 15 (:DEFINITION STRIP-CARS))
 (81 43 (:REWRITE DEFAULT-CAR))
 (62 62 (:TYPE-PRESCRIPTION MEMBERP))
 (38 19 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (32 32 (:TYPE-PRESCRIPTION STRIP-CARS))
 (32 16 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (32 16 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (32 16 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (32 16 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (32 16 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (30 30 (:REWRITE STRIP-CARS-OF-NON-CONSP))
 (25 25 (:REWRITE DEFAULT-CDR))
 (22 10 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (22 1 (:REWRITE MEMBERP-OF-CONS))
 (19 19 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (19 19 (:REWRITE WFR-HACK5))
 (16 16 (:TYPE-PRESCRIPTION LEN))
 (16 16 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (16 16 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (16 16 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (16 16 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (16 16 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (16 16 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (15 15 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (15 15 (:REWRITE CLEAR-BINDING-OF-NOT-CONSP))
 (11 1 (:REWRITE STRIP-CARS-OF-CONS))
 (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
 (10 10 (:REWRITE CLR-DIFFERENTIAL))
 (4 1 (:REWRITE MEMBERP-OF-CONS-IRREL-STRONG))
 )
(CLEAR-BINDING-OF-CLEAR-BINDING
 (382 45 (:DEFINITION STRIP-CARS))
 (277 149 (:REWRITE DEFAULT-CAR))
 (128 64 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (88 88 (:TYPE-PRESCRIPTION STRIP-CARS))
 (88 44 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (88 44 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (88 44 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (88 44 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (81 81 (:REWRITE DEFAULT-CDR))
 (75 75 (:REWRITE WFR-HACK5))
 (66 48 (:REWRITE CLEAR-BINDING-OF-NOT-CONSP))
 (64 64 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (44 44 (:TYPE-PRESCRIPTION LEN))
 (44 44 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (44 44 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (44 44 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (44 44 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (44 44 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (44 44 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (42 42 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (42 19 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (19 19 (:TYPE-PRESCRIPTION BOOLEANP))
 (19 19 (:REWRITE CLR-DIFFERENTIAL))
 (19 1 (:REWRITE MEMBERP-OF-CONS-IRREL-STRONG))
 (1 1 (:REWRITE MEMBERP-OF-CONS-SAME))
 )
(ACL2-COUNT-CLEAR-BINDING-DECREASES
 (1109 11 (:LINEAR ACL2-COUNT-CAR-CDR-LINEAR))
 (835 390 (:REWRITE DEFAULT-+-2))
 (561 390 (:REWRITE DEFAULT-+-1))
 (402 48 (:DEFINITION STRIP-CARS))
 (326 292 (:REWRITE ACL2-COUNT-WHEN-STRING))
 (240 60 (:DEFINITION INTEGER-ABS))
 (232 116 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (218 215 (:REWRITE DEFAULT-CDR))
 (128 128 (:REWRITE FOLD-CONSTS-IN-+))
 (119 85 (:REWRITE DEFAULT-<-1))
 (116 116 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (110 85 (:REWRITE DEFAULT-<-2))
 (106 106 (:REWRITE WFR-HACK5))
 (99 93 (:REWRITE STRIP-CARS-OF-NON-CONSP))
 (94 47 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (94 47 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (94 47 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (92 47 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (90 90 (:TYPE-PRESCRIPTION STRIP-CARS))
 (90 30 (:DEFINITION LENGTH))
 (79 5 (:REWRITE MEMBERP-OF-CONS))
 (64 32 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (60 60 (:REWRITE DEFAULT-UNARY-MINUS))
 (54 48 (:REWRITE CLEAR-BINDING-OF-NOT-CONSP))
 (47 47 (:TYPE-PRESCRIPTION LEN))
 (47 47 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (47 47 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (47 47 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (47 47 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (47 47 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (47 47 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (42 42 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (32 32 (:TYPE-PRESCRIPTION BOOLEANP))
 (32 32 (:REWRITE CLR-DIFFERENTIAL))
 (30 30 (:REWRITE DEFAULT-REALPART))
 (30 30 (:REWRITE DEFAULT-NUMERATOR))
 (30 30 (:REWRITE DEFAULT-IMAGPART))
 (30 30 (:REWRITE DEFAULT-DENOMINATOR))
 (30 30 (:REWRITE DEFAULT-COERCE-2))
 (30 30 (:REWRITE DEFAULT-COERCE-1))
 (17 5 (:REWRITE MEMBERP-OF-CONS-IRREL-STRONG))
 )
(SET-TO-NIL-EQUAL-CLEAR-FIELD)
(CLEAR-FIELD-OF-CLEAR-FIELD
 (56 11 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (50 25 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (25 25 (:TYPE-PRESCRIPTION BOOLEANP))
 (25 25 (:REWRITE CLR-DIFFERENTIAL))
 (21 3 (:REWRITE GET-FIELD-OF-SET-FIELD-BOTH))
 (14 2 (:REWRITE CLEAR-FIELD-OF-SET-FIELD-DIFF))
 (12 3 (:REWRITE GET-FIELD-OF-SET-FIELD-DIFF-2))
 (12 3 (:REWRITE GET-FIELD-OF-SET-FIELD-DIFF-1))
 (4 1 (:REWRITE SET-FIELD-OF-SET-FIELD-DIFF-2))
 (4 1 (:REWRITE SET-FIELD-OF-SET-FIELD-DIFF-1))
 )
(CLEAR-FIELD-OF-SET-FIELDS
 (343 11 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (270 9 (:REWRITE GET-FIELD-OF-SET-FIELDS))
 (218 26 (:DEFINITION STRIP-CARS))
 (191 104 (:REWRITE DEFAULT-CAR))
 (106 53 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (78 57 (:REWRITE DEFAULT-CDR))
 (53 53 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (52 52 (:REWRITE WFR-HACK5))
 (50 50 (:TYPE-PRESCRIPTION STRIP-CARS))
 (50 25 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (50 25 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (50 25 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (50 25 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (38 19 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (37 18 (:REWRITE SET-FIELDS-WHEN-PAIRS-IS-NOT-A-CONSP))
 (37 18 (:REWRITE SET-FIELDS-OF-NON-CONS))
 (25 25 (:TYPE-PRESCRIPTION LEN))
 (25 25 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (25 25 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (25 25 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (25 25 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (25 25 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (25 25 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (23 23 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (19 19 (:TYPE-PRESCRIPTION BOOLEANP))
 (19 19 (:REWRITE CLR-DIFFERENTIAL))
 (19 1 (:REWRITE MEMBERP-OF-CONS-IRREL-STRONG))
 (15 15 (:REWRITE CLEAR-BINDING-OF-NOT-CONSP))
 (9 9 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (1 1 (:REWRITE MEMBERP-OF-CONS-SAME))
 )
(SET-FIELDS-OF-CLEAR-BINDING
 (311 8 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (252 8 (:REWRITE GET-FIELD-OF-SET-FIELDS))
 (76 9 (:DEFINITION STRIP-CARS))
 (70 41 (:REWRITE DEFAULT-CAR))
 (52 52 (:TYPE-PRESCRIPTION MEMBERP))
 (44 22 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (43 26 (:REWRITE DEFAULT-CDR))
 (34 12 (:REWRITE SET-FIELDS-BASE-CASE))
 (32 4 (:REWRITE CLEAR-BINDING-DOES-NOTHING))
 (24 18 (:REWRITE STRIP-CARS-OF-NON-CONSP))
 (22 22 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (22 12 (:REWRITE SET-FIELDS-WHEN-PAIRS-IS-NOT-A-CONSP))
 (22 12 (:REWRITE SET-FIELDS-OF-NON-CONS))
 (19 19 (:REWRITE WFR-HACK5))
 (18 18 (:TYPE-PRESCRIPTION STRIP-CARS))
 (18 9 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (18 9 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (18 9 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (18 9 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (18 9 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (18 9 (:DEFINITION ENDP))
 (16 8 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (10 8 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:TYPE-PRESCRIPTION LEN))
 (9 9 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (9 9 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (9 9 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (9 9 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (9 9 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (9 9 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (9 9 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 (8 8 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (8 8 (:REWRITE CLR-DIFFERENTIAL))
 (4 4 (:REWRITE CLEAR-BINDING-OF-NOT-CONSP))
 )
(CLEAR-FIELD-OF-SET-FIELDS-DIFF
 (190 7 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (150 5 (:REWRITE GET-FIELD-OF-SET-FIELDS))
 (44 22 (:REWRITE DEFAULT-CAR))
 (40 5 (:DEFINITION STRIP-CARS))
 (34 17 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (30 30 (:TYPE-PRESCRIPTION MEMBERP))
 (27 15 (:REWRITE DEFAULT-CDR))
 (26 13 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (17 17 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (13 13 (:TYPE-PRESCRIPTION BOOLEANP))
 (13 13 (:REWRITE CLR-DIFFERENTIAL))
 (11 11 (:REWRITE WFR-HACK5))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (10 10 (:REWRITE STRIP-CARS-OF-NON-CONSP))
 (10 10 (:REWRITE SET-FIELDS-WHEN-PAIRS-IS-NOT-A-CONSP))
 (10 10 (:REWRITE SET-FIELDS-OF-NON-CONS))
 (10 5 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (10 5 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (10 5 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (10 5 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (10 5 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (5 5 (:TYPE-PRESCRIPTION LEN))
 (5 5 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (5 5 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (5 5 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (5 5 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (5 5 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (5 5 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (5 5 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (5 5 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 )
(GET-FIELD-OF-CLEAR-FIELD-BOTH
 (12 6 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:REWRITE CLR-DIFFERENTIAL))
 (4 1 (:REWRITE GET-FIELD-OF-SET-FIELD-DIFF-2))
 (4 1 (:REWRITE GET-FIELD-OF-SET-FIELD-DIFF-1))
 (1 1 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 )
(CLR-OF-CLEAR-FIELD)
(CLR-OF-SET-FIELDS
 (296 8 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (241 16 (:REWRITE CLR-WHEN-NOT-IN-RKEYS))
 (240 8 (:REWRITE GET-FIELD-OF-SET-FIELDS))
 (64 32 (:REWRITE DEFAULT-CAR))
 (64 8 (:DEFINITION STRIP-CARS))
 (48 48 (:TYPE-PRESCRIPTION MEMBERP))
 (48 24 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (45 45 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (45 15 (:REWRITE SET::NEVER-IN-EMPTY))
 (41 25 (:REWRITE DEFAULT-CDR))
 (30 30 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (30 30 (:REWRITE SET::SUBSET-IN-2))
 (30 30 (:REWRITE SET::SUBSET-IN))
 (30 15 (:REWRITE SET::IN-TAIL))
 (28 14 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (24 24 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (16 16 (:TYPE-PRESCRIPTION STRIP-CARS))
 (16 16 (:REWRITE WFR-HACK5))
 (16 16 (:REWRITE STRIP-CARS-OF-NON-CONSP))
 (16 16 (:REWRITE NOT-CLR-WHEN-NOT-S))
 (16 8 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (16 8 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (16 8 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (16 8 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (16 8 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (15 15 (:REWRITE SET::SUBSET-IN-2-ALT))
 (15 15 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (15 15 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (15 15 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (14 14 (:TYPE-PRESCRIPTION BOOLEANP))
 (14 14 (:REWRITE CLR-DIFFERENTIAL))
 (13 13 (:REWRITE SET-FIELDS-WHEN-PAIRS-IS-NOT-A-CONSP))
 (13 13 (:REWRITE SET-FIELDS-OF-NON-CONS))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (8 8 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (8 8 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (8 8 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (8 8 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (8 8 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (8 8 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (8 8 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (8 8 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (8 8 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 )
(CLEAR-FIELD-DOES-NOTHING)
(CLR-OF-SET-FIELD-DIFF
 (228 7 (:REWRITE CLR-WHEN-NOT-IN-RKEYS))
 (104 5 (:REWRITE S-SAME-G-STRONG))
 (90 1 (:REWRITE IN-OF-IF))
 (88 1 (:REWRITE RKEYS-S-TWO))
 (64 2 (:REWRITE S==R))
 (55 1 (:DEFINITION SET::DELETE))
 (49 49 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (40 2 (:REWRITE SET::DELETE-IN))
 (36 14 (:REWRITE SET::IN-TAIL))
 (36 1 (:REWRITE SET::IN-INSERT))
 (32 32 (:REWRITE SET::SUBSET-IN))
 (32 16 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (30 2 (:REWRITE SET::DELETE-NONMEMBER-CANCEL))
 (28 28 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (24 12 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (23 10 (:REWRITE SET::NEVER-IN-EMPTY))
 (22 22 (:REWRITE SET::SUBSET-IN-2))
 (16 16 (:TYPE-PRESCRIPTION BOOLEANP))
 (16 16 (:REWRITE CLR-DIFFERENTIAL))
 (16 2 (:REWRITE SET::INSERT-IDENTITY))
 (12 12 (:REWRITE SET::SUBSET-IN-2-ALT))
 (12 2 (:REWRITE EQUAL-S-RECORD-EQUALITY))
 (11 11 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (11 11 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (11 11 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (10 2 (:REWRITE SET::INSERT-WHEN-EMPTY))
 (10 1 (:REWRITE EQUAL-EQUAL-A-HEAD-HACK))
 (8 4 (:REWRITE SET::TAIL-WHEN-EMPTY))
 (8 2 (:REWRITE TAG-LOCATION-ELIMINATION))
 (8 2 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (8 2 (:REWRITE INSERT-WHEN-EMPTY))
 (7 7 (:REWRITE NOT-CLR-WHEN-NOT-S))
 (6 2 (:REWRITE SET::DELETE-PRESERVES-EMPTY))
 (2 2 (:REWRITE SET::TAIL-PRESERVES-EMPTY))
 (2 2 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (2 2 (:REWRITE SET::HEAD-WHEN-EMPTY))
 (2 2 (:REWRITE HEAD-WHEN-EMPTY))
 (1 1 (:REWRITE SET::HEAD-UNIQUE))
 )
(G-OF-CLEAR-FIELD-SAME)
(CLR-NON-NIL-WHEN-GET-FIELD)
(CLR-NON-NIL-WHEN-GET-FIELD-2)
(CLR-NON-NIL-WHEN-GET-CLASS
 (2 1 (:REWRITE G-WHEN-NOT-IN-RKEYS-CHEAP))
 (1 1 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (1 1 (:REWRITE CLR-DIFFERENTIAL))
 )
