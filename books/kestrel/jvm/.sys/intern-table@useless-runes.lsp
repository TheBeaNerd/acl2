(JVM::ALL-STRINGP)
(JVM::INTERN-TABLEP)
(JVM::EMPTY-INTERN-TABLE)
(JVM::INTERN-TABLEP-OF-EMPTY-INTERN-TABLE)
(JVM::INTERN-TABLE-OKP
 (139 60 (:REWRITE DEFAULT-CDR))
 (129 32 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (116 8 (:REWRITE USE-ALL-ADDRESSP))
 (107 58 (:REWRITE DEFAULT-CAR))
 (106 8 (:REWRITE ADDRESSP-WHEN-ADDRESS-OR-NULLP-AND-NOT-NULL-REFP))
 (98 4 (:DEFINITION ADDRESS-OR-NULLP))
 (86 86 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (75 6 (:REWRITE ALL-ADDRESSP-WHEN-NOT-CONSP))
 (64 32 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (57 19 (:REWRITE JVM::ALISTP-WHEN-METHOD-PROGRAMP))
 (38 38 (:TYPE-PRESCRIPTION JVM::METHOD-PROGRAMP))
 (33 11 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 (32 32 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (30 30 (:TYPE-PRESCRIPTION MEMBERP))
 (28 28 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (19 19 (:REWRITE JVM::ALISTP-WHEN-JVM-INSTRUCTIONS-OKAYP))
 (18 18 (:REWRITE STRIP-CARS-OF-NON-CONSP))
 (12 12 (:REWRITE WFR-HACK5))
 (12 6 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (12 6 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (12 6 (:REWRITE ALL-ADDRESSP-WHEN-NOT-CONSP-CHEAP))
 (8 8 (:TYPE-PRESCRIPTION ADDRESS-OR-NULLP))
 (8 8 (:REWRITE USE-ALL-ADDRESSP-2))
 (8 8 (:REWRITE ADDRESSP-WHEN-IN-DOMAIN-OF-HEAPP))
 (7 7 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (7 7 (:REWRITE CLR-DIFFERENTIAL))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (6 6 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (6 6 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (6 6 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (6 6 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (6 6 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (4 4 (:DEFINITION NULL-REF))
 )
(JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-PAIR
 (135 32 (:REWRITE DEFAULT-CDR))
 (63 20 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (42 42 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (40 20 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (36 9 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (32 32 (:REWRITE CLR-DIFFERENTIAL))
 (20 20 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (20 20 (:REWRITE DEFAULT-CAR))
 (18 18 (:TYPE-PRESCRIPTION BOOLEANP))
 (3 1 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 )
(JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-PAIR-ALT
 (102 102 (:REWRITE CLR-DIFFERENTIAL))
 (90 30 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (72 72 (:TYPE-PRESCRIPTION BOOLEANP))
 (72 18 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (70 10 (:REWRITE GET-CLASS-OF-SET-FIELD))
 (60 60 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (60 30 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (40 10 (:REWRITE GET-CLASS-OF-SET-FIELD-IRREL-PAIR))
 (30 30 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 )
(JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-AD
 (211 58 (:REWRITE DEFAULT-CDR))
 (162 9 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-PAIR-ALT))
 (96 96 (:REWRITE CLR-DIFFERENTIAL))
 (93 30 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (92 17 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (82 82 (:TYPE-PRESCRIPTION BOOLEANP))
 (74 2 (:DEFINITION SUBSETP-EQUAL))
 (62 62 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (60 30 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (50 50 (:REWRITE DEFAULT-CAR))
 (36 36 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (36 18 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (36 9 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (36 9 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-PAIR))
 (34 17 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (34 17 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (34 17 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (32 8 (:REWRITE GET-CLASS-OF-SET-FIELD-IRREL-PAIR))
 (30 30 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (28 14 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (21 5 (:REWRITE MEMBERP-OF-CONS-IRREL-STRONG))
 (17 17 (:TYPE-PRESCRIPTION LEN))
 (17 17 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (17 17 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (17 17 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (17 17 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (14 14 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (10 10 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (3 1 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 (2 2 (:REWRITE MEMBERP-OF-CAR-SAME))
 )
(JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-WHEN-BOUND
 (306 78 (:REWRITE DEFAULT-CDR))
 (230 10 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-AD))
 (210 10 (:REWRITE MEMBER-EQUAL-BECOMES-MEMBERP))
 (163 10 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-PAIR-ALT))
 (144 42 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (122 122 (:REWRITE CLR-DIFFERENTIAL))
 (96 96 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (90 18 (:REWRITE SET::IN-TAIL))
 (84 42 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (83 83 (:TYPE-PRESCRIPTION BOOLEANP))
 (61 61 (:REWRITE DEFAULT-CAR))
 (42 42 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (40 40 (:TYPE-PRESCRIPTION MEMBERP))
 (37 10 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (37 10 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-PAIR))
 (37 10 (:REWRITE GET-CLASS-OF-SET-FIELD-IRREL-PAIR))
 (36 36 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (36 36 (:REWRITE SET::SUBSET-IN))
 (27 9 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (27 9 (:REWRITE SET::NEVER-IN-EMPTY))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (20 10 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (20 10 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (20 10 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (20 10 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (20 10 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (20 10 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (18 18 (:REWRITE SET::SUBSET-IN-2))
 (18 6 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (10 10 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (10 10 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (10 10 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (10 10 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (10 10 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (10 10 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (10 10 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (10 10 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (10 10 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (10 10 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (1 1 (:REWRITE SUBSET-HACK))
 )
(JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-WHEN-BOUND-SAME-HEAP
 (10 2 (:REWRITE SET::IN-TAIL))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:REWRITE SET::SUBSET-IN))
 (4 1 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 2 (:REWRITE SET::SUBSET-IN-2))
 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE SET::SUBSET-IN-2-ALT))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (1 1 (:REWRITE CLR-DIFFERENTIAL))
 )
(JVM::INTERN-TABLE-OKP-OF-SET-FIELD-2
 (138 6 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-AD))
 (126 6 (:REWRITE MEMBER-EQUAL-BECOMES-MEMBERP))
 (122 29 (:REWRITE DEFAULT-CDR))
 (110 6 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-WHEN-BOUND-SAME-HEAP))
 (99 59 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (74 6 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-PAIR-ALT))
 (59 59 (:REWRITE CLR-DIFFERENTIAL))
 (57 18 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (40 40 (:TYPE-PRESCRIPTION BOOLEANP))
 (38 38 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (36 18 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (34 6 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-WHEN-BOUND))
 (27 9 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (26 26 (:REWRITE DEFAULT-CAR))
 (26 8 (:REWRITE GET-CLASS-OF-SET-FIELD-IRREL-PAIR))
 (24 24 (:TYPE-PRESCRIPTION MEMBERP))
 (21 21 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (18 18 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (18 6 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-PAIR))
 (17 7 (:REWRITE SET::NEVER-IN-EMPTY))
 (14 14 (:REWRITE SET::SUBSET-IN-2))
 (14 14 (:REWRITE SET::SUBSET-IN))
 (14 7 (:REWRITE SET::IN-TAIL))
 (12 12 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (12 6 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (12 6 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (7 7 (:REWRITE SET::SUBSET-IN-2-ALT))
 (7 7 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (7 7 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (7 7 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (7 7 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (6 6 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (6 6 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (6 6 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (6 6 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (6 6 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (6 6 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (6 6 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (3 1 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 )
(JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG)
(JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG)
(JVM::INTERN-TABLE-OKP-OF-SET-FIELDS-IRREL-BINDINGS
 (285 7 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (236 7 (:REWRITE GET-FIELD-OF-SET-FIELDS))
 (184 49 (:REWRITE DEFAULT-CAR))
 (112 36 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (101 24 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (86 2 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-PAIR-ALT))
 (81 32 (:REWRITE DEFAULT-CDR))
 (76 2 (:DEFINITION SUBSETP-EQUAL))
 (72 36 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (70 70 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (64 2 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-AD))
 (48 24 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (48 24 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (48 24 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (48 24 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (46 46 (:TYPE-PRESCRIPTION STRIP-CARS))
 (45 24 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (42 21 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (38 2 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-WHEN-BOUND-SAME-HEAP))
 (36 36 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (34 2 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-WHEN-BOUND))
 (30 3 (:DEFINITION STRIP-CDRS))
 (25 25 (:TYPE-PRESCRIPTION LEN))
 (24 24 (:REWRITE WFR-HACK5))
 (24 24 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (24 24 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (24 24 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (24 24 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (23 23 (:REWRITE CLR-DIFFERENTIAL))
 (22 4 (:REWRITE MEMBERP-OF-CONS-IRREL-STRONG))
 (21 21 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (20 2 (:REWRITE RKEYS-OF-SET-FIELDS))
 (18 18 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (18 6 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 (17 17 (:TYPE-PRESCRIPTION BOOLEANP))
 (17 17 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (17 17 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (12 12 (:REWRITE SET-FIELDS-WHEN-PAIRS-IS-NOT-A-CONSP))
 (12 12 (:REWRITE SET-FIELDS-OF-NON-CONS))
 (10 10 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (9 9 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (7 7 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (7 7 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (7 3 (:REWRITE SET::NEVER-IN-EMPTY))
 (6 6 (:REWRITE SET::SUBSET-IN-2))
 (6 6 (:REWRITE SET::SUBSET-IN))
 (6 3 (:REWRITE SET::IN-TAIL))
 (5 5 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 3 (:REWRITE SET::SUBSET-IN-2-ALT))
 (3 3 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (3 3 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (3 3 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (3 3 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (2 2 (:TYPE-PRESCRIPTION ALL-EQUAL$))
 (2 2 (:REWRITE MEMBERP-OF-CAR-SAME))
 (2 2 (:REWRITE IN-OF-RKEYS-OF-SET-FIELDS-IRREL))
 (2 1 (:REWRITE ALL-EQUAL$-WHEN-NOT-EQUAL-OF-LEN-AND-1-CHEAP))
 (2 1 (:REWRITE ALL-EQUAL$-WHEN-NOT-CONSP-CHEAP))
 )
(JVM::INTERN-TABLE-OKP-OF-SET-FIELDS-IRREL-AD
 (315 7 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (289 8 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELDS-IRREL-BINDINGS))
 (266 7 (:REWRITE GET-FIELD-OF-SET-FIELDS))
 (195 15 (:DEFINITION STRIP-CARS))
 (184 44 (:REWRITE DEFAULT-CAR))
 (103 29 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (64 64 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (58 29 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (52 26 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (52 26 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (52 26 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (52 26 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (52 26 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (52 26 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (48 27 (:REWRITE DEFAULT-CDR))
 (34 2 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-WHEN-BOUND))
 (30 30 (:TYPE-PRESCRIPTION STRIP-CARS))
 (30 30 (:REWRITE STRIP-CARS-OF-NON-CONSP))
 (30 10 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 (29 29 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (27 27 (:TYPE-PRESCRIPTION LEN))
 (26 26 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (26 26 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (26 26 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (26 26 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (26 26 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (26 26 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (26 26 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (26 2 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-WHEN-BOUND-SAME-HEAP))
 (23 23 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (22 22 (:REWRITE WFR-HACK5))
 (12 12 (:REWRITE SET-FIELDS-WHEN-PAIRS-IS-NOT-A-CONSP))
 (12 12 (:REWRITE SET-FIELDS-OF-NON-CONS))
 (9 9 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (8 2 (:REWRITE RKEYS-OF-SET-FIELDS))
 (7 7 (:TYPE-PRESCRIPTION BOOLEANP))
 (7 7 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (7 7 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (7 7 (:REWRITE CLR-DIFFERENTIAL))
 (7 3 (:REWRITE SET::NEVER-IN-EMPTY))
 (6 6 (:REWRITE SET::SUBSET-IN-2))
 (6 6 (:REWRITE SET::SUBSET-IN))
 (6 3 (:REWRITE SET::IN-TAIL))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 3 (:REWRITE SET::SUBSET-IN-2-ALT))
 (3 3 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (3 3 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (3 3 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (3 3 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (2 2 (:TYPE-PRESCRIPTION ALL-EQUAL$))
 (2 2 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (2 2 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (2 2 (:REWRITE IN-OF-RKEYS-OF-SET-FIELDS-IRREL))
 (2 1 (:REWRITE ALL-EQUAL$-WHEN-NOT-EQUAL-OF-LEN-AND-1-CHEAP))
 (2 1 (:REWRITE ALL-EQUAL$-WHEN-NOT-CONSP-CHEAP))
 )
(JVM::INTERN-TABLE-OKP-OF-SET-FIELDS-IRREL-WHEN-BOUND
 (336 16 (:REWRITE MEMBER-EQUAL-BECOMES-MEMBERP))
 (315 7 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (289 8 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELDS-IRREL-BINDINGS))
 (266 7 (:REWRITE GET-FIELD-OF-SET-FIELDS))
 (195 15 (:DEFINITION STRIP-CARS))
 (184 44 (:REWRITE DEFAULT-CAR))
 (184 8 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELDS-IRREL-AD))
 (113 113 (:TYPE-PRESCRIPTION MEMBERP))
 (103 29 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (82 17 (:REWRITE SET::IN-TAIL))
 (64 64 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (58 29 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (48 27 (:REWRITE DEFAULT-CDR))
 (48 2 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-WHEN-BOUND-SAME-HEAP))
 (46 23 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (46 23 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (46 23 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (46 23 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (46 23 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (46 23 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (38 38 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (34 34 (:REWRITE SET::SUBSET-IN))
 (30 30 (:TYPE-PRESCRIPTION STRIP-CARS))
 (30 30 (:REWRITE STRIP-CARS-OF-NON-CONSP))
 (30 10 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 (29 29 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (27 18 (:REWRITE SET::SUBSET-IN-2))
 (27 9 (:REWRITE SET::NEVER-IN-EMPTY))
 (24 24 (:TYPE-PRESCRIPTION LEN))
 (24 8 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (23 23 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (23 23 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (23 23 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (23 23 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (23 23 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (23 23 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (23 23 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (22 22 (:REWRITE WFR-HACK5))
 (17 17 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (16 16 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (12 12 (:REWRITE SET-FIELDS-WHEN-PAIRS-IS-NOT-A-CONSP))
 (12 12 (:REWRITE SET-FIELDS-OF-NON-CONS))
 (10 10 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (10 10 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (10 10 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (10 10 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (7 7 (:TYPE-PRESCRIPTION BOOLEANP))
 (7 7 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (7 7 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (7 7 (:REWRITE CLR-DIFFERENTIAL))
 (7 1 (:REWRITE RKEYS-OF-SET-FIELDS))
 (4 4 (:REWRITE SET::SUBSET-TRANSITIVE))
 (4 2 (:REWRITE SET::EMPTYP-SUBSET-2))
 (4 2 (:REWRITE SET::EMPTYP-SUBSET))
 (3 3 (:REWRITE SUBSET-HACK))
 (2 2 (:TYPE-PRESCRIPTION ALL-EQUAL$))
 (2 2 (:REWRITE SET::PICK-A-POINT-SUBSET-STRATEGY))
 (2 2 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (2 2 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (2 2 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (2 1 (:REWRITE ALL-EQUAL$-WHEN-NOT-EQUAL-OF-LEN-AND-1-CHEAP))
 (2 1 (:REWRITE ALL-EQUAL$-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE IN-OF-RKEYS-OF-SET-FIELDS-IRREL))
 )
(JVM::INTERN-TABLE-OKP-OF-SET-FIELDS-IRREL-WHEN-BOUND-SAME-HEAP
 (10 2 (:REWRITE SET::IN-TAIL))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:REWRITE SET::SUBSET-IN))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE SET::NEVER-IN-EMPTY))
 (2 2 (:REWRITE SET::SUBSET-IN-2))
 (2 1 (:REWRITE SET-FIELDS-BASE-CASE))
 (1 1 (:REWRITE SET::SUBSET-IN-2-ALT))
 (1 1 (:REWRITE SET-FIELDS-WHEN-PAIRS-IS-NOT-A-CONSP))
 (1 1 (:REWRITE SET-FIELDS-OF-NON-CONS))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (1 1 (:DEFINITION ENDP))
 )
(JVM::STRING-HAS-BEEN-INTERNEDP)
(JVM::BOOLEANP-OF-STRING-HAS-BEEN-INTERNEDP)
(JVM::STRING-HAS-BEEN-INTERNEDP-OF-EMPTY-INTERN-TABLE)
(JVM::GET-INTERNED-STRING)
(JVM::GET-INTERNED-STRING-OF-EMPTY-INTERN-TABLE)
(JVM::SET-INTERNED-STRING)
(JVM::GET-INTERNED-STRING-OF-SET-INTERNED-STRING-SAME
 (1 1 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(JVM::STRING-HAS-BEEN-INTERNEDP-OF-SET-INTERNED-STRING-SAME
 (1 1 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(JVM::STRING-HAS-BEEN-INTERNEDP-OF-SET-INTERNED-STRING-DIFF
 (3 3 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (3 3 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (2 1 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (1 1 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE CLR-DIFFERENTIAL))
 )
(JVM::NOT-MEMBERP-OF-STRIP-CDRS-WHEN-INTERN-TABLE-OKP
 (111 25 (:REWRITE DEFAULT-CDR))
 (54 16 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (40 8 (:REWRITE SET::IN-TAIL))
 (36 36 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (36 7 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (32 16 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (28 1 (:DEFINITION SUBSETP-EQUAL))
 (18 1 (:REWRITE MEMBER-EQUAL-BECOMES-MEMBERP))
 (17 17 (:REWRITE DEFAULT-CAR))
 (16 16 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (16 16 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (16 16 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (16 16 (:REWRITE SET::SUBSET-IN))
 (16 8 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (14 7 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (14 7 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (14 7 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (13 10 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (12 4 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (12 4 (:REWRITE SET::NEVER-IN-EMPTY))
 (10 10 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (10 10 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (10 10 (:REWRITE CLR-DIFFERENTIAL))
 (8 8 (:REWRITE SET::SUBSET-IN-2))
 (7 7 (:TYPE-PRESCRIPTION LEN))
 (7 7 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (7 7 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (7 7 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (7 7 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (6 6 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (6 6 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (6 2 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 (6 1 (:REWRITE MEMBERP-OF-CONS-IRREL-STRONG))
 (5 5 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (4 4 (:REWRITE SET::SUBSET-IN-2-ALT))
 (4 4 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (4 4 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (4 4 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (3 3 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(JVM::INTERN-TABLE-OKP-OF-INIT-REF-IN-HEAP
 (51 1 (:REWRITE SET-FIELD-OF-GET-FIELD-SAME-ERIC-2))
 (50 1 (:REWRITE JVM::INTERN-TABLE-OKP-OF-SET-FIELD-IRREL-WHEN-BOUND-SAME-HEAP))
 (44 1 (:REWRITE GET-FIELD-OF-SET-FIELDS))
 (16 16 (:TYPE-PRESCRIPTION GEN-INIT-BINDINGS))
 (15 2 (:REWRITE SET::SUBSET-IN-2-ALT))
 (13 4 (:REWRITE SET::SUBSET-IN-2))
 (13 1 (:DEFINITION STRIP-CARS))
 (12 3 (:REWRITE SET::IN-TAIL))
 (10 10 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (7 7 (:TYPE-PRESCRIPTION MEMBERP))
 (7 2 (:REWRITE DEFAULT-CAR))
 (7 1 (:REWRITE RKEYS-OF-SET-FIELDS))
 (6 6 (:REWRITE SET::SUBSET-IN))
 (6 2 (:REWRITE SET::NEVER-IN-EMPTY))
 (6 1 (:REWRITE SET-FIELDS-BASE-CASE))
 (6 1 (:REWRITE JVM::GET-SUPERCLASSES-AUX-OPENER))
 (5 2 (:REWRITE STRIP-CARS-OF-NON-CONSP))
 (4 4 (:TYPE-PRESCRIPTION SET::SUBSET-TYPE))
 (4 4 (:REWRITE SET::SUBSET-TRANSITIVE))
 (4 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (4 2 (:REWRITE SET::EMPTYP-SUBSET-2))
 (4 2 (:REWRITE SET::EMPTYP-SUBSET))
 (4 1 (:REWRITE SET-FIELDS-WHEN-PAIRS-IS-NOT-A-CONSP))
 (4 1 (:REWRITE SET-FIELDS-OF-NON-CONS))
 (4 1 (:DEFINITION ENDP))
 (3 1 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (3 1 (:REWRITE NOT-MEMBERP-OF-CLASS-PAIR-AND-STRIP-CARS-OF-GEN-INIT-BINDINGS))
 (3 1 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (2 2 (:TYPE-PRESCRIPTION STRIP-CARS))
 (2 2 (:TYPE-PRESCRIPTION LEN))
 (2 2 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (2 2 (:TYPE-PRESCRIPTION JVM::CLASS-TABLEP))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP))
 (2 2 (:TYPE-PRESCRIPTION ALL-EQUAL$))
 (2 2 (:REWRITE SUBSET-HACK))
 (2 2 (:REWRITE SET::PICK-A-POINT-SUBSET-STRATEGY))
 (2 2 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (2 2 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (2 2 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (2 2 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (2 2 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 (2 2 (:REWRITE CLR-DIFFERENTIAL))
 (2 1 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (2 1 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (2 1 (:REWRITE MEMBERP-WHEN-NOT-CONSP-CHEAP))
 (2 1 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (2 1 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (2 1 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (2 1 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (2 1 (:REWRITE ALL-EQUAL$-WHEN-NOT-EQUAL-OF-LEN-AND-1-CHEAP))
 (2 1 (:REWRITE ALL-EQUAL$-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (1 1 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (1 1 (:REWRITE WFR-HACK5))
 (1 1 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (1 1 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-AND-NOT-INTERSECTION-EQUAL-CHEAP))
 (1 1 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (1 1 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (1 1 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (1 1 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (1 1 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (1 1 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (1 1 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (1 1 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (1 1 (:REWRITE IN-OF-RKEYS-OF-SET-FIELDS-IRREL))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(JVM::GET-FIELD-OF-GET-INTERNED-STRING-AND-CLASS-PAIR
 (125 55 (:REWRITE DEFAULT-CAR))
 (118 38 (:REWRITE DEFAULT-CDR))
 (90 30 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (60 60 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (60 30 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (37 22 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (30 30 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (22 22 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (22 22 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (22 22 (:REWRITE CLR-DIFFERENTIAL))
 (15 15 (:TYPE-PRESCRIPTION BOOLEANP))
 (14 14 (:REWRITE WFR-HACK5))
 )
(JVM::INTERN-TABLE-OKP-OF-ACONS
 (9 4 (:REWRITE DEFAULT-CDR))
 (3 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (3 1 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (2 2 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (2 2 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (2 2 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE CLR-DIFFERENTIAL))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(JVM::NOT-MEMBER-EQUAL-OF-NEW-AD-OF-RKEYS-AND-STRIP-CDRS-WHEN-INTERN-TABLE-OKP
 (1 1 (:REWRITE NEW-AD-KNOWN))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-TWO))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-MAIN))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL-ALT))
 (1 1 (:REWRITE IN-RKEYS-WHEN-GET-FIELD-NON-NIL))
 )
(JVM::NOT-NULL-REFP-OF-GET-INTERNED-STRING
 (122 57 (:REWRITE DEFAULT-CDR))
 (119 10 (:REWRITE ADDRESSP-WHEN-ADDRESS-OR-NULLP-AND-NOT-NULL-REFP))
 (118 10 (:REWRITE USE-ALL-ADDRESSP))
 (109 5 (:DEFINITION ADDRESS-OR-NULLP))
 (102 26 (:REWRITE JVM::CONSP-OF-CAR-WHEN-FIELD-INFO-ALISTP))
 (95 61 (:REWRITE DEFAULT-CAR))
 (89 10 (:REWRITE ALL-ADDRESSP-WHEN-NOT-CONSP))
 (68 68 (:TYPE-PRESCRIPTION JVM::FIELD-INFO-ALISTP))
 (52 26 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (42 42 (:TYPE-PRESCRIPTION STRIP-CDRS))
 (42 14 (:REWRITE JVM::ALISTP-WHEN-METHOD-PROGRAMP))
 (30 30 (:TYPE-PRESCRIPTION MEMBERP))
 (28 28 (:TYPE-PRESCRIPTION JVM::METHOD-PROGRAMP))
 (26 26 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (24 8 (:REWRITE JVM::FIELD-INFO-ALISTP-OF-CDR))
 (20 10 (:REWRITE ALL-ADDRESSP-WHEN-NOT-CONSP-CHEAP))
 (17 16 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (16 16 (:REWRITE CLR-DIFFERENTIAL))
 (14 14 (:REWRITE JVM::ALISTP-WHEN-JVM-INSTRUCTIONS-OKAYP))
 (13 13 (:REWRITE STRIP-CARS-OF-NON-CONSP))
 (12 12 (:REWRITE WFR-HACK5))
 (12 6 (:REWRITE MEMBERP-WHEN-SINGLETON-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-NOT-CONS-OF-CDR-CHEAP))
 (12 6 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-CDR-CHEAP))
 (12 6 (:REWRITE JVM::MEMBER-WHEN-NOT-MEMBERP-OF-CDR-CHEAP))
 (11 11 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CDR-WRONG))
 (11 11 (:REWRITE JVM::NOT-EQUAL-CONSTANT-WHEN-CAR-WRONG))
 (11 11 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (11 11 (:REWRITE LOOKUP-EQUAL-WHEN-NOT-ASSOC-EQUAL-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION ADDRESS-OR-NULLP))
 (10 10 (:REWRITE USE-ALL-ADDRESSP-2))
 (10 10 (:REWRITE ADDRESSP-WHEN-IN-DOMAIN-OF-HEAPP))
 (6 6 (:TYPE-PRESCRIPTION LEN))
 (6 6 (:REWRITE NOT-MEMBERP-WHEN-MEMBERP-OF-TAKE))
 (6 6 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-2))
 (6 6 (:REWRITE MEMBERP-WHEN-SUBSETP-EQUAL-1))
 (6 6 (:REWRITE MEMBERP-WHEN-NOT-EQUAL-OF-CAR-CHEAP))
 (6 6 (:REWRITE MEMBERP-WHEN-MEMBERP-OF-FIRSTN))
 (6 6 (:REWRITE MEMBERP-OF-CONSTANT-WHEN-NOT-MEMBER-OF-CONSTANT))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP))
 )
