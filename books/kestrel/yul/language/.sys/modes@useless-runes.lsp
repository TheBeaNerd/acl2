(YUL::MODEP)
(YUL::CONSP-WHEN-MODEP)
(YUL::MODE-KIND$INLINE)
(YUL::MODE-KIND-POSSIBILITIES)
(YUL::MODE-FIX$INLINE)
(YUL::MODEP-OF-MODE-FIX)
(YUL::MODE-FIX-WHEN-MODEP)
(YUL::MODE-FIX$INLINE)
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(YUL::MODE-EQUIV$INLINE)
(YUL::MODE-EQUIV-IS-AN-EQUIVALENCE)
(YUL::MODE-EQUIV-IMPLIES-EQUAL-MODE-FIX-1)
(YUL::MODE-FIX-UNDER-MODE-EQUIV)
(YUL::EQUAL-OF-MODE-FIX-1-FORWARD-TO-MODE-EQUIV)
(YUL::EQUAL-OF-MODE-FIX-2-FORWARD-TO-MODE-EQUIV)
(YUL::MODE-EQUIV-OF-MODE-FIX-1-FORWARD)
(YUL::MODE-EQUIV-OF-MODE-FIX-2-FORWARD)
(YUL::MODE-KIND$INLINE-OF-MODE-FIX-X
 (1 1 (:REWRITE YUL::MODE-FIX-WHEN-MODEP))
 )
(YUL::MODE-KIND$INLINE-MODE-EQUIV-CONGRUENCE-ON-X)
(YUL::CONSP-OF-MODE-FIX)
(YUL::TAG-WHEN-MODEP-FORWARD)
(YUL::TAG-OF-MODE-FIX)
(YUL::MODE-REGULAR)
(YUL::RETURN-TYPE-OF-MODE-REGULAR)
(YUL::MODE-FIX-WHEN-REGULAR
 (3 1 (:REWRITE YUL::MODE-FIX-WHEN-MODEP))
 (2 2 (:TYPE-PRESCRIPTION YUL::MODEP))
 )
(YUL::EQUAL-OF-MODE-REGULAR
 (3 3 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(YUL::MODE-BREAK)
(YUL::RETURN-TYPE-OF-MODE-BREAK)
(YUL::MODE-FIX-WHEN-BREAK
 (3 1 (:REWRITE YUL::MODE-FIX-WHEN-MODEP))
 (2 2 (:TYPE-PRESCRIPTION YUL::MODEP))
 (1 1 (:REWRITE YUL::MODE-FIX-WHEN-REGULAR))
 )
(YUL::EQUAL-OF-MODE-BREAK
 (3 3 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (2 2 (:REWRITE YUL::MODE-FIX-WHEN-REGULAR))
 )
(YUL::MODE-CONTINUE)
(YUL::RETURN-TYPE-OF-MODE-CONTINUE)
(YUL::MODE-FIX-WHEN-CONTINUE
 (3 1 (:REWRITE YUL::MODE-FIX-WHEN-MODEP))
 (2 2 (:TYPE-PRESCRIPTION YUL::MODEP))
 (1 1 (:REWRITE YUL::MODE-FIX-WHEN-REGULAR))
 (1 1 (:REWRITE YUL::MODE-FIX-WHEN-BREAK))
 )
(YUL::EQUAL-OF-MODE-CONTINUE
 (3 3 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (2 2 (:REWRITE YUL::MODE-FIX-WHEN-REGULAR))
 (2 2 (:REWRITE YUL::MODE-FIX-WHEN-BREAK))
 )
(YUL::MODE-LEAVE)
(YUL::RETURN-TYPE-OF-MODE-LEAVE)
(YUL::MODE-FIX-WHEN-LEAVE
 (3 1 (:REWRITE YUL::MODE-FIX-WHEN-MODEP))
 (2 2 (:TYPE-PRESCRIPTION YUL::MODEP))
 (1 1 (:REWRITE YUL::MODE-FIX-WHEN-REGULAR))
 (1 1 (:REWRITE YUL::MODE-FIX-WHEN-CONTINUE))
 (1 1 (:REWRITE YUL::MODE-FIX-WHEN-BREAK))
 )
(YUL::EQUAL-OF-MODE-LEAVE
 (3 3 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (2 2 (:REWRITE YUL::MODE-FIX-WHEN-REGULAR))
 (2 2 (:REWRITE YUL::MODE-FIX-WHEN-CONTINUE))
 (2 2 (:REWRITE YUL::MODE-FIX-WHEN-BREAK))
 )
(YUL::MODE-FIX-REDEF
 (3 1 (:REWRITE YUL::MODE-FIX-WHEN-MODEP))
 (2 2 (:TYPE-PRESCRIPTION YUL::MODEP))
 )
(YUL::MODE-SETP)
(YUL::BOOLEANP-OFMODE-SETP
 (6 2 (:DEFINITION YUL::MODE-SETP))
 (2 2 (:TYPE-PRESCRIPTION YUL::MODEP))
 (2 2 (:TYPE-PRESCRIPTION FAST-<<))
 )
(YUL::SETP-WHEN-MODE-SETP)
(YUL::MODEP-OF-HEAD-WHEN-MODE-SETP
 (25 1 (:REWRITE FAST-<<-IS-<<))
 (19 5 (:REWRITE <<-TRICHOTOMY))
 (17 3 (:REWRITE <<-ASYMMETRIC))
 (12 12 (:TYPE-PRESCRIPTION <<))
 (8 8 (:TYPE-PRESCRIPTION SET::SFIX))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE <<-TRANSITIVE))
 (4 4 (:TYPE-PRESCRIPTION FAST-<<))
 (4 4 (:REWRITE DEFAULT-CDR))
 (4 1 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 )
(YUL::MODE-SETP-OF-TAIL-WHEN-MODE-SETP
 (57 15 (:REWRITE <<-TRICHOTOMY))
 (51 9 (:REWRITE <<-ASYMMETRIC))
 (15 15 (:REWRITE <<-TRANSITIVE))
 (14 14 (:REWRITE DEFAULT-CDR))
 (11 11 (:TYPE-PRESCRIPTION SET::SFIX))
 (9 9 (:REWRITE DEFAULT-CAR))
 (4 4 (:TYPE-PRESCRIPTION YUL::MODEP))
 (4 4 (:TYPE-PRESCRIPTION FAST-<<))
 (3 1 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 )
(YUL::MODE-SETP-OF-INSERT
 (2673 179 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (1763 227 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (1500 1231 (:REWRITE <<-TRANSITIVE))
 (1206 1194 (:REWRITE DEFAULT-CDR))
 (949 941 (:REWRITE DEFAULT-CAR))
 (714 90 (:REWRITE SET::HEAD-WHEN-EMPTYP))
 (656 32 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (640 28 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (300 60 (:REWRITE SET::INSERT-IDENTITY))
 (227 227 (:REWRITE SET::IN-SET))
 (180 180 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (120 60 (:REWRITE SET::IN-TAIL))
 (90 90 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (9 9 (:REWRITE <<-IRREFLEXIVE))
 )
(YUL::MODEP-WHEN-IN-MODE-SETP-BINDS-FREE-X
 (32 32 (:TYPE-PRESCRIPTION SET::SFIX))
 (25 1 (:REWRITE FAST-<<-IS-<<))
 (19 5 (:REWRITE <<-TRICHOTOMY))
 (17 3 (:REWRITE <<-ASYMMETRIC))
 (12 12 (:TYPE-PRESCRIPTION <<))
 (5 5 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE <<-TRANSITIVE))
 (4 4 (:REWRITE DEFAULT-CDR))
 (3 3 (:TYPE-PRESCRIPTION FAST-<<))
 (1 1 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 )
(YUL::MODE-SETP-OF-UNION
 (8761 2227 (:REWRITE <<-TRICHOTOMY))
 (7032 12 (:REWRITE SET::INSERT-IDENTITY))
 (7008 12 (:REWRITE SET::UNION-IN))
 (6960 48 (:REWRITE SET::IN-TAIL))
 (6726 566 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (5033 864 (:REWRITE <<-ASYMMETRIC))
 (4820 132 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (3576 18 (:REWRITE SET::UNION-EMPTYP))
 (2856 2784 (:REWRITE DEFAULT-CDR))
 (2748 12 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (2248 2220 (:REWRITE <<-TRANSITIVE))
 (1904 1904 (:REWRITE DEFAULT-CAR))
 (1238 36 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (838 24 (:REWRITE SET::UNION-EMPTYP-Y))
 (833 833 (:REWRITE YUL::MODEP-WHEN-IN-MODE-SETP-BINDS-FREE-X))
 (782 24 (:REWRITE SET::UNION-EMPTYP-X))
 (566 566 (:REWRITE SET::IN-SET))
 (326 12 (:REWRITE SET::HEAD-WHEN-EMPTYP))
 (215 2 (:REWRITE SET::EMPTYP-SFIX-CANCEL))
 (120 120 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (12 12 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (7 7 (:REWRITE <<-IRREFLEXIVE))
 )
(YUL::MODE-SETP-OF-DIFFERENCE
 (57 15 (:REWRITE <<-TRICHOTOMY))
 (51 9 (:REWRITE <<-ASYMMETRIC))
 (27 3 (:REWRITE SET::SUBSET-DIFFERENCE))
 (24 6 (:REWRITE SET::IN-TAIL))
 (22 22 (:REWRITE YUL::MODEP-WHEN-IN-MODE-SETP-BINDS-FREE-X))
 (22 2 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (18 6 (:REWRITE SET::DIFFERENCE-EMPTYP-Y))
 (18 6 (:REWRITE SET::DIFFERENCE-EMPTYP-X))
 (15 15 (:REWRITE <<-TRANSITIVE))
 (15 9 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (13 3 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (12 12 (:TYPE-PRESCRIPTION SET::SFIX))
 (12 12 (:REWRITE DEFAULT-CDR))
 (9 9 (:REWRITE DEFAULT-CAR))
 (9 3 (:REWRITE SET::NEVER-IN-EMPTY))
 (9 3 (:REWRITE SET::EMPTYP-SUBSET-2))
 (9 3 (:REWRITE SET::EMPTYP-SUBSET))
 (8 2 (:REWRITE SET::INSERT-IDENTITY))
 (5 5 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (5 5 (:REWRITE SET::HEAD-WHEN-EMPTYP))
 (4 2 (:REWRITE SET::DIFFERENCE-IN))
 (3 3 (:REWRITE SET::PICK-A-POINT-SUBSET-CONSTRAINT-HELPER))
 (2 2 (:REWRITE SET::HEAD-UNIQUE))
 )
(YUL::MODE-SETP-OF-DELETE
 (57 15 (:REWRITE <<-TRICHOTOMY))
 (51 9 (:REWRITE <<-ASYMMETRIC))
 (32 4 (:REWRITE SET::DELETE-NONMEMBER-CANCEL))
 (15 15 (:REWRITE YUL::MODEP-WHEN-IN-MODE-SETP-BINDS-FREE-X))
 (15 15 (:REWRITE <<-TRANSITIVE))
 (14 14 (:TYPE-PRESCRIPTION SET::IN-TYPE))
 (12 12 (:REWRITE DEFAULT-CDR))
 (12 4 (:REWRITE SET::NEVER-IN-EMPTY))
 (12 2 (:REWRITE SET::INSERT-WHEN-EMPTYP))
 (11 11 (:TYPE-PRESCRIPTION YUL::MODEP))
 (11 11 (:TYPE-PRESCRIPTION FAST-<<))
 (9 9 (:REWRITE DEFAULT-CAR))
 (9 3 (:REWRITE SET::DELETE-PRESERVES-EMPTYP))
 (8 4 (:REWRITE SET::IN-TAIL))
 (8 2 (:REWRITE SET::INSERT-IDENTITY))
 (6 6 (:TYPE-PRESCRIPTION SET::SFIX))
 (6 6 (:REWRITE SET::TAIL-WHEN-EMPTYP))
 (6 1 (:REWRITE SET::SFIX-WHEN-EMPTYP))
 (5 5 (:REWRITE SET::IN-TAIL-OR-HEAD))
 (5 5 (:REWRITE SET::HEAD-WHEN-EMPTYP))
 (4 2 (:REWRITE SET::DELETE-IN))
 (2 2 (:REWRITE SET::HEAD-UNIQUE))
 )
(YUL::MODE-SET-FIX
 (1 1 (:TYPE-PRESCRIPTION YUL::MODE-SET-FIX))
 )
(YUL::MODE-SETP-OF-MODE-SET-FIX)
(YUL::MODE-SET-FIX-WHEN-MODE-SETP
 (13 13 (:TYPE-PRESCRIPTION YUL::MODE-SET-FIX))
 )
(YUL::EMPTYP-MODE-SET-FIX
 (4 2 (:REWRITE YUL::MODE-SET-FIX-WHEN-MODE-SETP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (24 24 (:TYPE-PRESCRIPTION YUL::MODE-SET-FIX))
 )
(YUL::MODE-SET-EQUIV$INLINE
 (4 4 (:TYPE-PRESCRIPTION YUL::MODE-SET-FIX))
 )
(YUL::MODE-SET-EQUIV-IS-AN-EQUIVALENCE)
(YUL::MODE-SET-EQUIV-IMPLIES-EQUAL-MODE-SET-FIX-1)
(YUL::MODE-SET-FIX-UNDER-MODE-SET-EQUIV)
(YUL::EQUAL-OF-MODE-SET-FIX-1-FORWARD-TO-MODE-SET-EQUIV)
(YUL::EQUAL-OF-MODE-SET-FIX-2-FORWARD-TO-MODE-SET-EQUIV)
(YUL::MODE-SET-EQUIV-OF-MODE-SET-FIX-1-FORWARD)
(YUL::MODE-SET-EQUIV-OF-MODE-SET-FIX-2-FORWARD)
(YUL::MODE-SET-RESULTP)
(YUL::CONSP-WHEN-MODE-SET-RESULTP)
(YUL::MODE-SET-RESULT-KIND$INLINE)
(YUL::MODE-SET-RESULT-KIND-POSSIBILITIES)
(YUL::MODE-SET-RESULT-FIX$INLINE
 (1 1 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 )
(YUL::MODE-SET-RESULTP-OF-MODE-SET-RESULT-FIX
 (21 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (11 1 (:REWRITE YUL::MODE-SET-FIX-WHEN-MODE-SETP))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (3 3 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 )
(YUL::MODE-SET-RESULT-FIX-WHEN-MODE-SET-RESULTP)
(YUL::MODE-SET-RESULT-FIX$INLINE
 (3 3 (:DEFINITION STRIP-CARS))
 (3 3 (:DEFINITION ALISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (24 24 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 )
(YUL::MODE-SET-RESULT-EQUIV$INLINE
 (4 4 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 )
(YUL::MODE-SET-RESULT-EQUIV-IS-AN-EQUIVALENCE)
(YUL::MODE-SET-RESULT-EQUIV-IMPLIES-EQUAL-MODE-SET-RESULT-FIX-1)
(YUL::MODE-SET-RESULT-FIX-UNDER-MODE-SET-RESULT-EQUIV)
(YUL::EQUAL-OF-MODE-SET-RESULT-FIX-1-FORWARD-TO-MODE-SET-RESULT-EQUIV)
(YUL::EQUAL-OF-MODE-SET-RESULT-FIX-2-FORWARD-TO-MODE-SET-RESULT-EQUIV)
(YUL::MODE-SET-RESULT-EQUIV-OF-MODE-SET-RESULT-FIX-1-FORWARD)
(YUL::MODE-SET-RESULT-EQUIV-OF-MODE-SET-RESULT-FIX-2-FORWARD)
(YUL::MODE-SET-RESULT-KIND$INLINE-OF-MODE-SET-RESULT-FIX-X
 (6 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (5 1 (:DEFINITION FTY::RESERRP))
 (2 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (1 1 (:REWRITE YUL::MODE-SET-RESULT-FIX-WHEN-MODE-SET-RESULTP))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(YUL::MODE-SET-RESULT-KIND$INLINE-MODE-SET-RESULT-EQUIV-CONGRUENCE-ON-X)
(YUL::MODE-SET-RESULT-OK->GET$INLINE
 (1 1 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK->GET$INLINE))
 )
(YUL::MODE-SETP-OF-MODE-SET-RESULT-OK->GET
 (17 2 (:DEFINITION YUL::MODE-SETP))
 (14 1 (:REWRITE YUL::MODE-SET-FIX-WHEN-MODE-SETP))
 (8 1 (:DEFINITION YUL::MODE-SET-FIX))
 (3 3 (:TYPE-PRESCRIPTION YUL::MODEP))
 (3 3 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK->GET$INLINE))
 (3 3 (:TYPE-PRESCRIPTION FAST-<<))
 )
(YUL::MODE-SET-RESULT-OK->GET$INLINE-OF-MODE-SET-RESULT-FIX-X
 (109 109 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 (54 18 (:REWRITE YUL::MODE-SET-RESULT-FIX-WHEN-MODE-SET-RESULTP))
 (36 36 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULTP))
 (26 16 (:TYPE-PRESCRIPTION YUL::MODE-SET-FIX))
 (24 16 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK->GET$INLINE))
 )
(YUL::MODE-SET-RESULT-OK->GET$INLINE-MODE-SET-RESULT-EQUIV-CONGRUENCE-ON-X)
(YUL::MODE-SET-RESULT-OK->GET-WHEN-WRONG-KIND
 (12 12 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK->GET$INLINE))
 )
(YUL::MODE-SET-RESULT-OK
 (3 1 (:DEFINITION YUL::MODE-SETP))
 (1 1 (:TYPE-PRESCRIPTION YUL::MODEP))
 (1 1 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK))
 (1 1 (:TYPE-PRESCRIPTION FAST-<<))
 )
(YUL::RETURN-TYPE-OF-MODE-SET-RESULT-OK
 (22 2 (:REWRITE YUL::MODE-SET-FIX-WHEN-MODE-SETP))
 (15 15 (:TYPE-PRESCRIPTION YUL::MODE-SET-FIX))
 (10 10 (:TYPE-PRESCRIPTION YUL::MODEP))
 (10 10 (:TYPE-PRESCRIPTION FAST-<<))
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (3 3 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(YUL::MODE-SET-RESULT-OK->GET-OF-MODE-SET-RESULT-OK
 (68 68 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK))
 (27 27 (:TYPE-PRESCRIPTION YUL::MODE-SET-FIX))
 (16 8 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK->GET$INLINE))
 )
(YUL::MODE-SET-RESULT-OK-OF-FIELDS
 (42 7 (:DEFINITION YUL::MODE-SETP))
 (13 13 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK->GET$INLINE))
 (13 13 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 (10 10 (:TYPE-PRESCRIPTION YUL::MODEP))
 (10 10 (:TYPE-PRESCRIPTION FAST-<<))
 (6 3 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK))
 (3 1 (:REWRITE YUL::MODE-SET-RESULT-FIX-WHEN-MODE-SET-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULTP))
 )
(YUL::MODE-SET-RESULT-FIX-WHEN-OK
 (34 6 (:DEFINITION YUL::MODE-SETP))
 (13 13 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK->GET$INLINE))
 (13 13 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 (8 8 (:TYPE-PRESCRIPTION YUL::MODEP))
 (8 8 (:TYPE-PRESCRIPTION FAST-<<))
 (6 3 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK))
 (3 1 (:REWRITE YUL::MODE-SET-RESULT-FIX-WHEN-MODE-SET-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULTP))
 )
(YUL::EQUAL-OF-MODE-SET-RESULT-OK)
(YUL::MODE-SET-RESULT-OK-OF-MODE-SET-FIX-GET
 (34 6 (:DEFINITION YUL::MODE-SETP))
 (9 6 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK))
 (8 8 (:TYPE-PRESCRIPTION YUL::MODEP))
 (8 8 (:TYPE-PRESCRIPTION FAST-<<))
 )
(YUL::MODE-SET-RESULT-OK-MODE-SET-EQUIV-CONGRUENCE-ON-GET)
(YUL::MODE-SET-RESULT-ERR->GET$INLINE
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(YUL::RESERRP-OF-MODE-SET-RESULT-ERR->GET
 (93 3 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (15 6 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(YUL::MODE-SET-RESULT-ERR->GET$INLINE-OF-MODE-SET-RESULT-FIX-X
 (140 7 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (126 7 (:DEFINITION FTY::RESERRP))
 (74 16 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (52 52 (:TYPE-PRESCRIPTION STRIP-CARS))
 (29 5 (:DEFINITION ALISTP))
 (24 8 (:REWRITE YUL::MODE-SET-RESULT-FIX-WHEN-MODE-SET-RESULTP))
 (21 21 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 (20 20 (:TYPE-PRESCRIPTION ALISTP))
 (16 16 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULTP))
 (7 7 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (5 5 (:DEFINITION STRIP-CARS))
 (3 3 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 )
(YUL::MODE-SET-RESULT-ERR->GET$INLINE-MODE-SET-RESULT-EQUIV-CONGRUENCE-ON-X)
(YUL::MODE-SET-RESULT-ERR->GET-WHEN-WRONG-KIND
 (3 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (1 1 (:DEFINITION FTY::RESERRP))
 )
(YUL::MODE-SET-RESULT-ERR
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(YUL::RETURN-TYPE-OF-MODE-SET-RESULT-ERR)
(YUL::MODE-SET-RESULT-ERR->GET-OF-MODE-SET-RESULT-ERR
 (50 8 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (36 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (34 1 (:DEFINITION FTY::RESERRP))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (9 1 (:DEFINITION ALISTP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (3 3 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (3 1 (:DEFINITION STRIP-CARS))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 )
(YUL::MODE-SET-RESULT-ERR-OF-FIELDS
 (42 2 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (38 2 (:DEFINITION FTY::RESERRP))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (13 13 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 (10 4 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (8 2 (:DEFINITION ALISTP))
 (3 1 (:REWRITE YUL::MODE-SET-RESULT-FIX-WHEN-MODE-SET-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (2 2 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULTP))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(YUL::MODE-SET-RESULT-FIX-WHEN-ERR
 (22 2 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (19 1 (:DEFINITION FTY::RESERRP))
 (13 13 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 1 (:DEFINITION ALISTP))
 (3 1 (:REWRITE YUL::MODE-SET-RESULT-FIX-WHEN-MODE-SET-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULTP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (1 1 (:DEFINITION STRIP-CARS))
 )
(YUL::EQUAL-OF-MODE-SET-RESULT-ERR
 (98 6 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (80 6 (:DEFINITION FTY::RESERRP))
 (29 23 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (18 18 (:REWRITE DEFAULT-CDR))
 (16 6 (:DEFINITION ALISTP))
 (13 13 (:REWRITE DEFAULT-CAR))
 (12 6 (:DEFINITION STRIP-CARS))
 (10 2 (:REWRITE FTY::RESERRP-WHEN-RESERR-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (4 4 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (4 4 (:TYPE-PRESCRIPTION FTY::RESERR-OPTIONP))
 (4 2 (:REWRITE FTY::RESERR-OPTIONP-WHEN-RESERRP))
 )
(YUL::MODE-SET-RESULT-ERR-OF-RESERR-FIX-GET)
(YUL::MODE-SET-RESULT-ERR-RESERR-EQUIV-CONGRUENCE-ON-GET)
(YUL::MODE-SET-RESULT-FIX-REDEF
 (22 11 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK))
 (15 15 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-FIX$INLINE))
 (12 12 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULT-OK->GET$INLINE))
 (9 3 (:REWRITE YUL::MODE-SET-RESULT-FIX-WHEN-MODE-SET-RESULTP))
 (6 6 (:TYPE-PRESCRIPTION YUL::MODE-SET-RESULTP))
 )
(YUL::MODE-SET-RESULTP-WHEN-MODE-SETP)
(YUL::MODE-SET-RESULTP-WHEN-RESERRP)
(YUL::NOT-RESERRP-WHEN-MODE-SETP
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(YUL::MODE-SETP-WHEN-MODE-SET-RESULTP-AND-NOT-RESERRP)
