(OBAG::BAGP)
(OBAG::BOOLEANP-OF-BAGP)
(OBAG::BAGP-WHEN-SETP
 (54 54 (:REWRITE DEFAULT-CDR))
 (53 45 (:REWRITE <<-TRANSITIVE))
 (38 38 (:REWRITE DEFAULT-CAR))
 (33 11 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (22 22 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (11 11 (:REWRITE SET::IN-SET))
 )
(OBAG::BFIX
 (1 1 (:TYPE-PRESCRIPTION OBAG::BFIX))
 )
(OBAG::BAGP-OF-BFIX
 (17 2 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (6 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (3 3 (:TYPE-PRESCRIPTION OBAG::BFIX))
 (2 2 (:REWRITE SET::IN-SET))
 )
(OBAG::BFIX-WHEN-BAGP
 (19 19 (:TYPE-PRESCRIPTION OBAG::BFIX))
 (14 2 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (6 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 )
(OBAG::EMPTY
 (6 6 (:TYPE-PRESCRIPTION OBAG::BFIX))
 )
(OBAG::BOOLEANP-OF-EMPTY)
(OBAG::BAGP-WHEN-NOT-EMPTY
 (11 11 (:TYPE-PRESCRIPTION OBAG::BFIX))
 (7 1 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (3 1 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 2 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (1 1 (:REWRITE SET::IN-SET))
 (1 1 (:REWRITE OBAG::BFIX-WHEN-BAGP))
 )
(OBAG::BFIX-WHEN-EMPTY
 (4 4 (:TYPE-PRESCRIPTION OBAG::BFIX))
 )
(OBAG::HEAD
 (25 1 (:REWRITE FAST-<<-IS-<<))
 (22 4 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (20 8 (:REWRITE OBAG::BFIX-WHEN-EMPTY))
 (20 4 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTY))
 (19 5 (:REWRITE <<-TRICHOTOMY))
 (17 3 (:REWRITE <<-ASYMMETRIC))
 (12 12 (:TYPE-PRESCRIPTION <<))
 (9 3 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (6 6 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 6 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE <<-TRANSITIVE))
 (3 3 (:REWRITE SET::IN-SET))
 )
(OBAG::HEAD-WHEN-EMPTY
 (1 1 (:TYPE-PRESCRIPTION OBAG::BFIX))
 )
(OBAG::HEAD-COUNT
 (229 112 (:REWRITE DEFAULT-+-2))
 (176 26 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTY))
 (164 43 (:REWRITE <<-TRICHOTOMY))
 (163 25 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (155 112 (:REWRITE DEFAULT-+-1))
 (142 25 (:REWRITE <<-ASYMMETRIC))
 (96 24 (:DEFINITION INTEGER-ABS))
 (96 12 (:DEFINITION LENGTH))
 (77 77 (:REWRITE DEFAULT-CDR))
 (69 23 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (60 12 (:DEFINITION LEN))
 (56 25 (:REWRITE OBAG::BFIX-WHEN-EMPTY))
 (54 54 (:REWRITE DEFAULT-CAR))
 (46 46 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (46 46 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (43 43 (:REWRITE <<-TRANSITIVE))
 (38 30 (:REWRITE DEFAULT-<-2))
 (36 30 (:REWRITE DEFAULT-<-1))
 (30 30 (:REWRITE FOLD-CONSTS-IN-+))
 (24 24 (:REWRITE DEFAULT-UNARY-MINUS))
 (23 23 (:REWRITE SET::IN-SET))
 (12 12 (:TYPE-PRESCRIPTION LEN))
 (12 12 (:REWRITE DEFAULT-REALPART))
 (12 12 (:REWRITE DEFAULT-NUMERATOR))
 (12 12 (:REWRITE DEFAULT-IMAGPART))
 (12 12 (:REWRITE DEFAULT-DENOMINATOR))
 (12 12 (:REWRITE DEFAULT-COERCE-2))
 (12 12 (:REWRITE DEFAULT-COERCE-1))
 (11 11 (:TYPE-PRESCRIPTION OBAG::BFIX))
 )
(OBAG::HEAD-COUNT-BUILT-IN
 (229 112 (:REWRITE DEFAULT-+-2))
 (176 26 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTY))
 (164 43 (:REWRITE <<-TRICHOTOMY))
 (163 25 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (155 112 (:REWRITE DEFAULT-+-1))
 (142 25 (:REWRITE <<-ASYMMETRIC))
 (96 24 (:DEFINITION INTEGER-ABS))
 (96 12 (:DEFINITION LENGTH))
 (77 77 (:REWRITE DEFAULT-CDR))
 (69 23 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (60 12 (:DEFINITION LEN))
 (56 25 (:REWRITE OBAG::BFIX-WHEN-EMPTY))
 (54 54 (:REWRITE DEFAULT-CAR))
 (46 46 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (46 46 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (43 43 (:REWRITE <<-TRANSITIVE))
 (38 30 (:REWRITE DEFAULT-<-2))
 (36 30 (:REWRITE DEFAULT-<-1))
 (30 30 (:REWRITE FOLD-CONSTS-IN-+))
 (24 24 (:REWRITE DEFAULT-UNARY-MINUS))
 (23 23 (:REWRITE SET::IN-SET))
 (12 12 (:TYPE-PRESCRIPTION LEN))
 (12 12 (:REWRITE DEFAULT-REALPART))
 (12 12 (:REWRITE DEFAULT-NUMERATOR))
 (12 12 (:REWRITE DEFAULT-IMAGPART))
 (12 12 (:REWRITE DEFAULT-DENOMINATOR))
 (12 12 (:REWRITE DEFAULT-COERCE-2))
 (12 12 (:REWRITE DEFAULT-COERCE-1))
 (11 11 (:TYPE-PRESCRIPTION OBAG::BFIX))
 )
(OBAG::TAIL
 (105 15 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (87 18 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTY))
 (60 23 (:REWRITE OBAG::BFIX-WHEN-EMPTY))
 (45 15 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (41 41 (:REWRITE DEFAULT-CDR))
 (30 30 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (30 30 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (22 22 (:REWRITE DEFAULT-CAR))
 (20 20 (:REWRITE <<-TRANSITIVE))
 (15 15 (:REWRITE SET::IN-SET))
 )
(OBAG::BAGP-OF-TAIL
 (85 12 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (69 18 (:REWRITE <<-TRICHOTOMY))
 (65 1 (:REWRITE OBAG::BFIX-WHEN-BAGP))
 (57 10 (:REWRITE <<-ASYMMETRIC))
 (34 12 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTY))
 (33 11 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (29 26 (:REWRITE DEFAULT-CDR))
 (24 24 (:TYPE-PRESCRIPTION OBAG::EMPTY))
 (22 22 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (22 22 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (18 18 (:REWRITE <<-TRANSITIVE))
 (16 16 (:REWRITE DEFAULT-CAR))
 (11 11 (:REWRITE SET::IN-SET))
 (3 1 (:REWRITE OBAG::BFIX-WHEN-EMPTY))
 )
(OBAG::TAIL-WHEN-EMPTY
 (1 1 (:TYPE-PRESCRIPTION OBAG::BFIX))
 )
(OBAG::TAIL-COUNT
 (183 48 (:REWRITE <<-TRICHOTOMY))
 (171 25 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTY))
 (162 77 (:REWRITE DEFAULT-+-2))
 (162 24 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (159 28 (:REWRITE <<-ASYMMETRIC))
 (108 77 (:REWRITE DEFAULT-+-1))
 (94 94 (:REWRITE DEFAULT-CDR))
 (69 23 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (61 61 (:REWRITE DEFAULT-CAR))
 (54 24 (:REWRITE OBAG::BFIX-WHEN-EMPTY))
 (48 48 (:REWRITE <<-TRANSITIVE))
 (46 46 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (46 46 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (40 10 (:DEFINITION INTEGER-ABS))
 (40 5 (:DEFINITION LENGTH))
 (25 5 (:DEFINITION LEN))
 (24 16 (:REWRITE DEFAULT-<-2))
 (23 23 (:REWRITE SET::IN-SET))
 (22 22 (:REWRITE FOLD-CONSTS-IN-+))
 (21 16 (:REWRITE DEFAULT-<-1))
 (11 11 (:TYPE-PRESCRIPTION OBAG::BFIX))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:TYPE-PRESCRIPTION LEN))
 (5 5 (:REWRITE DEFAULT-REALPART))
 (5 5 (:REWRITE DEFAULT-NUMERATOR))
 (5 5 (:REWRITE DEFAULT-IMAGPART))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 )
(OBAG::TAIL-COUNT-BUILT-IN
 (183 48 (:REWRITE <<-TRICHOTOMY))
 (171 25 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTY))
 (162 77 (:REWRITE DEFAULT-+-2))
 (162 24 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (159 28 (:REWRITE <<-ASYMMETRIC))
 (108 77 (:REWRITE DEFAULT-+-1))
 (94 94 (:REWRITE DEFAULT-CDR))
 (69 23 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (61 61 (:REWRITE DEFAULT-CAR))
 (54 24 (:REWRITE OBAG::BFIX-WHEN-EMPTY))
 (48 48 (:REWRITE <<-TRANSITIVE))
 (46 46 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (46 46 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (40 10 (:DEFINITION INTEGER-ABS))
 (40 5 (:DEFINITION LENGTH))
 (25 5 (:DEFINITION LEN))
 (24 16 (:REWRITE DEFAULT-<-2))
 (23 23 (:REWRITE SET::IN-SET))
 (22 22 (:REWRITE FOLD-CONSTS-IN-+))
 (21 16 (:REWRITE DEFAULT-<-1))
 (11 11 (:TYPE-PRESCRIPTION OBAG::BFIX))
 (10 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:TYPE-PRESCRIPTION LEN))
 (5 5 (:REWRITE DEFAULT-REALPART))
 (5 5 (:REWRITE DEFAULT-NUMERATOR))
 (5 5 (:REWRITE DEFAULT-IMAGPART))
 (5 5 (:REWRITE DEFAULT-DENOMINATOR))
 (5 5 (:REWRITE DEFAULT-COERCE-2))
 (5 5 (:REWRITE DEFAULT-COERCE-1))
 )
(OBAG::INSERT
 (20 20 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 (1 1 (:TYPE-PRESCRIPTION OBAG::TAIL-WHEN-EMPTY))
 )
(OBAG::BAGP-OF-INSERT
 (3627 494 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (2079 1142 (:REWRITE OBAG::BFIX-WHEN-EMPTY))
 (1455 485 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (1266 1080 (:REWRITE DEFAULT-CDR))
 (1027 929 (:REWRITE DEFAULT-CAR))
 (970 970 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (970 970 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (872 731 (:REWRITE <<-TRANSITIVE))
 (671 237 (:REWRITE OBAG::HEAD-WHEN-EMPTY))
 (485 485 (:REWRITE SET::IN-SET))
 (401 70 (:REWRITE OBAG::TAIL-WHEN-EMPTY))
 (51 51 (:TYPE-PRESCRIPTION OBAG::BFIX))
 (11 11 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 )
(OBAG::DELETE
 (19 19 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 (6 6 (:TYPE-PRESCRIPTION OBAG::TAIL-WHEN-EMPTY))
 )
(OBAG::BAGP-OF-DELETE
 (4397 635 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (2866 1608 (:REWRITE OBAG::BFIX-WHEN-EMPTY))
 (1881 627 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (1514 1514 (:REWRITE DEFAULT-CDR))
 (1254 1254 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (1254 1254 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (1113 1113 (:REWRITE DEFAULT-CAR))
 (1003 173 (:REWRITE OBAG::TAIL-WHEN-EMPTY))
 (862 238 (:REWRITE OBAG::HEAD-WHEN-EMPTY))
 (627 627 (:REWRITE SET::IN-SET))
 (37 37 (:TYPE-PRESCRIPTION OBAG::BFIX))
 (8 8 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 (2 2 (:REWRITE <<-IRREFLEXIVE))
 )
(OBAG::IN
 (20 20 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 (3 3 (:TYPE-PRESCRIPTION OBAG::TAIL-WHEN-EMPTY))
 )
(OBAG::BOOLEANP-OF-IN
 (2 2 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 )
(OBAG::OCCS
 (21 21 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 (6 6 (:TYPE-PRESCRIPTION OBAG::TAIL-WHEN-EMPTY))
 )
(OBAG::NATP-OF-OCCS
 (2 2 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 )
(OBAG::CARDINALITY
 (1 1 (:TYPE-PRESCRIPTION OBAG::TAIL-WHEN-EMPTY))
 )
(OBAG::NATP-OF-CARDINALITY)
(OBAG::SUBBAG
 (3 3 (:TYPE-PRESCRIPTION OBAG::TAIL-WHEN-EMPTY))
 (2 2 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 )
(OBAG::BOOLEANP-OF-SUBBAG)
(OBAG::UNION
 (3 3 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 (1 1 (:TYPE-PRESCRIPTION OBAG::TAIL-WHEN-EMPTY))
 )
(OBAG::BAGP-OF-UNION
 (77 8 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (33 33 (:TYPE-PRESCRIPTION OBAG::UNION))
 (27 9 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTY))
 (24 8 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (16 16 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (16 16 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (13 1 (:REWRITE OBAG::BFIX-WHEN-BAGP))
 (8 8 (:REWRITE SET::IN-SET))
 (3 1 (:REWRITE OBAG::BFIX-WHEN-EMPTY))
 (1 1 (:REWRITE OBAG::TAIL-WHEN-EMPTY))
 (1 1 (:REWRITE OBAG::HEAD-WHEN-EMPTY))
 )
(OBAG::UNION)
(OBAG::INTERSECT
 (4 4 (:TYPE-PRESCRIPTION OBAG::TAIL-WHEN-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 )
(OBAG::BAGP-OF-INTERSECT
 (130 13 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (39 13 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (39 13 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTY))
 (26 26 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (26 26 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (13 13 (:REWRITE SET::IN-SET))
 (9 9 (:REWRITE OBAG::HEAD-WHEN-EMPTY))
 (2 2 (:REWRITE OBAG::TAIL-WHEN-EMPTY))
 )
(OBAG::INTERSECT)
(OBAG::DIFFERENCE
 (4 4 (:TYPE-PRESCRIPTION OBAG::TAIL-WHEN-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION OBAG::HEAD-WHEN-EMPTY))
 )
(OBAG::BAGP-OF-DIFFERENCE
 (130 13 (:REWRITE OBAG::BAGP-WHEN-SETP))
 (39 13 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (39 13 (:REWRITE OBAG::BAGP-WHEN-NOT-EMPTY))
 (26 26 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (26 26 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (13 13 (:REWRITE SET::IN-SET))
 (9 9 (:REWRITE OBAG::HEAD-WHEN-EMPTY))
 (2 2 (:REWRITE OBAG::TAIL-WHEN-EMPTY))
 )
(OBAG::DIFFERENCE)
