(DEPGRAPH::MERGESORT-ALIST-VALUES)
(DEPGRAPH::MERGESORT-ALIST-VALUES-WHEN-ATOM)
(DEPGRAPH::MERGESORT-ALIST-VALUES-OF-CONS
 (49 7 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (22 22 (:REWRITE DEFAULT-CAR))
 (21 7 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (17 17 (:REWRITE DEFAULT-CDR))
 (16 4 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (15 15 (:REWRITE DEPGRAPH::MERGESORT-ALIST-VALUES-WHEN-ATOM))
 (14 14 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (14 14 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (7 7 (:REWRITE SET::IN-SET))
 (4 4 (:REWRITE ALISTP-WHEN-ATOM))
 )
(DEPGRAPH::ALISTP-OF-MERGESORT-ALIST-VALUES
 (28 10 (:REWRITE ALISTP-WHEN-ATOM))
 (21 3 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (16 4 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (15 15 (:REWRITE DEFAULT-CAR))
 (9 3 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 6 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (3 3 (:REWRITE SET::IN-SET))
 )
(DEPGRAPH::HONS-ASSOC-EQUAL-OF-MERGESORT-ALIST-VALUES
 (850 111 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (452 80 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (421 409 (:REWRITE DEFAULT-CAR))
 (327 109 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (315 305 (:REWRITE DEFAULT-CDR))
 (226 226 (:TYPE-PRESCRIPTION ALISTP))
 (218 218 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (218 218 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (171 171 (:TYPE-PRESCRIPTION DEPGRAPH::MERGESORT-ALIST-VALUES))
 (132 33 (:REWRITE ALISTP-OF-CDR))
 (113 113 (:REWRITE ALISTP-WHEN-ATOM))
 (109 109 (:REWRITE SET::IN-SET))
 (48 48 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 )
(DEPGRAPH::ALIST-KEYS-OF-MERGESORT-ALIST-VALUES
 (72 14 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (63 9 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (50 49 (:REWRITE DEFAULT-CAR))
 (39 39 (:REWRITE DEFAULT-CDR))
 (36 36 (:TYPE-PRESCRIPTION DEPGRAPH::MERGESORT-ALIST-VALUES))
 (36 36 (:TYPE-PRESCRIPTION ALISTP))
 (27 9 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (18 18 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (18 18 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (18 18 (:REWRITE ALISTP-WHEN-ATOM))
 (16 4 (:REWRITE ALISTP-OF-CDR))
 (9 9 (:REWRITE SET::IN-SET))
 )
(DEPGRAPH::L0
 (146 7 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (90 15 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (85 8 (:DEFINITION TRUE-LISTP))
 (70 10 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (64 10 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (60 25 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (50 50 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (42 42 (:REWRITE DEFAULT-CDR))
 (40 40 (:REWRITE DEFAULT-CAR))
 (35 35 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (33 33 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (32 32 (:TYPE-PRESCRIPTION ALISTP))
 (25 25 (:REWRITE SET::IN-SET))
 (24 6 (:REWRITE ALISTP-OF-CDR))
 (16 16 (:REWRITE ALISTP-WHEN-ATOM))
 (6 6 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 )
(DEPGRAPH::LIST-EQUIV-IMPLIES-EQUAL-MERGESORT-ALIST-VALUES-1
 (120 6 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (72 12 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (72 6 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
 (66 6 (:DEFINITION TRUE-LISTP))
 (36 16 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (32 32 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (30 12 (:REWRITE DEPGRAPH::MERGESORT-ALIST-VALUES-WHEN-ATOM))
 (30 6 (:DEFINITION LEN))
 (28 4 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (24 24 (:REWRITE DEFAULT-CDR))
 (20 20 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (16 16 (:REWRITE SET::IN-SET))
 (16 16 (:REWRITE DEFAULT-CAR))
 (16 4 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (12 6 (:REWRITE DEFAULT-+-2))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (6 6 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (6 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE ALISTP-WHEN-ATOM))
 )
(DEPGRAPH::L0
 (252 12 (:DEFINITION DEPGRAPH::MERGESORT-ALIST-VALUES))
 (205 30 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (92 92 (:REWRITE DEFAULT-CAR))
 (78 26 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (66 66 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 (66 66 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (66 66 (:REWRITE DEFAULT-CDR))
 (52 52 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (52 52 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (48 12 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (36 36 (:REWRITE DEPGRAPH::MERGESORT-ALIST-VALUES-WHEN-ATOM))
 (26 26 (:REWRITE SET::IN-SET))
 (24 24 (:TYPE-PRESCRIPTION ALISTP))
 (12 12 (:REWRITE ALISTP-WHEN-ATOM))
 )
(DEPGRAPH::L1
 (42 2 (:DEFINITION DEPGRAPH::MERGESORT-ALIST-VALUES))
 (14 2 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 2 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (6 6 (:REWRITE DEPGRAPH::MERGESORT-ALIST-VALUES-WHEN-ATOM))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE ALISTP-WHEN-ATOM))
 (2 2 (:REWRITE ALIST-KEYS-WHEN-ATOM))
 )
(DEPGRAPH::ALIST-EQUIV-IMPLIES-ALIST-EQUIV-MERGESORT-ALIST-VALUES-1
 (42 2 (:DEFINITION DEPGRAPH::MERGESORT-ALIST-VALUES))
 (14 2 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (8 8 (:REWRITE DEFAULT-CAR))
 (8 2 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (6 6 (:REWRITE DEPGRAPH::MERGESORT-ALIST-VALUES-WHEN-ATOM))
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE ALISTP-WHEN-ATOM))
 )
(DEPGRAPH::ALIST-VALUES-ARE-SETS-P)
(DEPGRAPH::ALIST-VALUES-ARE-SETS-P-WHEN-ATOM)
(DEPGRAPH::ALIST-VALUES-ARE-SETS-P-OF-CONS
 (18 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (14 14 (:REWRITE DEFAULT-CDR))
 (12 12 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (12 12 (:REWRITE DEPGRAPH::ALIST-VALUES-ARE-SETS-P-WHEN-ATOM))
 (12 3 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION ALISTP))
 (6 6 (:REWRITE SET::IN-SET))
 (3 3 (:REWRITE ALISTP-WHEN-ATOM))
 )
(DEPGRAPH::SETP-OF-LOOKUP-WHEN-ALIST-VALUES-ARE-SETS-P
 (182 60 (:REWRITE DEFAULT-CDR))
 (105 35 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (85 17 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
 (84 17 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (70 70 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (42 42 (:TYPE-PRESCRIPTION ALISTP))
 (39 39 (:REWRITE DEFAULT-CAR))
 (35 35 (:REWRITE SET::IN-SET))
 (21 21 (:REWRITE ALISTP-WHEN-ATOM))
 (16 4 (:REWRITE ALISTP-OF-CDR))
 )
(DEPGRAPH::ALIST-VALUES-ARE-SETS-P-OF-HONS-SHRINK-ALIST
 (162 27 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (85 81 (:REWRITE DEFAULT-CAR))
 (73 25 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (70 70 (:TYPE-PRESCRIPTION ALISTP))
 (70 66 (:REWRITE DEFAULT-CDR))
 (48 48 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (37 35 (:REWRITE ALISTP-WHEN-ATOM))
 (34 8 (:REWRITE ALISTP-OF-FAST-ALIST-FORK))
 (25 25 (:REWRITE SET::IN-SET))
 (9 9 (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
 (9 9 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
 (6 2 (:REWRITE ALISTP-OF-CONS))
 )
(DEPGRAPH::ALIST-VALUES-ARE-SETS-P-OF-MERGESORT-ALIST-VALUES
 (58 22 (:REWRITE DEFAULT-CDR))
 (44 17 (:REWRITE DEPGRAPH::ALIST-VALUES-ARE-SETS-P-WHEN-ATOM))
 (30 10 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (20 20 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (18 18 (:REWRITE DEFAULT-CAR))
 (14 2 (:REWRITE SET::MERGESORT-SET-IDENTITY))
 (10 10 (:REWRITE SET::IN-SET))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (1 1 (:REWRITE ALISTP-WHEN-ATOM))
 )
(DEPGRAPH::L0
 (146 7 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (90 15 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (85 8 (:DEFINITION TRUE-LISTP))
 (64 10 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (60 25 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (42 42 (:REWRITE DEFAULT-CDR))
 (35 35 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (33 33 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (32 32 (:TYPE-PRESCRIPTION ALISTP))
 (30 30 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (25 25 (:REWRITE SET::IN-SET))
 (24 6 (:REWRITE ALISTP-OF-CDR))
 (20 20 (:REWRITE DEFAULT-CAR))
 (16 16 (:REWRITE ALISTP-WHEN-ATOM))
 (6 6 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 )
(DEPGRAPH::LIST-EQUIV-IMPLIES-EQUAL-ALIST-VALUES-ARE-SETS-P-1
 (120 6 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (72 12 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (72 6 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
 (66 6 (:DEFINITION TRUE-LISTP))
 (36 16 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (30 30 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (30 12 (:REWRITE DEPGRAPH::ALIST-VALUES-ARE-SETS-P-WHEN-ATOM))
 (30 6 (:DEFINITION LEN))
 (24 24 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (24 24 (:REWRITE DEFAULT-CDR))
 (20 20 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (16 16 (:REWRITE SET::IN-SET))
 (16 4 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
 (12 6 (:REWRITE DEFAULT-+-2))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (8 8 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (6 6 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE ALISTP-WHEN-ATOM))
 )
