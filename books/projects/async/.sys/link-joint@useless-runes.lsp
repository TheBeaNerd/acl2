(ADE::FULLP)
(ADE::EMPTYP)
(ADE::VALIDP)
(ADE::4V->LINK-ST)
(ADE::MAP-TO-LINKS1
 (24 8 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (16 16 (:TYPE-PRESCRIPTION ADE::BVP))
 (16 16 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 )
(ADE::MAP-TO-LINKS
 (24 8 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (16 16 (:TYPE-PRESCRIPTION ADE::BVP))
 (16 16 (:REWRITE DEFAULT-CDR))
 (8 8 (:REWRITE DEFAULT-CAR))
 )
(ADE::REMOVE-DUP-NEIGHBORS)
(ADE::PRETTY-LIST)
(ADE::SIGNAL-VALS-GEN
 (54 18 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (46 38 (:REWRITE DEFAULT-<-1))
 (40 38 (:REWRITE DEFAULT-<-2))
 (23 9 (:REWRITE DEFAULT-*-2))
 (21 7 (:REWRITE COMMUTATIVITY-OF-+))
 (15 15 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE ZP-OPEN))
 (9 9 (:REWRITE DEFAULT-*-1))
 (7 7 (:REWRITE ZIP-OPEN))
 )
(ADE::N-RTZ-FULLP)
(ADE::N-RTZ-EMPTYP)
(ADE::N-RTZ-FULLP-OF-B-NOT)
(ADE::N-RTZ-EMPTYP-OF-B-NOT)
(ADE::DRAIN-N-RTZ-FULL)
(ADE::FILL-N-RTZ-EMPTY)
(ADE::RTZ-FULLP)
(ADE::RTZ-EMPTYP)
(ADE::JOINT-CNTL&)
(ADE::CHECK-JOINT-CNTL)
(ADE::JOINT-ACT)
(ADE::BOOLEANP-JOINT-ACT)
(ADE::JOINT-ACT-REWRITE
 (3 3 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(ADE::JOINT-ACT-REMOVES-F-BUF
 (20 8 (:TYPE-PRESCRIPTION ADE::BOOLEANP-JOINT-ACT))
 (8 8 (:TYPE-PRESCRIPTION BOOLEANP))
 )
(ADE::JOINT-CNTL$VALUE
 (67 67 (:REWRITE DEFAULT-CAR))
 (61 61 (:REWRITE DEFAULT-CDR))
 (46 19 (:REWRITE ADE::F-GATES=B-GATES))
 (25 5 (:DEFINITION ADE::DELETE-TO-EQ))
 (18 18 (:TYPE-PRESCRIPTION BOOLEANP))
 (9 9 (:TYPE-PRESCRIPTION ADE::F-AND))
 )
(ADE::CLICK-LINK&)
(ADE::CHECK-CLICK-LINK)
(ADE::CLICK-LINK$VALUE
 (266 266 (:REWRITE DEFAULT-CAR))
 (98 98 (:REWRITE DEFAULT-CDR))
 (38 10 (:REWRITE ADE::F-GATES=B-GATES))
 (30 6 (:DEFINITION ADE::DELETE-TO-EQ))
 (20 20 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 2 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (6 2 (:REWRITE ADE::F-BUF-OF-3VP))
 )
(ADE::CLICK-LINK$STATE
 (931 931 (:REWRITE DEFAULT-CAR))
 (323 323 (:REWRITE DEFAULT-CDR))
 (264 28 (:REWRITE ADE::UPDATE-ALIST-OF-NOT-A-KEY))
 (160 21 (:DEFINITION ALISTP))
 (85 17 (:DEFINITION ADE::DELETE-TO-EQ))
 (50 14 (:REWRITE ADE::F-GATES=B-GATES))
 (36 36 (:TYPE-PRESCRIPTION ADE::UPDATE-ALIST))
 (28 28 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 2 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (6 2 (:REWRITE ADE::F-BUF-OF-3VP))
 )
(ADE::LINK1*)
(ADE::LINK1*$DESTRUCTURE)
(ADE::NOT-PRIMP-LINK1)
(ADE::LINK1$NETLIST)
(ADE::LINK1&)
(ADE::CHECK-LINK1$NETLIST)
(ADE::LINK1$VALID-ST)
(ADE::LINK1$VALUE
 (10 4 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (10 4 (:REWRITE ADE::F-BUF-OF-3VP))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:TYPE-PRESCRIPTION ADE::3VP))
 (3 3 (:REWRITE NTH-WHEN-PREFIXP))
 )
(ADE::LINK1$STEP
 (1 1 (:TYPE-PRESCRIPTION ADE::F-SR))
 (1 1 (:TYPE-PRESCRIPTION ADE::F-IF))
 )
(ADE::LINK1$STATE
 (47 5 (:REWRITE ADE::UPDATE-ALIST-OF-NOT-A-KEY))
 (28 6 (:DEFINITION ALISTP))
 (11 5 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (11 5 (:REWRITE ADE::F-BUF-OF-3VP))
 (9 9 (:REWRITE NTH-WHEN-PREFIXP))
 (8 8 (:TYPE-PRESCRIPTION ADE::UPDATE-ALIST))
 (6 6 (:TYPE-PRESCRIPTION BOOLEANP))
 (6 6 (:TYPE-PRESCRIPTION ADE::3VP))
 (4 2 (:REWRITE ADE::ASSOC-EQ-VALUES-UPDATE-ALIST-NOT-MEMBER))
 (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 )
(ADE::LINK$INS-LEN
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(ADE::LINK*
 (16 8 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (8 8 (:TYPE-PRESCRIPTION POSP))
 )
(ADE::LINK*$DESTRUCTURE
 (60 30 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (30 30 (:TYPE-PRESCRIPTION POSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 )
(ADE::NOT-PRIMP-LINK)
(ADE::EXTRACT-VALID-DATA)
(ADE::LINK$NETLIST)
(ADE::LINK&)
(ADE::CHECK-LINK$NETLIST-64)
(ADE::LINK$ST-FORMAT)
(ADE::LINK$ST-FORMAT=>CONSTRAINT)
(ADE::LINK$VALID-ST)
(ADE::LINK$VALID-ST=>CONSTRAINT
 (5 1 (:DEFINITION LEN))
 (3 3 (:REWRITE NTH-WHEN-PREFIXP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(ADE::LINK$VALUE
 (92 1 (:REWRITE ADE::ASSOC-EQ-VALUES-APPEND-PAIRLIS$-WHEN-DISJOINT))
 (84 40 (:TYPE-PRESCRIPTION ADE::CONSP-SIS))
 (62 39 (:REWRITE DEFAULT-+-2))
 (42 4 (:REWRITE ADE::DISJOINT-ATOM))
 (40 40 (:TYPE-PRESCRIPTION POSP))
 (39 39 (:REWRITE DEFAULT-+-1))
 (30 4 (:REWRITE ADE::DISJOINT-COMMUTATIVE))
 (26 1 (:REWRITE TAKE-WHEN-PREFIXP))
 (24 8 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (24 1 (:REWRITE ADE::ASSOC-EQ-VALUES-ARGS-PAIRLIS$-ARGS))
 (22 4 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 (22 4 (:DEFINITION TRUE-LISTP))
 (20 2 (:DEFINITION ATOM))
 (16 16 (:TYPE-PRESCRIPTION ADE::BVP))
 (16 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-2))
 (16 4 (:REWRITE ADE::DISJOINT-SIS-SAME-SYM-1))
 (14 2 (:REWRITE PREFIXP-WHEN-PREFIXP))
 (14 2 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (12 3 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (10 10 (:TYPE-PRESCRIPTION PAIRLIS$))
 (10 10 (:TYPE-PRESCRIPTION BOOLEANP))
 (10 10 (:LINEAR LEN-WHEN-PREFIXP))
 (10 5 (:REWRITE ADE::LEN-SIS))
 (10 4 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (10 4 (:REWRITE ADE::F-BUF-OF-3VP))
 (9 9 (:TYPE-PRESCRIPTION ADE::DISJOINT))
 (8 2 (:DEFINITION BINARY-APPEND))
 (7 3 (:REWRITE ADE::FV-IF-WHEN-BVP))
 (6 6 (:TYPE-PRESCRIPTION ADE::3VP))
 (6 5 (:REWRITE DEFAULT-<-1))
 (5 5 (:TYPE-PRESCRIPTION PREFIXP))
 (5 5 (:REWRITE NTH-WHEN-PREFIXP))
 (5 5 (:REWRITE ADE::NFIX-OF-NAT))
 (5 5 (:REWRITE DEFAULT-<-2))
 (5 5 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (5 2 (:REWRITE TAKE-WHEN-ATOM))
 (5 2 (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
 (5 2 (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
 (4 4 (:REWRITE ADE::DISJOINT-SIS-DIFF-SYMS))
 (3 3 (:TYPE-PRESCRIPTION ADE::F-BUF))
 (3 3 (:REWRITE DEFAULT-SYMBOL-NAME))
 (3 3 (:DEFINITION STRIP-CARS))
 (2 2 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (2 2 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (2 2 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (2 2 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (2 2 (:REWRITE ADE::NTHCDR-OF-POS-CONST-IDX))
 (1 1 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (1 1 (:REWRITE ADE::NO-DUPLICATESP-SIS))
 )
(ADE::LINK$STEP
 (6 3 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (3 3 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1 1 (:TYPE-PRESCRIPTION ADE::F-SR))
 )
(ADE::LINK$STATE
 (264 132 (:REWRITE DEFAULT-+-2))
 (166 4 (:REWRITE ADE::LATCH-N$VALUE))
 (132 132 (:REWRITE DEFAULT-+-1))
 (126 13 (:REWRITE ADE::ASSOC-EQ-VALUES-ARGS-PAIRLIS$-ARGS))
 (80 4 (:REWRITE LEN-WHEN-PREFIXP))
 (75 19 (:REWRITE ADE::ASSOC-EQ-VALUES-ATOM))
 (72 72 (:LINEAR LEN-WHEN-PREFIXP))
 (67 13 (:REWRITE PREFIXP-WHEN-PREFIXP))
 (56 20 (:REWRITE ADE::BV-IS-TRUE-LIST))
 (51 4 (:REWRITE TAKE-WHEN-PREFIXP))
 (47 5 (:REWRITE ADE::UPDATE-ALIST-OF-NOT-A-KEY))
 (36 36 (:TYPE-PRESCRIPTION ADE::BVP))
 (36 36 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (32 32 (:TYPE-PRESCRIPTION PREFIXP))
 (28 6 (:DEFINITION ALISTP))
 (21 2 (:REWRITE ADE::ALL-UNBOUND-IN-BODY-ATOM-NAMES))
 (16 16 (:REWRITE NTH-WHEN-PREFIXP))
 (16 4 (:REWRITE ADE::NOT-EQUAL-WITH-SI-OF-DIFF-SYMBOL . 2))
 (16 4 (:DEFINITION BINARY-APPEND))
 (13 13 (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
 (13 13 (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
 (13 13 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (13 13 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (13 13 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (13 13 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (12 12 (:TYPE-PRESCRIPTION BOOLEANP))
 (11 5 (:REWRITE ADE::FV-IF-WHEN-BVP))
 (11 5 (:REWRITE ADE::F-BUF-OF-NOT-BOOLEANP))
 (11 5 (:REWRITE ADE::F-BUF-OF-3VP))
 (10 10 (:TYPE-PRESCRIPTION ADE::FV-IF))
 (8 8 (:TYPE-PRESCRIPTION ADE::UPDATE-ALIST))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 (6 6 (:TYPE-PRESCRIPTION ADE::3VP))
 (5 5 (:DEFINITION STRIP-CARS))
 (4 4 (:TYPE-PRESCRIPTION NO-DUPLICATESP-EQUAL))
 (4 4 (:TYPE-PRESCRIPTION ADE::F-BUF))
 (4 4 (:REWRITE TAKE-WHEN-ATOM))
 (4 4 (:REWRITE ADE::NO-DUPLICATESP-SIS))
 (4 4 (:REWRITE DEFAULT-SYMBOL-NAME))
 (4 2 (:REWRITE ADE::ASSOC-EQ-VALUES-DE-OCC-UPDATE-ALIST))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 )
(ADE::LINK$VALID-ST-PRESERVED
 (1056 168 (:DEFINITION LEN))
 (996 18 (:DEFINITION TAKE))
 (970 30 (:REWRITE LEN-WHEN-PREFIXP))
 (822 411 (:TYPE-PRESCRIPTION TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION))
 (670 40 (:REWRITE PREFIXP-WHEN-EQUAL-LENGTHS))
 (600 40 (:REWRITE PREFIXP-WHEN-PREFIXP))
 (411 411 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (358 190 (:REWRITE DEFAULT-+-2))
 (348 174 (:TYPE-PRESCRIPTION ADE::BVP-NTHCDR))
 (303 168 (:REWRITE DEFAULT-CAR))
 (276 36 (:REWRITE ADE::LEN-NTHCDR))
 (240 36 (:REWRITE TAKE-WHEN-ATOM))
 (214 214 (:REWRITE NTH-WHEN-PREFIXP))
 (212 12 (:REWRITE TAKE-WHEN-PREFIXP))
 (202 128 (:REWRITE DEFAULT-<-2))
 (190 190 (:REWRITE DEFAULT-+-1))
 (186 128 (:REWRITE DEFAULT-<-1))
 (176 24 (:REWRITE ZP-OPEN))
 (166 166 (:LINEAR LEN-WHEN-PREFIXP))
 (165 15 (:DEFINITION PAIRLIS$))
 (140 35 (:DEFINITION STRIP-CARS))
 (110 110 (:TYPE-PRESCRIPTION PREFIXP))
 (100 40 (:REWRITE PREFIXP-WHEN-NOT-CONSP-RIGHT))
 (100 40 (:REWRITE PREFIXP-WHEN-NOT-CONSP-LEFT))
 (100 10 (:DEFINITION ADE::V-THREEFIX))
 (83 83 (:LINEAR ADE::A-HELPFUL-LEMMA-FOR-TREE-INDUCTIONS))
 (52 4 (:REWRITE REPEAT-WHEN-ZP))
 (42 14 (:REWRITE ADE::BVP-NTHCDR))
 (40 40 (:REWRITE PREFIXP-TRANSITIVE . 2))
 (40 40 (:REWRITE PREFIXP-TRANSITIVE . 1))
 (40 40 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 2))
 (40 40 (:REWRITE PREFIXP-ONE-WAY-OR-ANOTHER . 1))
 (36 4 (:REWRITE CONSP-OF-TAKE))
 (35 35 (:TYPE-PRESCRIPTION STRIP-CARS))
 (35 5 (:REWRITE ADE::CAR-V-THREEFIX))
 (24 8 (:DEFINITION NATP))
 (20 2 (:REWRITE CAR-OF-TAKE))
 (16 16 (:TYPE-PRESCRIPTION ADE::FV-IF))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 )
