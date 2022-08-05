(ALISTP-OF-REVERSE-LIST
 (7137 564 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (2446 50 (:REWRITE CDR-OF-REVERSE-LIST))
 (1296 50 (:REWRITE CAR-OF-REVERSE-LIST))
 (1275 83 (:REWRITE CONSP-OF-REVERSE-LIST))
 (1177 1003 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1140 664 (:REWRITE DEFAULT-<-2))
 (988 194 (:REWRITE LEN-OF-CDR))
 (884 50 (:DEFINITION TAKE))
 (884 50 (:DEFINITION NTH))
 (784 100 (:REWRITE ZP-OPEN))
 (664 664 (:REWRITE USE-ALL-<-2))
 (664 664 (:REWRITE USE-ALL-<))
 (664 664 (:REWRITE DEFAULT-<-1))
 (654 552 (:REWRITE DEFAULT-+-2))
 (564 564 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (564 564 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (552 552 (:REWRITE DEFAULT-+-1))
 (508 154 (:REWRITE FOLD-CONSTS-IN-+))
 (484 242 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (393 391 (:REWRITE DEFAULT-CDR))
 (389 387 (:REWRITE DEFAULT-CAR))
 (346 83 (:REWRITE LEN-OF-REVERSE-LIST))
 (242 242 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 (200 200 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (136 68 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (95 95 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (68 68 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (6 6 (:REWRITE EQUAL-OF-LEN-AND-0))
 )
(STRIP-CARS-OF-REVERSE-LIST
 (2069 199 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (988 20 (:REWRITE CDR-OF-REVERSE-LIST))
 (528 20 (:REWRITE CAR-OF-REVERSE-LIST))
 (392 20 (:DEFINITION TAKE))
 (392 20 (:DEFINITION NTH))
 (385 329 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (352 40 (:REWRITE ZP-OPEN))
 (341 29 (:REWRITE CONSP-OF-REVERSE-LIST))
 (306 170 (:REWRITE DEFAULT-<-2))
 (228 169 (:REWRITE DEFAULT-+-2))
 (199 199 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (184 52 (:REWRITE FOLD-CONSTS-IN-+))
 (170 170 (:REWRITE USE-ALL-<-2))
 (170 170 (:REWRITE USE-ALL-<))
 (170 170 (:REWRITE DEFAULT-<-1))
 (170 34 (:REWRITE LEN-OF-CDR))
 (169 169 (:REWRITE DEFAULT-+-1))
 (152 152 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (143 143 (:REWRITE DEFAULT-CDR))
 (80 80 (:TYPE-PRESCRIPTION TRUE-LISTP-TAKE))
 (64 20 (:REWRITE LEN-OF-REVERSE-LIST))
 (21 21 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(RAW-COUNTEREXAMPLEP)
(ALISTP-WHEN-RAW-COUNTEREXAMPLEP
 (315 27 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (99 99 (:REWRITE DEFAULT-CAR))
 (54 27 (:REWRITE DEFAULT-<-2))
 (49 49 (:REWRITE DEFAULT-CDR))
 (36 36 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (34 17 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (27 27 (:REWRITE USE-ALL-<-2))
 (27 27 (:REWRITE USE-ALL-<))
 (27 27 (:REWRITE DEFAULT-<-1))
 (27 27 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (27 27 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (17 17 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (16 8 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (8 8 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 )
(RAW-COUNTEREXAMPLEP-OF-APPEND
 (1443 131 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (385 169 (:REWRITE DEFAULT-CDR))
 (205 151 (:REWRITE DEFAULT-CAR))
 (194 194 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (178 101 (:REWRITE DEFAULT-<-2))
 (131 131 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (120 24 (:REWRITE LEN-OF-CDR))
 (101 101 (:REWRITE USE-ALL-<-2))
 (101 101 (:REWRITE USE-ALL-<))
 (101 101 (:REWRITE DEFAULT-<-1))
 (101 101 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (74 37 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (37 37 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (32 16 (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
 (24 24 (:REWRITE DEFAULT-+-2))
 (24 24 (:REWRITE DEFAULT-+-1))
 (24 24 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (16 16 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (16 16 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(RAW-COUNTEREXAMPLEP-OF-REV
 (2712 120 (:REWRITE CDR-OF-REVERSE-LIST))
 (2185 187 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (1872 120 (:DEFINITION TAKE))
 (1020 150 (:REWRITE ZP-OPEN))
 (678 30 (:REWRITE CAR-OF-REVERSE-LIST))
 (670 606 (:REWRITE DEFAULT-+-2))
 (660 210 (:REWRITE FOLD-CONSTS-IN-+))
 (606 606 (:REWRITE DEFAULT-+-1))
 (506 333 (:REWRITE DEFAULT-<-2))
 (468 30 (:DEFINITION NTH))
 (460 92 (:REWRITE LEN-OF-CDR))
 (401 401 (:REWRITE DEFAULT-CAR))
 (371 371 (:REWRITE DEFAULT-CDR))
 (333 333 (:REWRITE USE-ALL-<-2))
 (333 333 (:REWRITE USE-ALL-<))
 (333 333 (:REWRITE DEFAULT-<-1))
 (278 18 (:REWRITE CONSP-OF-REVERSE-LIST))
 (187 187 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (175 175 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (162 81 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (108 30 (:REWRITE LEN-OF-REVERSE-LIST))
 (82 82 (:TYPE-PRESCRIPTION REVERSE-LIST))
 (81 81 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (20 20 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (8 4 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 )
(NATP-OF-LOOKUP-EQUAL-WHEN-RAW-COUNTEREXAMPLEP
 (6518 554 (:REWRITE DEFAULT-CDR))
 (5029 409 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (4324 88 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (3932 136 (:DEFINITION ALISTP))
 (554 329 (:REWRITE DEFAULT-<-2))
 (544 272 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (449 449 (:REWRITE DEFAULT-CAR))
 (440 88 (:REWRITE LEN-OF-CDR))
 (409 409 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (354 177 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (329 329 (:REWRITE USE-ALL-<-2))
 (329 329 (:REWRITE USE-ALL-<))
 (329 329 (:REWRITE DEFAULT-<-1))
 (313 313 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (272 272 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 (177 177 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (104 96 (:REWRITE DEFAULT-+-2))
 (96 96 (:REWRITE DEFAULT-+-1))
 (96 96 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (88 88 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(MATCH-CHARS
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(MATCH-CHARS-LEN-BOUND
 (184 16 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (49 25 (:REWRITE DEFAULT-<-2))
 (29 25 (:REWRITE DEFAULT-<-1))
 (25 25 (:REWRITE USE-ALL-<-2))
 (25 25 (:REWRITE USE-ALL-<))
 (16 16 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (16 16 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (14 14 (:REWRITE DEFAULT-CAR))
 (10 1 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (8 1 (:LINEAR LEN-OF-CDR-LINEAR))
 (7 7 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-+-1))
 )
(LEN-OF-MV-NTH-1-OF-MATCH-CHARS
 (348 34 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (56 46 (:REWRITE DEFAULT-CAR))
 (56 28 (:REWRITE DEFAULT-<-2))
 (34 34 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (32 22 (:REWRITE DEFAULT-CDR))
 (30 27 (:REWRITE DEFAULT-+-2))
 (30 27 (:REWRITE DEFAULT-+-1))
 (28 28 (:REWRITE USE-ALL-<-2))
 (28 28 (:REWRITE USE-ALL-<))
 (28 28 (:REWRITE DEFAULT-<-1))
 (28 28 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (20 2 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (16 2 (:LINEAR LEN-OF-CDR-LINEAR))
 (9 7 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(CHARACTER-LISTP-OF-MV-NTH-1-OF-MATCH-CHARS
 (544 47 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (89 10 (:REWRITE LEN-OF-MV-NTH-1-OF-MATCH-CHARS))
 (83 83 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (68 52 (:REWRITE DEFAULT-CAR))
 (64 37 (:REWRITE DEFAULT-<-2))
 (54 38 (:REWRITE DEFAULT-CDR))
 (47 47 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (41 41 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (37 37 (:REWRITE USE-ALL-<-2))
 (37 37 (:REWRITE USE-ALL-<))
 (37 37 (:REWRITE DEFAULT-<-1))
 (19 19 (:REWRITE DEFAULT-+-2))
 (19 19 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(TRUE-LISTP-OF-MV-NTH-1-OF-MATCH-CHARS
 (361 30 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (52 3 (:LINEAR MATCH-CHARS-LEN-BOUND))
 (50 26 (:REWRITE DEFAULT-<-2))
 (43 43 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (30 30 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (30 30 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (26 26 (:REWRITE USE-ALL-<-2))
 (26 26 (:REWRITE USE-ALL-<))
 (26 26 (:REWRITE DEFAULT-<-1))
 (21 21 (:REWRITE DEFAULT-CDR))
 (18 18 (:REWRITE DEFAULT-CAR))
 (15 3 (:REWRITE LEN-OF-CDR))
 (6 6 (:REWRITE LEN-OF-MV-NTH-1-OF-MATCH-CHARS))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(PARSE-BOOLEAN)
(PARSE-BOOLEAN-LEN-BOUND
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 (1 1 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-BOOLEAN
 (32 2 (:DEFINITION TRUE-LISTP))
 (24 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(CHARACTER-LISTP-OF-MV-NTH-1-OF-PARSE-BOOLEAN
 (42 2 (:DEFINITION CHARACTER-LISTP))
 (24 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (8 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(BOOLEANP-OF-MV-NTH-0-OF-PARSE-BOOLEAN)
(PARSE-EQUALITY-ETC)
(PARSE-EQUALITY-ETC-LEN-BOUND
 (116 46 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-MATCH-CHARS))
 (72 12 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-BINARY-NUMBER-FROM-CHARS))
 (70 12 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (66 66 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (48 8 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-BOOLEAN))
 (45 5 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (9 6 (:REWRITE DEFAULT-+-2))
 (9 6 (:REWRITE DEFAULT-+-1))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE USE-ALL-<-2))
 (1 1 (:REWRITE USE-ALL-<))
 )
(TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-EQUALITY-ETC
 (32 2 (:DEFINITION TRUE-LISTP))
 (24 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(CHARACTER-LISTP-OF-MV-NTH-1-OF-PARSE-EQUALITY-ETC
 (42 2 (:DEFINITION CHARACTER-LISTP))
 (24 2 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (10 10 (:TYPE-PRESCRIPTION LEN))
 (8 2 (:TYPE-PRESCRIPTION CHARACTER-LISTP-OF-MV-NTH-1-OF-PARSE-BINARY-NUMBER-FROM-CHARS))
 (8 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (4 2 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-MATCH-CHARS))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (2 2 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (2 2 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 )
(TYPE-OF-MV-NTH-0-OF-PARSE-EQUALITY-ETC)
(MAYBE-PARSE-ARRAY-INDEX)
(MAYBE-PARSE-ARRAY-INDEX-LEN-BOUND
 (271 32 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (183 93 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (168 70 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-MATCH-CHARS))
 (162 27 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-BINARY-NUMBER-FROM-CHARS))
 (133 41 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (120 12 (:REWRITE DEFAULT-CDR))
 (97 97 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (44 25 (:REWRITE DEFAULT-+-2))
 (40 4 (:REWRITE DEFAULT-CAR))
 (32 32 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (31 25 (:REWRITE DEFAULT-+-1))
 (30 15 (:REWRITE DEFAULT-<-2))
 (19 15 (:REWRITE DEFAULT-<-1))
 (18 3 (:LINEAR LEN-OF-CDR-LINEAR-STRONG))
 (16 16 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (15 15 (:REWRITE USE-ALL-<-2))
 (15 15 (:REWRITE USE-ALL-<))
 )
(TRUE-LISTP-OF-MV-NTH-1-OF-MAYBE-PARSE-ARRAY-INDEX
 (40 4 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (32 2 (:DEFINITION TRUE-LISTP))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (12 3 (:REWRITE DEFAULT-CDR))
 (10 1 (:REWRITE DEFAULT-CAR))
 (8 4 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (6 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 )
(CHARACTER-LISTP-OF-MV-NTH-1-OF-MAYBE-PARSE-ARRAY-INDEX
 (42 2 (:DEFINITION CHARACTER-LISTP))
 (40 4 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (18 18 (:TYPE-PRESCRIPTION LEN))
 (12 3 (:REWRITE DEFAULT-CDR))
 (12 3 (:REWRITE DEFAULT-CAR))
 (8 4 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (8 2 (:TYPE-PRESCRIPTION CHARACTER-LISTP-OF-MV-NTH-1-OF-PARSE-BINARY-NUMBER-FROM-CHARS))
 (8 2 (:REWRITE CHARACTER-LISTP-OF-CDR))
 (6 6 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (4 4 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (4 2 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-MATCH-CHARS))
 (4 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (2 2 (:REWRITE USE-ALL-<-2))
 (2 2 (:REWRITE USE-ALL-<))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE CONSP-WHEN-LEN-GREATER))
 )
(TYPE-OF-MV-NTH-0-OF-MAYBE-PARSE-ARRAY-INDEX
 (48 6 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (30 3 (:REWRITE DEFAULT-CDR))
 (30 3 (:REWRITE DEFAULT-CAR))
 (24 24 (:TYPE-PRESCRIPTION LEN))
 (18 6 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (12 12 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (6 6 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 )
(PARSE-COUNTEREXAMPLE
 (1224 612 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-MATCH-CHARS))
 (990 33 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-DECIMAL-NUMBER-FROM-CHARS))
 (930 15 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-MAYBE-PARSE-ARRAY-INDEX))
 (756 6 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-EQUALITY-ETC))
 (690 690 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (551 33 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (336 24 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-READ-CHARS-TO-TERMINATOR))
 (157 5 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (81 2 (:REWRITE DEFAULT-CDR))
 (23 7 (:REWRITE DEFAULT-<-1))
 (18 16 (:REWRITE DEFAULT-+-2))
 (17 16 (:REWRITE DEFAULT-+-1))
 (11 7 (:REWRITE DEFAULT-<-2))
 (7 7 (:REWRITE USE-ALL-<-2))
 (7 7 (:REWRITE USE-ALL-<))
 (5 5 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (4 4 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(ALISTP-OF-PARSE-COUNTEREXAMPLE
 (6096 107 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5760 2880 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-MATCH-CHARS))
 (5220 174 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-DECIMAL-NUMBER-FROM-CHARS))
 (4836 78 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-MAYBE-PARSE-ARRAY-INDEX))
 (3780 30 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-EQUALITY-ETC))
 (3246 180 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (3227 3227 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (1170 6 (:LINEAR PARSE-EQUALITY-ETC-LEN-BOUND))
 (1088 60 (:REWRITE DEFAULT-CDR))
 (910 65 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-READ-CHARS-TO-TERMINATOR))
 (594 6 (:LINEAR MAYBE-PARSE-ARRAY-INDEX-LEN-BOUND))
 (312 6 (:LINEAR PARSE-DECIMAL-NUMBER-FROM-CHARS-LEN-BOUND))
 (188 94 (:REWRITE DEFAULT-<-2))
 (144 24 (:REWRITE LEN-OF-MV-NTH-1-OF-MATCH-CHARS))
 (138 69 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (108 6 (:LINEAR MATCH-CHARS-LEN-BOUND))
 (107 107 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (94 94 (:REWRITE USE-ALL-<-2))
 (94 94 (:REWRITE USE-ALL-<))
 (94 94 (:REWRITE DEFAULT-<-1))
 (94 94 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (80 79 (:REWRITE DEFAULT-CAR))
 (69 69 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 (66 33 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (42 12 (:REWRITE COMMUTATIVITY-OF-+))
 (33 33 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (30 24 (:REWRITE DEFAULT-+-2))
 (30 24 (:REWRITE DEFAULT-+-1))
 (18 6 (:REWRITE REVERSE-LIST-OF-CONS))
 (12 6 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 )
(RAW-COUNTEREXAMPLEP-OF-PARSE-COUNTEREXAMPLE
 (9320 4660 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-MATCH-CHARS))
 (9304 123 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (8700 290 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-DECIMAL-NUMBER-FROM-CHARS))
 (8060 130 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-MAYBE-PARSE-ARRAY-INDEX))
 (6300 50 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-PARSE-EQUALITY-ETC))
 (5215 5215 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (5197 230 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1950 10 (:LINEAR PARSE-EQUALITY-ETC-LEN-BOUND))
 (1543 199 (:REWRITE DEFAULT-CDR))
 (1190 85 (:TYPE-PRESCRIPTION TRUE-LISTP-OF-MV-NTH-1-OF-READ-CHARS-TO-TERMINATOR))
 (990 10 (:LINEAR MAYBE-PARSE-ARRAY-INDEX-LEN-BOUND))
 (520 10 (:LINEAR PARSE-DECIMAL-NUMBER-FROM-CHARS-LEN-BOUND))
 (240 40 (:REWRITE LEN-OF-MV-NTH-1-OF-MATCH-CHARS))
 (212 106 (:REWRITE DEFAULT-<-2))
 (180 10 (:LINEAR MATCH-CHARS-LEN-BOUND))
 (136 135 (:REWRITE DEFAULT-CAR))
 (123 123 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (108 54 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (106 106 (:REWRITE USE-ALL-<-2))
 (106 106 (:REWRITE USE-ALL-<))
 (106 106 (:REWRITE DEFAULT-<-1))
 (106 106 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (70 20 (:REWRITE COMMUTATIVITY-OF-+))
 (54 54 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (50 40 (:REWRITE DEFAULT-+-2))
 (50 40 (:REWRITE DEFAULT-+-1))
 (30 10 (:REWRITE REVERSE-LIST-OF-CONS))
 (20 10 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 )
(PARSE-COUNTEREXAMPLE
 (149 11 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (23 1 (:LINEAR READ-CHARS-TO-TERMINATOR-LEN-BOUND))
 (20 14 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (20 10 (:REWRITE DEFAULT-<-2))
 (20 10 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (20 8 (:REWRITE DEFAULT-CDR))
 (16 11 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (16 2 (:REWRITE LEN-OF-MV-NTH-1-OF-MATCH-CHARS))
 (11 11 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (11 11 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (10 10 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 (10 10 (:REWRITE USE-ALL-<-2))
 (10 10 (:REWRITE USE-ALL-<))
 (10 10 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE DEFAULT-CAR))
 (9 2 (:REWRITE COMMUTATIVITY-OF-+))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (5 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 )
(COUNTEREXAMPLEP)
(ALISTP-WHEN-COUNTEREXAMPLEP
 (299 24 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (105 5 (:DEFINITION TRUE-LISTP))
 (48 48 (:REWRITE DEFAULT-CAR))
 (45 24 (:REWRITE DEFAULT-<-2))
 (40 40 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (32 32 (:REWRITE DEFAULT-CDR))
 (31 5 (:REWRITE LEN-OF-CDR))
 (24 24 (:REWRITE USE-ALL-<-2))
 (24 24 (:REWRITE USE-ALL-<))
 (24 24 (:REWRITE DEFAULT-<-1))
 (24 24 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (24 24 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (18 9 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (14 7 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (9 9 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (7 7 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 (7 5 (:REWRITE DEFAULT-+-2))
 (5 5 (:REWRITE DEFAULT-+-1))
 (5 5 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (2 2 (:REWRITE EQUAL-OF-LEN-AND-0))
 )
(COUNTEREXAMPLEP-OF-REVERSE-LIST
 (5535 404 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (2295 96 (:REWRITE CDR-OF-REVERSE-LIST))
 (1680 96 (:DEFINITION TAKE))
 (1110 180 (:REWRITE LEN-OF-CDR))
 (992 128 (:REWRITE ZP-OPEN))
 (956 579 (:REWRITE DEFAULT-<-2))
 (790 604 (:REWRITE DEFAULT-+-2))
 (765 32 (:REWRITE CAR-OF-REVERSE-LIST))
 (609 41 (:REWRITE CONSP-OF-REVERSE-LIST))
 (605 605 (:REWRITE DEFAULT-CDR))
 (604 604 (:REWRITE DEFAULT-+-1))
 (579 579 (:REWRITE USE-ALL-<-2))
 (579 579 (:REWRITE USE-ALL-<))
 (579 579 (:REWRITE DEFAULT-<-1))
 (560 32 (:DEFINITION NTH))
 (548 164 (:REWRITE FOLD-CONSTS-IN-+))
 (461 461 (:REWRITE DEFAULT-CAR))
 (404 404 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (395 395 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (136 50 (:REWRITE LEN-OF-REVERSE-LIST))
 (135 135 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (98 49 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (70 70 (:REWRITE EQUAL-OF-LEN-AND-0))
 (49 49 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 )
(NATP-OF-MAXELEM-OF-STRIP-CARS-WHEN-COUNTEREXAMPLEP
 (613 51 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (294 15 (:REWRITE MAXELEM-SINGLETON-ALT))
 (159 42 (:REWRITE DEFAULT-<-1))
 (153 153 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (152 6 (:DEFINITION TRUE-LISTP))
 (144 25 (:REWRITE LEN-OF-CDR))
 (111 102 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (87 56 (:REWRITE DEFAULT-CAR))
 (71 42 (:REWRITE DEFAULT-<-2))
 (66 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (60 53 (:REWRITE DEFAULT-CDR))
 (60 6 (:REWRITE <=-OF-MAXELEM-WHEN-MEMBER-EQUAL))
 (45 3 (:REWRITE RATIONALP-OF-MAXELEM))
 (42 42 (:REWRITE USE-ALL-<-2))
 (42 42 (:REWRITE USE-ALL-<))
 (42 42 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (42 6 (:DEFINITION MEMBER-EQUAL))
 (33 15 (:REWRITE MAXELEM-WHEN-NON-CONSP))
 (33 3 (:REWRITE ACL2-NUMBERP-OF-MAXELEM))
 (30 30 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (29 18 (:REWRITE DEFAULT-+-2))
 (24 3 (:LINEAR MAXELEM-OF-STRIP-CARS-LINEAR))
 (24 3 (:DEFINITION INTEGER-LISTP))
 (18 18 (:REWRITE DEFAULT-+-1))
 (18 3 (:REWRITE RATIONAL-LISTP-OF-STRIP-CARS))
 (18 3 (:DEFINITION RATIONAL-LISTP))
 (16 8 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (15 15 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (12 12 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 (11 11 (:REWRITE EQUAL-OF-LEN-AND-0))
 (9 3 (:REWRITE NODENUM-TYPE-ALISTP-OF-CDR))
 (8 8 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (6 3 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 )
(RATIONAL-LISTP-OF-STRIP-CARS-WHEN-COUNTEREXAMPLEP
 (276 20 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (108 4 (:DEFINITION TRUE-LISTP))
 (45 24 (:REWRITE DEFAULT-CAR))
 (41 20 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (36 18 (:REWRITE DEFAULT-<-2))
 (35 32 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (32 4 (:REWRITE LEN-OF-CDR))
 (30 6 (:REWRITE RATIONAL-LISTP-OF-STRIP-CARS))
 (25 22 (:REWRITE DEFAULT-CDR))
 (20 20 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 (20 20 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (18 18 (:REWRITE USE-ALL-<-2))
 (18 18 (:REWRITE USE-ALL-<))
 (18 18 (:REWRITE DEFAULT-<-1))
 (18 18 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (12 4 (:REWRITE NODENUM-TYPE-ALISTP-OF-CDR))
 (8 4 (:REWRITE DEFAULT-+-2))
 (8 4 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (4 4 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (4 4 (:REWRITE EQUAL-OF-LEN-AND-0))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(<=-OF-0-AND-MAXELEM-OF-STRIP-CARS-WHEN-COUNTEREXAMPLEP
 (6 3 (:TYPE-PRESCRIPTION RATIONALP-OF-MAXELEM))
 (3 3 (:TYPE-PRESCRIPTION STRIP-CARS))
 )
(<=-OF-0-AND-MAXELEM-OF-STRIP-CARS-WHEN-NODENUM-TYPE-ALISTP
 (1056 100 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (819 6 (:LINEAR <=-OF-0-AND-MAXELEM-OF-STRIP-CARS-WHEN-COUNTEREXAMPLEP))
 (804 15 (:DEFINITION COUNTEREXAMPLEP))
 (634 317 (:TYPE-PRESCRIPTION RATIONALP-OF-MAXELEM))
 (496 66 (:REWRITE DEFAULT-<-1))
 (367 13 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (360 12 (:DEFINITION TRUE-LISTP))
 (359 22 (:REWRITE MAXELEM-SINGLETON-ALT))
 (287 123 (:REWRITE DEFAULT-CAR))
 (269 66 (:REWRITE DEFAULT-<-2))
 (214 33 (:REWRITE LEN-OF-CDR))
 (176 160 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (159 9 (:REWRITE RATIONALP-OF-CAR-OF-CAR))
 (158 61 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (136 136 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (135 9 (:DEFINITION RATIONAL-LISTP))
 (118 117 (:REWRITE DEFAULT-CDR))
 (103 8 (:REWRITE ACL2-NUMBERP-OF-MAXELEM))
 (98 8 (:REWRITE <=-OF-MAXELEM-WHEN-MEMBER-EQUAL))
 (81 81 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (79 8 (:DEFINITION INTEGER-LISTP))
 (74 8 (:DEFINITION MEMBER-EQUAL))
 (73 8 (:REWRITE RATIONALP-OF-MAXELEM))
 (66 66 (:REWRITE USE-ALL-<-2))
 (66 66 (:REWRITE USE-ALL-<))
 (50 20 (:REWRITE MAXELEM-WHEN-NON-CONSP))
 (49 32 (:REWRITE DEFAULT-+-2))
 (48 48 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (40 40 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (40 40 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (32 32 (:REWRITE DEFAULT-+-1))
 (32 16 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (29 11 (:REWRITE RATIONAL-LISTP-OF-STRIP-CARS))
 (22 11 (:REWRITE RATIONAL-LISTP-OF-STRIP-CARS-WHEN-COUNTEREXAMPLEP))
 (17 17 (:REWRITE EQUAL-OF-LEN-AND-0))
 (16 16 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (16 8 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (12 12 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (8 2 (:REWRITE NODENUM-TYPE-ALISTP-OF-CDR))
 (3 3 (:REWRITE CDR-CONS))
 (3 3 (:REWRITE CAR-CONS))
 )
(INTEGERP-OF-MAXELEM-OF-STRIP-CARS-WHEN-NODENUM-TYPE-ALISTP
 (432 216 (:TYPE-PRESCRIPTION RATIONALP-OF-MAXELEM))
 (252 31 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (118 7 (:REWRITE MAXELEM-SINGLETON-ALT))
 (54 30 (:REWRITE DEFAULT-CAR))
 (53 48 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (49 49 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (49 16 (:REWRITE DEFAULT-<-1))
 (48 3 (:REWRITE INTEGERP-OF-MAXELEM))
 (47 4 (:DEFINITION INTEGER-LISTP))
 (44 10 (:REWRITE LEN-OF-CDR))
 (33 5 (:REWRITE NODENUM-TYPE-ALISTP-OF-CDR))
 (28 25 (:REWRITE DEFAULT-CDR))
 (28 16 (:REWRITE DEFAULT-<-2))
 (25 7 (:REWRITE MAXELEM-WHEN-NON-CONSP))
 (23 23 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (20 20 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (20 2 (:REWRITE <=-OF-MAXELEM-WHEN-MEMBER-EQUAL))
 (16 16 (:REWRITE USE-ALL-<-2))
 (16 16 (:REWRITE USE-ALL-<))
 (14 2 (:DEFINITION MEMBER-EQUAL))
 (14 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (11 1 (:REWRITE ACL2-NUMBERP-OF-MAXELEM))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (10 5 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (10 1 (:LINEAR <=-OF-0-AND-MAXELEM-OF-STRIP-CARS-WHEN-COUNTEREXAMPLEP))
 (8 4 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (8 1 (:LINEAR MAXELEM-OF-STRIP-CARS-LINEAR))
 (8 1 (:LINEAR <=-OF-0-AND-MAXELEM-OF-STRIP-CARS-WHEN-NODENUM-TYPE-ALISTP))
 (8 1 (:DEFINITION COUNTEREXAMPLEP))
 (6 4 (:REWRITE DEFAULT-+-2))
 (5 5 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (5 1 (:REWRITE RATIONALP-OF-MAXELEM))
 (4 4 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (4 4 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE EQUAL-OF-LEN-AND-0))
 (2 1 (:REWRITE RATIONAL-LISTP-OF-STRIP-CARS-WHEN-COUNTEREXAMPLEP))
 (1 1 (:REWRITE RATIONAL-LISTP-OF-STRIP-CARS))
 )
(ALL-INTEGERP-OF-STRIP-CARS-WHEN-NODENUM-TYPE-ALISTP
 (123 11 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (30 12 (:REWRITE DEFAULT-CAR))
 (18 9 (:REWRITE DEFAULT-<-2))
 (16 11 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (14 14 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (11 11 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (10 5 (:REWRITE ALL-INTEGERP-WHEN-NOT-CONSP-CHEAP))
 (9 9 (:REWRITE USE-ALL-<-2))
 (9 9 (:REWRITE USE-ALL-<))
 (9 9 (:REWRITE DEFAULT-<-1))
 (9 9 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (8 2 (:REWRITE NODENUM-TYPE-ALISTP-OF-CDR))
 (7 7 (:REWRITE DEFAULT-CDR))
 (6 3 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (5 5 (:TYPE-PRESCRIPTION STRIP-CARS))
 (3 3 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 )
(SET-ARRAY-VALS-FROM-COUNTEREXAMPLE
 (393 40 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (112 7 (:DEFINITION TRUE-LISTP))
 (71 44 (:REWRITE DEFAULT-CDR))
 (58 31 (:REWRITE DEFAULT-<-2))
 (55 37 (:REWRITE DEFAULT-CAR))
 (50 50 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (50 25 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (40 40 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (39 1 (:DEFINITION UPDATE-NTH))
 (35 35 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (32 31 (:REWRITE DEFAULT-<-1))
 (31 31 (:REWRITE USE-ALL-<-2))
 (31 31 (:REWRITE USE-ALL-<))
 (25 25 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (10 2 (:REWRITE LEN-OF-CDR))
 (6 1 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(TRUE-LISTP-OF-SET-ARRAY-VALS-FROM-COUNTEREXAMPLE
 (549 56 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (231 7 (:DEFINITION UPDATE-NTH))
 (218 54 (:REWRITE DEFAULT-CDR))
 (188 49 (:REWRITE DEFAULT-CAR))
 (187 11 (:DEFINITION TRUE-LISTP))
 (97 93 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (56 56 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (53 31 (:REWRITE DEFAULT-<-2))
 (42 7 (:REWRITE ZP-OPEN))
 (31 31 (:REWRITE USE-ALL-<-2))
 (31 31 (:REWRITE USE-ALL-<))
 (31 31 (:REWRITE DEFAULT-<-1))
 (24 24 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (14 7 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (10 2 (:REWRITE LEN-OF-CDR))
 (9 9 (:REWRITE DEFAULT-+-2))
 (9 9 (:REWRITE DEFAULT-+-1))
 (7 7 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (2 2 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(FIXUP-COUNTEREXAMPLE
 (1690 137 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (322 161 (:REWRITE DEFAULT-<-2))
 (296 259 (:REWRITE DEFAULT-CDR))
 (199 188 (:REWRITE DEFAULT-CAR))
 (182 91 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (171 161 (:REWRITE DEFAULT-<-1))
 (166 137 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (161 161 (:REWRITE USE-ALL-<-2))
 (161 161 (:REWRITE USE-ALL-<))
 (155 155 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (142 108 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (137 137 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (134 134 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (115 5 (:DEFINITION EXPT))
 (91 91 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (88 4 (:REWRITE REPEAT-WHEN-ZP))
 (78 78 (:TYPE-PRESCRIPTION NATP))
 (72 4 (:REWRITE ZP-OPEN))
 (56 7 (:REWRITE LEN-OF-CDR))
 (48 24 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (25 5 (:REWRITE ZIP-OPEN))
 (24 17 (:REWRITE DEFAULT-+-2))
 (17 17 (:REWRITE DEFAULT-+-1))
 (15 5 (:REWRITE DEFAULT-*-2))
 (15 5 (:REWRITE COMMUTATIVITY-OF-+))
 (7 7 (:REWRITE EQUAL-OF-LEN-AND-0))
 (7 7 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (6 6 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (5 5 (:REWRITE DEFAULT-*-1))
 (4 4 (:TYPE-PRESCRIPTION ZP))
 (1 1 (:TYPE-PRESCRIPTION AXE-TYPEP))
 )
(ALISTP-OF-MV-NTH-1-OF-FIXUP-COUNTEREXAMPLE
 (3455 318 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (2832 212 (:REWRITE DEFAULT-CDR))
 (1548 36 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (950 475 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (763 313 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (702 233 (:REWRITE DEFAULT-CAR))
 (630 481 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (482 250 (:REWRITE DEFAULT-<-2))
 (345 15 (:DEFINITION EXPT))
 (333 333 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 (318 318 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (314 157 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (280 250 (:REWRITE DEFAULT-<-1))
 (250 250 (:REWRITE USE-ALL-<-2))
 (250 250 (:REWRITE USE-ALL-<))
 (198 9 (:REWRITE REPEAT-WHEN-ZP))
 (175 175 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (162 9 (:REWRITE ZP-OPEN))
 (157 157 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 (146 73 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (90 90 (:TYPE-PRESCRIPTION NATP-OF-BV-ARRAY-TYPE-LEN))
 (75 15 (:REWRITE ZIP-OPEN))
 (73 73 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (50 50 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (45 15 (:REWRITE DEFAULT-*-2))
 (45 15 (:REWRITE COMMUTATIVITY-OF-+))
 (35 35 (:REWRITE DEFAULT-+-2))
 (35 35 (:REWRITE DEFAULT-+-1))
 (25 5 (:REWRITE LEN-OF-CDR))
 (15 15 (:REWRITE DEFAULT-*-1))
 (15 5 (:REWRITE REVERSE-LIST-OF-CONS))
 (10 5 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (9 9 (:TYPE-PRESCRIPTION ZP))
 (5 5 (:TYPE-PRESCRIPTION REVERSE-LIST))
 (5 5 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 )
(STRIP-CARS-OF-MV-NTH-1-OF-FIXUP-COUNTEREXAMPLE
 (5581 530 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (5128 388 (:REWRITE DEFAULT-CDR))
 (2838 66 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (2508 66 (:DEFINITION ALISTP))
 (1701 457 (:REWRITE DEFAULT-CAR))
 (1402 520 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (1226 613 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (1144 867 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (743 395 (:REWRITE DEFAULT-<-2))
 (690 30 (:DEFINITION EXPT))
 (530 530 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (482 482 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 (455 395 (:REWRITE DEFAULT-<-1))
 (424 28 (:REWRITE ZP-OPEN))
 (397 19 (:REWRITE REPEAT-WHEN-ZP))
 (395 395 (:REWRITE USE-ALL-<-2))
 (395 395 (:REWRITE USE-ALL-<))
 (264 132 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (232 232 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (180 180 (:TYPE-PRESCRIPTION NATP-OF-BV-ARRAY-TYPE-LEN))
 (150 30 (:REWRITE ZIP-OPEN))
 (135 5 (:REWRITE CDR-OF-REVERSE-LIST))
 (135 5 (:REWRITE CAR-OF-REVERSE-LIST))
 (132 132 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 (132 66 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (120 100 (:REWRITE DEFAULT-+-2))
 (110 5 (:DEFINITION TAKE))
 (110 5 (:DEFINITION NTH))
 (100 100 (:REWRITE DEFAULT-+-1))
 (94 94 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (90 30 (:REWRITE DEFAULT-*-2))
 (90 30 (:REWRITE COMMUTATIVITY-OF-+))
 (87 5 (:REWRITE CONSP-OF-REVERSE-LIST))
 (66 66 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (50 10 (:REWRITE LEN-OF-CDR))
 (40 10 (:REWRITE FOLD-CONSTS-IN-+))
 (30 30 (:REWRITE DEFAULT-*-1))
 (18 18 (:TYPE-PRESCRIPTION ZP))
 (14 5 (:REWRITE LEN-OF-REVERSE-LIST))
 (10 10 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (2 1 (:TYPE-PRESCRIPTION SET-ARRAY-VALS-FROM-COUNTEREXAMPLE))
 (1 1 (:TYPE-PRESCRIPTION REPEAT))
 )
(CONSP-OF-MV-NTH-1-OF-FIXUP-COUNTEREXAMPLE
 (7504 462 (:REWRITE DEFAULT-CDR))
 (6919 677 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (4128 96 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (3648 96 (:DEFINITION ALISTP))
 (2104 1052 (:TYPE-PRESCRIPTION ASSOC-EQUAL-TYPE))
 (1962 502 (:REWRITE DEFAULT-CAR))
 (1519 1150 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (897 39 (:DEFINITION EXPT))
 (849 456 (:REWRITE DEFAULT-<-2))
 (825 825 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 (534 456 (:REWRITE DEFAULT-<-1))
 (506 23 (:REWRITE REPEAT-WHEN-ZP))
 (456 456 (:REWRITE USE-ALL-<-2))
 (456 456 (:REWRITE USE-ALL-<))
 (414 23 (:REWRITE ZP-OPEN))
 (384 192 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (259 259 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (230 230 (:TYPE-PRESCRIPTION NATP-OF-BV-ARRAY-TYPE-LEN))
 (195 39 (:REWRITE ZIP-OPEN))
 (192 192 (:TYPE-PRESCRIPTION NODENUM-TYPE-ALISTP))
 (192 96 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (142 142 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (117 39 (:REWRITE DEFAULT-*-2))
 (117 39 (:REWRITE COMMUTATIVITY-OF-+))
 (96 96 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (95 25 (:REWRITE LEN-OF-CDR))
 (88 88 (:REWRITE DEFAULT-+-2))
 (88 88 (:REWRITE DEFAULT-+-1))
 (50 25 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (39 39 (:REWRITE DEFAULT-*-1))
 (23 23 (:TYPE-PRESCRIPTION ZP))
 (2 1 (:REWRITE LEN-OF-REVERSE-LIST))
 )
(COUNTEREXAMPLEP-OF-MV-NTH-1-OF-FIXUP-COUNTEREXAMPLE
 (4681 392 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (3386 483 (:REWRITE DEFAULT-CDR))
 (1838 12 (:REWRITE CONSP-OF-MV-NTH-1-OF-FIXUP-COUNTEREXAMPLE))
 (1806 42 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (1596 42 (:DEFINITION ALISTP))
 (910 382 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (784 14 (:DEFINITION RAW-COUNTEREXAMPLEP))
 (770 602 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (753 355 (:REWRITE DEFAULT-CAR))
 (729 376 (:REWRITE DEFAULT-<-2))
 (729 27 (:DEFINITION TRUE-LISTP))
 (506 22 (:DEFINITION EXPT))
 (458 458 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 (420 376 (:REWRITE DEFAULT-<-1))
 (392 392 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (376 376 (:REWRITE USE-ALL-<-2))
 (376 376 (:REWRITE USE-ALL-<))
 (352 16 (:REWRITE REPEAT-WHEN-ZP))
 (288 16 (:REWRITE ZP-OPEN))
 (266 37 (:REWRITE LEN-OF-CDR))
 (259 259 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (238 119 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (168 84 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (160 160 (:TYPE-PRESCRIPTION NATP-OF-BV-ARRAY-TYPE-LEN))
 (119 119 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (110 22 (:REWRITE ZIP-OPEN))
 (108 81 (:REWRITE DEFAULT-+-2))
 (81 81 (:REWRITE DEFAULT-+-1))
 (66 22 (:REWRITE DEFAULT-*-2))
 (66 22 (:REWRITE COMMUTATIVITY-OF-+))
 (64 64 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (37 37 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (30 10 (:REWRITE REVERSE-LIST-OF-CONS))
 (27 27 (:REWRITE EQUAL-OF-LEN-AND-0))
 (22 22 (:REWRITE DEFAULT-*-1))
 (20 10 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (16 16 (:TYPE-PRESCRIPTION ZP))
 (10 10 (:TYPE-PRESCRIPTION REVERSE-LIST))
 (8 2 (:REWRITE NODENUM-TYPE-ALISTP-OF-CDR))
 )
(BOUNDED-COUNTEREXAMPLEP)
(BOUNDED-COUNTEREXAMPLEP-OF-MV-NTH-1-OF-FIXUP-COUNTEREXAMPLE
 (11521 1060 (:REWRITE CONSP-FROM-LEN-CHEAP))
 (7603 971 (:REWRITE DEFAULT-CDR))
 (7302 137 (:REWRITE ALL-<-WHEN-NOT-CONSP))
 (6051 39 (:REWRITE CONSP-OF-MV-NTH-1-OF-FIXUP-COUNTEREXAMPLE))
 (4730 110 (:REWRITE CONSP-OF-ASSOC-EQUAL))
 (4180 110 (:DEFINITION ALISTP))
 (3050 1011 (:REWRITE DEFAULT-<-1))
 (2934 962 (:REWRITE DEFAULT-CAR))
 (2106 980 (:LINEAR LEN-POSITIVE-WHEN-CONSP-LINEAR-CHEAP))
 (2030 26 (:REWRITE STRIP-CARS-OF-MV-NTH-1-OF-FIXUP-COUNTEREXAMPLE))
 (1990 65 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1974 1011 (:REWRITE DEFAULT-<-2))
 (1925 90 (:REWRITE RATIONALP-OF-CAR-OF-CAR))
 (1763 1491 (:REWRITE LEN-WHEN-NOT-CONSP-CHEAP))
 (1635 60 (:DEFINITION RATIONAL-LISTP))
 (1311 57 (:DEFINITION EXPT))
 (1145 53 (:REWRITE REPEAT-WHEN-ZP))
 (1111 1011 (:REWRITE USE-ALL-<))
 (1060 1060 (:REWRITE CONSP-WHEN-LEN-EQUAL-CONSTANT))
 (1029 37 (:DEFINITION TRUE-LISTP))
 (1011 1011 (:REWRITE USE-ALL-<-2))
 (936 52 (:REWRITE ZP-OPEN))
 (880 40 (:REWRITE USE-ALL-<-FOR-CAR))
 (786 786 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 (692 692 (:REWRITE CONSP-WHEN-LEN-GREATER))
 (626 13 (:REWRITE COUNTEREXAMPLEP-OF-MV-NTH-1-OF-FIXUP-COUNTEREXAMPLE))
 (536 268 (:REWRITE CONSP-OF-CAR-WHEN-SYMBOL-TERM-ALISTP-CHEAP))
 (520 520 (:TYPE-PRESCRIPTION NATP-OF-BV-ARRAY-TYPE-LEN))
 (446 67 (:REWRITE LEN-OF-CDR))
 (440 220 (:REWRITE ALISTP-WHEN-NODENUM-TYPE-ALISTP-CHEAP))
 (285 57 (:REWRITE ZIP-OPEN))
 (270 270 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (268 268 (:TYPE-PRESCRIPTION SYMBOL-TERM-ALISTP))
 (239 137 (:REWRITE ALL-<-WHEN-NOT-CONSP-CHEAP))
 (218 181 (:REWRITE DEFAULT-+-2))
 (207 3 (:DEFINITION RAW-COUNTEREXAMPLEP))
 (181 181 (:REWRITE DEFAULT-+-1))
 (171 57 (:REWRITE DEFAULT-*-2))
 (171 57 (:REWRITE COMMUTATIVITY-OF-+))
 (160 60 (:REWRITE RATIONAL-LISTP-OF-STRIP-CARS))
 (150 150 (:REWRITE ALL-<-TRANSITIVE-FREE-2))
 (150 150 (:REWRITE ALL-<-TRANSITIVE-FREE))
 (130 130 (:REWRITE ASSOC-EQUAL-WHEN-NOT-CONSP-CHEAP))
 (120 60 (:REWRITE RATIONAL-LISTP-OF-STRIP-CARS-WHEN-COUNTEREXAMPLEP))
 (109 109 (:REWRITE NOT-ALL-<-WHEN-MEMBERP))
 (109 109 (:REWRITE NOT-ALL-<-WHEN-MEMBER-EQUAL))
 (100 100 (:TYPE-PRESCRIPTION MEMBERP))
 (90 30 (:REWRITE REVERSE-LIST-OF-CONS))
 (80 40 (:REWRITE <-OF-CAR-WHEN-ALL-<-CHEAP))
 (70 70 (:TYPE-PRESCRIPTION ACONS))
 (67 67 (:REWRITE CONSP-OF-CDR-WHEN-LEN-KNOWN))
 (60 30 (:REWRITE APPEND-WHEN-NOT-CONSP-ARG1-CHEAP))
 (57 57 (:REWRITE DEFAULT-*-1))
 (52 52 (:TYPE-PRESCRIPTION ZP))
 (37 37 (:REWRITE EQUAL-OF-LEN-AND-0))
 (33 33 (:TYPE-PRESCRIPTION RAW-COUNTEREXAMPLEP))
 (32 32 (:TYPE-PRESCRIPTION REVERSE-LIST))
 (20 20 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (20 5 (:REWRITE NODENUM-TYPE-ALISTP-OF-CDR))
 (19 1 (:REWRITE CONSP-OF-REVERSE-LIST))
 (3 1 (:REWRITE LEN-OF-REVERSE-LIST))
 )
