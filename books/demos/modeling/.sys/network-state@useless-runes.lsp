(UNKNOWN-OR-INTEGERP)
(CLIENT-STATE-P
 (2 2 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 )
(CLIENT-STATE)
(HONSED-CLIENT-STATE)
(CLIENT-STATE->NUMBER-TO-SQUARE$INLINE
 (2 2 (:DEFINITION ASSOC-EQUAL))
 )
(CLIENT-STATE->ANSWER$INLINE
 (2 2 (:DEFINITION ASSOC-EQUAL))
 )
(CONSP-OF-CLIENT-STATE)
(BOOLEANP-OF-CLIENT-STATE-P)
(CLIENT-STATE-P-OF-CLIENT-STATE)
(TAG-OF-CLIENT-STATE)
(TAG-WHEN-CLIENT-STATE-P)
(CLIENT-STATE-P-WHEN-WRONG-TAG)
(CONSP-WHEN-CLIENT-STATE-P)
(CLIENT-STATE->NUMBER-TO-SQUARE-OF-CLIENT-STATE)
(CLIENT-STATE->ANSWER-OF-CLIENT-STATE)
(INTEGER-P-OF-CLIENT-STATE->NUMBER-TO-SQUARE)
(UNKNOWN-OR-INTEGERP-OF-CLIENT-STATE->ANSWER)
(SERVER-STATE-P
 (3 3 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 )
(SERVER-STATE)
(HONSED-SERVER-STATE)
(SERVER-STATE->REQUESTS-SERVED$INLINE
 (1 1 (:DEFINITION ASSOC-EQUAL))
 )
(CONSP-OF-SERVER-STATE)
(BOOLEANP-OF-SERVER-STATE-P)
(SERVER-STATE-P-OF-SERVER-STATE)
(TAG-OF-SERVER-STATE)
(TAG-WHEN-SERVER-STATE-P)
(SERVER-STATE-P-WHEN-WRONG-TAG)
(CONSP-WHEN-SERVER-STATE-P)
(SERVER-STATE->REQUESTS-SERVED-OF-SERVER-STATE)
(INTEGERP-OF-SERVER-STATE->REQUESTS-SERVED)
(MESSAGE-P
 (2 2 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 )
(MESSAGE)
(HONSED-MESSAGE)
(MESSAGE->TAG$INLINE
 (2 2 (:DEFINITION ASSOC-EQUAL))
 )
(MESSAGE->PAYLOAD$INLINE
 (2 2 (:DEFINITION ASSOC-EQUAL))
 )
(CONSP-OF-MESSAGE)
(BOOLEANP-OF-MESSAGE-P)
(MESSAGE-P-OF-MESSAGE)
(TAG-OF-MESSAGE)
(TAG-WHEN-MESSAGE-P)
(MESSAGE-P-WHEN-WRONG-TAG)
(CONSP-WHEN-MESSAGE-P)
(MESSAGE->TAG-OF-MESSAGE)
(MESSAGE->PAYLOAD-OF-MESSAGE)
(KEYWORDP-OF-MESSAGE->TAG)
(INTEGERP-OF-MESSAGE->PAYLOAD)
(ID-P)
(ID-P-IMPLIES-KEYWORDP
 (2 2 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 )
(NETWORK-PACKET-P
 (3 3 (:TYPE-PRESCRIPTION CONSP-ASSOC-EQUAL))
 )
(NETWORK-PACKET)
(HONSED-NETWORK-PACKET)
(NETWORK-PACKET->SENDER$INLINE
 (3 3 (:DEFINITION ASSOC-EQUAL))
 )
(NETWORK-PACKET->DEST$INLINE
 (3 3 (:DEFINITION ASSOC-EQUAL))
 )
(NETWORK-PACKET->MESSAGE$INLINE
 (3 3 (:DEFINITION ASSOC-EQUAL))
 )
(CONSP-OF-NETWORK-PACKET)
(BOOLEANP-OF-NETWORK-PACKET-P)
(NETWORK-PACKET-P-OF-NETWORK-PACKET)
(TAG-OF-NETWORK-PACKET)
(TAG-WHEN-NETWORK-PACKET-P)
(NETWORK-PACKET-P-WHEN-WRONG-TAG)
(CONSP-WHEN-NETWORK-PACKET-P)
(NETWORK-PACKET->SENDER-OF-NETWORK-PACKET)
(NETWORK-PACKET->DEST-OF-NETWORK-PACKET)
(NETWORK-PACKET->MESSAGE-OF-NETWORK-PACKET)
(ID-P-OF-NETWORK-PACKET->SENDER)
(ID-P-OF-NETWORK-PACKET->DEST)
(MESSAGE-P-OF-NETWORK-PACKET->MESSAGE)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(NETWORK-STATE-P)
(NETWORK-STATE-P-OF-CONS)
(NETWORK-STATE-P-OF-CDR-WHEN-NETWORK-STATE-P)
(NETWORK-STATE-P-WHEN-NOT-CONSP)
(NETWORK-PACKET-P-OF-CAR-WHEN-NETWORK-STATE-P)
(TRUE-LISTP-WHEN-NETWORK-STATE-P-COMPOUND-RECOGNIZER)
(NETWORK-STATE-P-OF-LIST-FIX)
(NETWORK-STATE-P-OF-SFIX)
(NETWORK-STATE-P-OF-INSERT)
(NETWORK-STATE-P-OF-DELETE)
(NETWORK-STATE-P-OF-MERGESORT)
(NETWORK-STATE-P-OF-UNION)
(NETWORK-STATE-P-OF-INTERSECT-1)
(NETWORK-STATE-P-OF-INTERSECT-2)
(NETWORK-STATE-P-OF-DIFFERENCE)
(NETWORK-STATE-P-OF-DUPLICATED-MEMBERS)
(NETWORK-STATE-P-OF-REV)
(NETWORK-STATE-P-OF-APPEND)
(NETWORK-STATE-P-OF-RCONS)
(NETWORK-PACKET-P-WHEN-MEMBER-EQUAL-OF-NETWORK-STATE-P)
(NETWORK-STATE-P-WHEN-SUBSETP-EQUAL)
(NETWORK-STATE-P-OF-SET-DIFFERENCE-EQUAL)
(NETWORK-STATE-P-OF-INTERSECTION-EQUAL-1)
(NETWORK-STATE-P-OF-INTERSECTION-EQUAL-2)
(NETWORK-STATE-P-OF-UNION-EQUAL)
(NETWORK-STATE-P-OF-TAKE)
(NETWORK-STATE-P-OF-REPEAT)
(NETWORK-PACKET-P-OF-NTH-WHEN-NETWORK-STATE-P)
(NETWORK-STATE-P-OF-UPDATE-NTH)
(NETWORK-STATE-P-OF-BUTLAST)
(NETWORK-STATE-P-OF-NTHCDR)
(NETWORK-STATE-P-OF-LAST)
(NETWORK-STATE-P-OF-REMOVE)
(NETWORK-STATE-P-OF-REVAPPEND)
(SQUARE
 (5 5 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-POSITIVE))
 (5 5 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NONZERO))
 )
(SQUARE-OUTPUT-LEMMA)
(RETRIEVE-NETWORK-MESSAGE
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE NETWORK-STATE-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(RETRIEVE-NETWORK-MESSAGE-RETURNS-NETWORK-PACKET-P
 (184 18 (:DEFINITION MEMBER-EQUAL))
 (118 14 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (98 91 (:REWRITE DEFAULT-CAR))
 (76 76 (:REWRITE DEFAULT-CDR))
 (36 36 (:REWRITE SUBSETP-MEMBER . 2))
 (36 36 (:REWRITE SUBSETP-MEMBER . 1))
 (26 13 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (26 13 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (26 13 (:REWRITE TAG-WHEN-MESSAGE-P))
 (26 13 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (13 13 (:TYPE-PRESCRIPTION BOOLEANP-OF-SERVER-STATE-P))
 (13 13 (:TYPE-PRESCRIPTION BOOLEANP-OF-MESSAGE-P))
 (13 13 (:TYPE-PRESCRIPTION BOOLEANP-OF-CLIENT-STATE-P))
 (12 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (8 1 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE SET::IN-SET))
 )
(RETRIEVE-NETWORK-MESSAGE-RETURNS-NETWORK-STATE-P
 (42 2 (:REWRITE SUBSETP-OF-CONS))
 (15 1 (:DEFINITION MEMBER-EQUAL))
 (14 14 (:REWRITE SUBSETP-TRANS2))
 (14 14 (:REWRITE SUBSETP-TRANS))
 (11 11 (:REWRITE DEFAULT-CAR))
 (8 8 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (8 8 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (7 7 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 )
(MAKE-SQUARE-REQUEST
 (10 1 (:REWRITE MESSAGE-P-WHEN-WRONG-TAG))
 (4 1 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (4 1 (:REWRITE TAG-WHEN-MESSAGE-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-NETWORK-PACKET-P))
 (1 1 (:REWRITE TAG-OF-MESSAGE))
 )
(MAKE-SQUARE-REQUEST-OUTPUT-LEMMA
 (6 1 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (4 1 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (2 2 (:REWRITE NETWORK-PACKET-P-WHEN-MEMBER-EQUAL-OF-NETWORK-STATE-P))
 (1 1 (:REWRITE TAG-OF-NETWORK-PACKET))
 )
(PRINT-STATES)
(CLIENT-STEP1)
(CLIENT-STEP1-OUTPUT-LEMMA-1
 (10 2 (:REWRITE CLIENT-STATE-P-WHEN-WRONG-TAG))
 (2 2 (:REWRITE NETWORK-STATE-P-WHEN-SUBSETP-EQUAL))
 (2 1 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (2 1 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (2 1 (:REWRITE TAG-WHEN-MESSAGE-P))
 (2 1 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-SERVER-STATE-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-NETWORK-PACKET-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-MESSAGE-P))
 (1 1 (:REWRITE NETWORK-STATE-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(CLIENT-STEP1-OUTPUT-LEMMA-2
 (24 2 (:DEFINITION MEMBER-EQUAL))
 (21 1 (:REWRITE SUBSETP-OF-CONS))
 (18 2 (:REWRITE NETWORK-PACKET-P-WHEN-MEMBER-EQUAL-OF-NETWORK-STATE-P))
 (11 11 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (9 1 (:REWRITE CLIENT-STATE-P-WHEN-WRONG-TAG))
 (6 2 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (6 1 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP-OF-NETWORK-PACKET-P))
 (2 2 (:REWRITE NETWORK-STATE-P-WHEN-NOT-CONSP))
 (2 1 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (2 1 (:REWRITE TAG-WHEN-MESSAGE-P))
 (2 1 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-SERVER-STATE-P))
 (1 1 (:REWRITE TAG-OF-NETWORK-PACKET))
 )
(MAKE-SQUARE-RESPONSE
 (10 1 (:REWRITE MESSAGE-P-WHEN-WRONG-TAG))
 (4 1 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (4 1 (:REWRITE TAG-WHEN-MESSAGE-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-NETWORK-PACKET-P))
 (1 1 (:REWRITE TAG-OF-MESSAGE))
 )
(MAKE-SQUARE-RESPONSE-OUTPUT-LEMMA
 (6 1 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (4 1 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (2 2 (:REWRITE NETWORK-PACKET-P-WHEN-MEMBER-EQUAL-OF-NETWORK-STATE-P))
 (1 1 (:REWRITE TAG-OF-NETWORK-PACKET))
 )
(LEMMA-ADDED-IN-TYPE-ALIST-REORDERING
 (216 16 (:DEFINITION MEMBER-EQUAL))
 (129 13 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (106 94 (:REWRITE DEFAULT-CAR))
 (73 73 (:REWRITE DEFAULT-CDR))
 (51 3 (:REWRITE NETWORK-PACKET-P-OF-CAR-WHEN-NETWORK-STATE-P))
 (32 32 (:REWRITE SUBSETP-MEMBER . 2))
 (32 32 (:REWRITE SUBSETP-MEMBER . 1))
 (29 13 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (29 13 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (29 13 (:REWRITE TAG-WHEN-MESSAGE-P))
 (29 13 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (22 11 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (13 13 (:TYPE-PRESCRIPTION BOOLEANP-OF-SERVER-STATE-P))
 (13 13 (:TYPE-PRESCRIPTION BOOLEANP-OF-MESSAGE-P))
 (13 13 (:TYPE-PRESCRIPTION BOOLEANP-OF-CLIENT-STATE-P))
 (12 12 (:REWRITE SUBSETP-TRANS2))
 (12 12 (:REWRITE SUBSETP-TRANS))
 (12 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (11 11 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (8 1 (:DEFINITION TRUE-LISTP))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (2 2 (:REWRITE SET::IN-SET))
 )
(SERVER-STEP1
 (289 30 (:DEFINITION MEMBER-EQUAL))
 (147 16 (:REWRITE RETRIEVE-NETWORK-MESSAGE-RETURNS-NETWORK-PACKET-P))
 (146 18 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (137 17 (:REWRITE SERVER-STATE-P-WHEN-WRONG-TAG))
 (136 136 (:REWRITE DEFAULT-CAR))
 (118 118 (:REWRITE DEFAULT-CDR))
 (68 34 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (68 34 (:REWRITE TAG-WHEN-MESSAGE-P))
 (64 32 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (59 59 (:REWRITE SUBSETP-MEMBER . 2))
 (59 59 (:REWRITE SUBSETP-MEMBER . 1))
 (32 32 (:TYPE-PRESCRIPTION BOOLEANP-OF-CLIENT-STATE-P))
 (9 1 (:REWRITE MESSAGE-P-WHEN-WRONG-TAG))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (2 1 (:TYPE-PRESCRIPTION INTEGERP-OF-MESSAGE->PAYLOAD))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(SERVER-STEP1-OUTPUT-LEMMA-1
 (65 7 (:REWRITE SERVER-STATE-P-WHEN-WRONG-TAG))
 (45 9 (:DEFINITION RETRIEVE-NETWORK-MESSAGE))
 (28 4 (:REWRITE NETWORK-PACKET-P-WHEN-MEMBER-EQUAL-OF-NETWORK-STATE-P))
 (21 21 (:REWRITE DEFAULT-CAR))
 (20 20 (:REWRITE DEFAULT-CDR))
 (18 2 (:REWRITE RETRIEVE-NETWORK-MESSAGE-RETURNS-NETWORK-PACKET-P))
 (16 6 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (16 6 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (16 6 (:REWRITE TAG-WHEN-MESSAGE-P))
 (16 2 (:DEFINITION MEMBER-EQUAL))
 (10 10 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (8 8 (:REWRITE NETWORK-STATE-P-WHEN-SUBSETP-EQUAL))
 (8 4 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (6 3 (:REWRITE DEFAULT-+-2))
 (6 1 (:DEFINITION EXPT))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP-OF-CLIENT-STATE-P))
 (4 4 (:REWRITE SUBSETP-MEMBER . 2))
 (4 4 (:REWRITE SUBSETP-MEMBER . 1))
 (4 4 (:REWRITE NETWORK-STATE-P-WHEN-NOT-CONSP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE DEFAULT-*-2))
 (2 2 (:TYPE-PRESCRIPTION ID-P))
 (2 2 (:REWRITE TAG-OF-SERVER-STATE))
 (1 1 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (1 1 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (1 1 (:REWRITE DEFAULT-*-1))
 (1 1 (:DEFINITION FIX))
 )
(SERVER-STEP1-OUTPUT-LEMMA-2
 (120 13 (:DEFINITION MEMBER-EQUAL))
 (84 84 (:REWRITE DEFAULT-CAR))
 (82 10 (:REWRITE SERVER-STATE-P-WHEN-WRONG-TAG))
 (79 9 (:REWRITE RETRIEVE-NETWORK-MESSAGE-RETURNS-NETWORK-PACKET-P))
 (75 75 (:REWRITE DEFAULT-CDR))
 (43 6 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (32 15 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (28 14 (:REWRITE TAG-WHEN-MESSAGE-P))
 (26 26 (:REWRITE SUBSETP-MEMBER . 2))
 (26 26 (:REWRITE SUBSETP-MEMBER . 1))
 (26 13 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (22 1 (:REWRITE SUBSETP-OF-CONS))
 (13 13 (:TYPE-PRESCRIPTION BOOLEANP-OF-CLIENT-STATE-P))
 (12 6 (:REWRITE DEFAULT-*-2))
 (6 6 (:REWRITE DEFAULT-*-1))
 (4 4 (:REWRITE SUBSETP-TRANS2))
 (4 4 (:REWRITE SUBSETP-TRANS))
 (3 3 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:TYPE-PRESCRIPTION INTEGERP-OF-SERVER-STATE->REQUESTS-SERVED))
 (1 1 (:REWRITE TAG-OF-NETWORK-PACKET))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(CLIENT-STEP2
 (281 29 (:DEFINITION MEMBER-EQUAL))
 (146 18 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (138 15 (:REWRITE RETRIEVE-NETWORK-MESSAGE-RETURNS-NETWORK-PACKET-P))
 (137 17 (:REWRITE CLIENT-STATE-P-WHEN-WRONG-TAG))
 (135 135 (:REWRITE DEFAULT-CAR))
 (117 117 (:REWRITE DEFAULT-CDR))
 (68 34 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (68 34 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (68 34 (:REWRITE TAG-WHEN-MESSAGE-P))
 (57 57 (:REWRITE SUBSETP-MEMBER . 2))
 (57 57 (:REWRITE SUBSETP-MEMBER . 1))
 (34 34 (:TYPE-PRESCRIPTION BOOLEANP-OF-SERVER-STATE-P))
 (15 15 (:TYPE-PRESCRIPTION ID-P))
 (9 1 (:REWRITE MESSAGE-P-WHEN-WRONG-TAG))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 )
(CLIENT-STEP2-OUTPUT-LEMMA-1
 (100 11 (:REWRITE CLIENT-STATE-P-WHEN-WRONG-TAG))
 (72 8 (:DEFINITION MEMBER-EQUAL))
 (52 6 (:REWRITE RETRIEVE-NETWORK-MESSAGE-RETURNS-NETWORK-PACKET-P))
 (51 51 (:REWRITE DEFAULT-CAR))
 (41 41 (:REWRITE DEFAULT-CDR))
 (37 5 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (32 15 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (32 15 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (32 15 (:REWRITE TAG-WHEN-MESSAGE-P))
 (16 16 (:REWRITE SUBSETP-MEMBER . 2))
 (16 16 (:REWRITE SUBSETP-MEMBER . 1))
 (15 15 (:TYPE-PRESCRIPTION BOOLEANP-OF-SERVER-STATE-P))
 (6 6 (:TYPE-PRESCRIPTION ID-P))
 (1 1 (:REWRITE TAG-OF-CLIENT-STATE))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 )
(CLIENT-STEP2-OUTPUT-LEMMA-2
 (10 4 (:REWRITE NETWORK-STATE-P-WHEN-SUBSETP-EQUAL))
 (9 1 (:REWRITE CLIENT-STATE-P-WHEN-WRONG-TAG))
 (5 1 (:DEFINITION RETRIEVE-NETWORK-MESSAGE))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (2 2 (:REWRITE NETWORK-STATE-P-WHEN-NOT-CONSP))
 (2 1 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (2 1 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (2 1 (:REWRITE TAG-WHEN-MESSAGE-P))
 (2 1 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-SERVER-STATE-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-NETWORK-PACKET-P))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP-OF-MESSAGE-P))
 (1 1 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (1 1 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 )
(HONEST-SQUARE-IS-GOOD-CONCRETE
 (3 3 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (3 3 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 )
(HONEST-SQUARE-IS-GOOD-SYMBOLIC-SIMULATION
 (28 28 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (28 28 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (18 2 (:DEFINITION EXPT))
 (9 1 (:REWRITE SERVER-STATE-P-WHEN-WRONG-TAG))
 (9 1 (:REWRITE CLIENT-STATE-P-WHEN-WRONG-TAG))
 (8 2 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 2 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (4 2 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (4 2 (:REWRITE TAG-WHEN-MESSAGE-P))
 (4 2 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (4 2 (:REWRITE DEFAULT-*-1))
 (4 2 (:DEFINITION FIX))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP-OF-NETWORK-PACKET-P))
 (2 2 (:TYPE-PRESCRIPTION BOOLEANP-OF-MESSAGE-P))
 (2 2 (:REWRITE NETWORK-STATE-P-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:TYPE-PRESCRIPTION INTEGERP-OF-SERVER-STATE->REQUESTS-SERVED))
 (1 1 (:REWRITE NETWORK-STATE-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(MAN-IN-THE-MIDDLE-SPECIFIC-ATTACK
 (289 30 (:DEFINITION MEMBER-EQUAL))
 (147 16 (:REWRITE RETRIEVE-NETWORK-MESSAGE-RETURNS-NETWORK-PACKET-P))
 (146 18 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (140 140 (:REWRITE DEFAULT-CAR))
 (122 122 (:REWRITE DEFAULT-CDR))
 (59 59 (:REWRITE SUBSETP-MEMBER . 2))
 (59 59 (:REWRITE SUBSETP-MEMBER . 1))
 (34 17 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (34 17 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (34 17 (:REWRITE TAG-WHEN-MESSAGE-P))
 (34 17 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (17 17 (:TYPE-PRESCRIPTION BOOLEANP-OF-SERVER-STATE-P))
 (17 17 (:TYPE-PRESCRIPTION BOOLEANP-OF-CLIENT-STATE-P))
 (16 16 (:TYPE-PRESCRIPTION ID-P))
 (14 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (14 1 (:REWRITE DEFAULT-+-2))
 (9 1 (:REWRITE MESSAGE-P-WHEN-WRONG-TAG))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(MAN-IN-THE-MIDDLE-SPECIFIC-ATTACK-OUTPUT-LEMMA
 (96 10 (:DEFINITION MEMBER-EQUAL))
 (54 54 (:REWRITE DEFAULT-CAR))
 (52 6 (:REWRITE RETRIEVE-NETWORK-MESSAGE-RETURNS-NETWORK-PACKET-P))
 (45 45 (:REWRITE DEFAULT-CDR))
 (43 6 (:REWRITE NETWORK-PACKET-P-WHEN-WRONG-TAG))
 (22 1 (:REWRITE SUBSETP-OF-CONS))
 (20 20 (:REWRITE SUBSETP-MEMBER . 2))
 (20 20 (:REWRITE SUBSETP-MEMBER . 1))
 (17 2 (:REWRITE DEFAULT-+-2))
 (12 5 (:REWRITE TAG-WHEN-NETWORK-PACKET-P))
 (8 4 (:REWRITE TAG-WHEN-SERVER-STATE-P))
 (8 4 (:REWRITE TAG-WHEN-MESSAGE-P))
 (8 4 (:REWRITE TAG-WHEN-CLIENT-STATE-P))
 (7 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP-OF-SERVER-STATE-P))
 (4 4 (:TYPE-PRESCRIPTION BOOLEANP-OF-CLIENT-STATE-P))
 (4 4 (:REWRITE SUBSETP-TRANS2))
 (4 4 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (2 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE TAG-OF-NETWORK-PACKET))
 )
(ATTACK1)
(ATTACK2)
