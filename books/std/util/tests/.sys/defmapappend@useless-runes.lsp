(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(STD::MY-NAT-LISTP)
(STD::MY-NAT-LISTP-OF-CONS)
(STD::MY-NAT-LISTP-OF-CDR-WHEN-MY-NAT-LISTP)
(STD::MY-NAT-LISTP-WHEN-NOT-CONSP)
(STD::NATP-OF-CAR-WHEN-MY-NAT-LISTP)
(STD::MY-NAT-LISTP-OF-APPEND)
(STD::MY-NAT-LISTP-OF-LIST-FIX)
(STD::MY-NAT-LISTP-OF-SFIX)
(STD::MY-NAT-LISTP-OF-INSERT)
(STD::MY-NAT-LISTP-OF-DELETE)
(STD::MY-NAT-LISTP-OF-MERGESORT)
(STD::MY-NAT-LISTP-OF-UNION)
(STD::MY-NAT-LISTP-OF-INTERSECT-1)
(STD::MY-NAT-LISTP-OF-INTERSECT-2)
(STD::MY-NAT-LISTP-OF-DIFFERENCE)
(STD::MY-NAT-LISTP-OF-DUPLICATED-MEMBERS)
(STD::MY-NAT-LISTP-OF-REV)
(STD::MY-NAT-LISTP-OF-RCONS)
(STD::NATP-WHEN-MEMBER-EQUAL-OF-MY-NAT-LISTP)
(STD::MY-NAT-LISTP-WHEN-SUBSETP-EQUAL)
(STD::MY-NAT-LISTP-SET-EQUIV-CONGRUENCE)
(STD::MY-NAT-LISTP-OF-SET-DIFFERENCE-EQUAL)
(STD::MY-NAT-LISTP-OF-INTERSECTION-EQUAL-1)
(STD::MY-NAT-LISTP-OF-INTERSECTION-EQUAL-2)
(STD::MY-NAT-LISTP-OF-UNION-EQUAL)
(STD::MY-NAT-LISTP-OF-TAKE)
(STD::MY-NAT-LISTP-OF-REPEAT)
(STD::NATP-OF-NTH-WHEN-MY-NAT-LISTP)
(STD::MY-NAT-LISTP-OF-UPDATE-NTH)
(STD::MY-NAT-LISTP-OF-BUTLAST)
(STD::MY-NAT-LISTP-OF-NTHCDR)
(STD::MY-NAT-LISTP-OF-LAST)
(STD::MY-NAT-LISTP-OF-REMOVE)
(STD::MY-NAT-LISTP-OF-REVAPPEND)
(STD::NATS)
(STD::MY-NAT-LISTP-OF-NATS
 (21 1 (:REWRITE SUBSETP-OF-CONS))
 (14 14 (:TYPE-PRESCRIPTION STD::NATS))
 (14 4 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 (12 1 (:DEFINITION MEMBER-EQUAL))
 (6 6 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (4 4 (:REWRITE ZP-OPEN))
 (3 3 (:REWRITE SUBSETP-TRANS2))
 (3 3 (:REWRITE SUBSETP-TRANS))
 (2 2 (:REWRITE SUBSETP-MEMBER . 2))
 (2 2 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(STD::MAP-NATS-EXEC)
(STD::MAP-NATS-NREV)
(STD::MAP-NATS)
(STD::MAP-NATS-NIL-PRESERVINGP-LEMMA)
(STD::MAP-NATS-NREV-REMOVAL
 (64 5 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (36 6 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (36 3 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
 (33 3 (:DEFINITION TRUE-LISTP))
 (16 16 (:REWRITE DEFAULT-CDR))
 (15 15 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (15 3 (:DEFINITION LEN))
 (12 12 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (12 6 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (10 10 (:REWRITE DEFAULT-CAR))
 (6 6 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (6 6 (:REWRITE SET::IN-SET))
 (6 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (3 3 (:REWRITE DEFAULT-+-1))
 (2 2 (:TYPE-PRESCRIPTION TYPE-OF-RCONS))
 )
(STD::MAP-NATS-EXEC-REMOVAL
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 )
(STD::MAP-NATS-OF-TAKE)
(STD::SET-EQUIV-CONGRUENCE-OVER-MAP-NATS)
(STD::SUBSETP-OF-MAP-NATS-WHEN-SUBSETP)
(STD::MEMBER-OF-NATS-IN-MAP-NATS)
(STD::MAP-NATS-OF-REV)
(STD::MAP-NATS-OF-LIST-FIX)
(STD::MAP-NATS-OF-APPEND)
(STD::CDR-OF-MAP-NATS)
(STD::CAR-OF-MAP-NATS)
(STD::MAP-NATS-UNDER-IFF)
(STD::CONSP-OF-MAP-NATS)
(STD::LEN-OF-MAP-NATS)
(STD::TRUE-LISTP-OF-MAP-NATS)
(STD::MAP-NATS-WHEN-NOT-CONSP)
(STD::MAP-NATS-OF-CONS)
(STD::MAP-NATS-NREV
 (24 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (16 2 (:DEFINITION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:REWRITE SET::IN-SET))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(STD::MAP-NATS)
(STD::MAP-NATS-EXEC
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(STD::APPEND-NATS-EXEC
 (6 6 (:TYPE-PRESCRIPTION REVAPPEND))
 )
(STD::APPEND-NATS)
(STD::SET-EQUIV-CONGRUENCE-OVER-APPEND-NATS
 (30 5 (:DEFINITION BINARY-APPEND))
 (25 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
(STD::SUBSETP-OF-APPEND-NATS-WHEN-SUBSETP)
(STD::MEMBER-IN-APPEND-NATS)
(STD::APPEND-NATS-EXEC-REMOVAL
 (85 5 (:DEFINITION BINARY-APPEND))
 (50 50 (:TYPE-PRESCRIPTION REV))
 (50 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (35 35 (:TYPE-PRESCRIPTION STD::NATS))
 (35 20 (:REWRITE CONSP-OF-REV))
 (25 10 (:REWRITE DEFAULT-CDR))
 (25 10 (:REWRITE DEFAULT-CAR))
 (20 5 (:REWRITE REV-WHEN-NOT-CONSP))
 )
(STD::APPEND-NATS-OF-LIST-FIX)
(STD::APPEND-NATS-OF-APPEND)
(STD::APPEND-NATS-WHEN-NOT-CONSP)
(STD::APPEND-NATS-OF-CONS)
(STD::APPEND-NATS-EXEC
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(STD::APPEND-NATS
 (30 5 (:DEFINITION BINARY-APPEND))
 (25 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (13 1 (:REWRITE REV-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE STD::APPEND-NATS-WHEN-NOT-CONSP))
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 )
(STD::M0-EXEC
 (6 6 (:TYPE-PRESCRIPTION REVAPPEND))
 )
(STD::M0)
(STD::SET-EQUIV-CONGRUENCE-OVER-M0
 (30 5 (:DEFINITION BINARY-APPEND))
 (25 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
(STD::SUBSETP-OF-M0-WHEN-SUBSETP)
(STD::MEMBER-IN-M0)
(STD::M0-EXEC-REMOVAL
 (85 5 (:DEFINITION BINARY-APPEND))
 (50 50 (:TYPE-PRESCRIPTION REV))
 (50 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (35 35 (:TYPE-PRESCRIPTION STD::NATS))
 (35 20 (:REWRITE CONSP-OF-REV))
 (25 10 (:REWRITE DEFAULT-CDR))
 (25 10 (:REWRITE DEFAULT-CAR))
 (20 5 (:REWRITE REV-WHEN-NOT-CONSP))
 )
(STD::M0-OF-LIST-FIX)
(STD::M0-OF-APPEND)
(STD::M0-WHEN-NOT-CONSP)
(STD::M0-OF-CONS)
(STD::M0-EXEC
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(STD::M0
 (30 5 (:DEFINITION BINARY-APPEND))
 (25 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (13 1 (:REWRITE REV-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE STD::M0-WHEN-NOT-CONSP))
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 )
(STD::M1-EXEC
 (6 6 (:TYPE-PRESCRIPTION REVAPPEND))
 )
(STD::M1)
(STD::SET-EQUIV-CONGRUENCE-OVER-M1
 (30 5 (:DEFINITION BINARY-APPEND))
 (25 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
(STD::SUBSETP-OF-M1-WHEN-SUBSETP)
(STD::MEMBER-IN-M1)
(STD::M1-EXEC-REMOVAL
 (85 5 (:DEFINITION BINARY-APPEND))
 (50 50 (:TYPE-PRESCRIPTION REV))
 (50 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (35 35 (:TYPE-PRESCRIPTION STD::NATS))
 (35 20 (:REWRITE CONSP-OF-REV))
 (25 10 (:REWRITE DEFAULT-CDR))
 (25 10 (:REWRITE DEFAULT-CAR))
 (20 5 (:REWRITE REV-WHEN-NOT-CONSP))
 )
(STD::M1-OF-LIST-FIX)
(STD::M1-OF-APPEND)
(STD::M1-WHEN-NOT-CONSP)
(STD::M1-OF-CONS)
(STD::M1-EXEC
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(STD::M1
 (30 5 (:DEFINITION BINARY-APPEND))
 (25 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (13 1 (:REWRITE REV-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE STD::M1-WHEN-NOT-CONSP))
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 )
(STD::M2-EXEC
 (6 6 (:TYPE-PRESCRIPTION REVAPPEND))
 )
(STD::M2)
(STD::SET-EQUIV-CONGRUENCE-OVER-M2
 (30 5 (:DEFINITION BINARY-APPEND))
 (25 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
(STD::SUBSETP-OF-M2-WHEN-SUBSETP)
(STD::MEMBER-IN-M2)
(STD::M2-EXEC-REMOVAL
 (85 5 (:DEFINITION BINARY-APPEND))
 (50 50 (:TYPE-PRESCRIPTION REV))
 (50 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (35 35 (:TYPE-PRESCRIPTION STD::NATS))
 (35 20 (:REWRITE CONSP-OF-REV))
 (25 10 (:REWRITE DEFAULT-CDR))
 (25 10 (:REWRITE DEFAULT-CAR))
 (20 5 (:REWRITE REV-WHEN-NOT-CONSP))
 )
(STD::M2-OF-LIST-FIX)
(STD::M2-OF-APPEND)
(STD::M2-WHEN-NOT-CONSP)
(STD::M2-OF-CONS)
(STD::M2-EXEC
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(STD::M2
 (30 5 (:DEFINITION BINARY-APPEND))
 (25 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (13 1 (:REWRITE REV-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE STD::M2-WHEN-NOT-CONSP))
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 )
(STD::M3-EXEC
 (6 6 (:TYPE-PRESCRIPTION REVAPPEND))
 )
(STD::M3)
(STD::SET-EQUIV-CONGRUENCE-OVER-M3
 (30 5 (:DEFINITION BINARY-APPEND))
 (25 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 )
(STD::SUBSETP-OF-M3-WHEN-SUBSETP)
(STD::MEMBER-IN-M3)
(STD::M3-EXEC-REMOVAL
 (85 5 (:DEFINITION BINARY-APPEND))
 (50 50 (:TYPE-PRESCRIPTION REV))
 (50 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (35 35 (:TYPE-PRESCRIPTION STD::NATS))
 (35 20 (:REWRITE CONSP-OF-REV))
 (25 10 (:REWRITE DEFAULT-CDR))
 (25 10 (:REWRITE DEFAULT-CAR))
 (20 5 (:REWRITE REV-WHEN-NOT-CONSP))
 )
(STD::M3-OF-LIST-FIX)
(STD::M3-OF-APPEND)
(STD::M3-WHEN-NOT-CONSP)
(STD::M3-OF-CONS)
(STD::M3-EXEC
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE SUBSETP-TRANS2))
 (1 1 (:REWRITE SUBSETP-TRANS))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(STD::M3
 (30 5 (:DEFINITION BINARY-APPEND))
 (25 10 (:REWRITE APPEND-WHEN-NOT-CONSP))
 (13 1 (:REWRITE REV-WHEN-NOT-CONSP))
 (10 10 (:REWRITE DEFAULT-CDR))
 (10 10 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE STD::M3-WHEN-NOT-CONSP))
 (2 2 (:REWRITE STD::MY-NAT-LISTP-WHEN-SUBSETP-EQUAL))
 (1 1 (:REWRITE STD::MY-NAT-LISTP-WHEN-NOT-CONSP))
 )
