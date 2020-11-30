(UBYTE2-LISTP)
(STD::DEFLIST-LOCAL-BOOLEANP-ELEMENT-THM)
(STD::DEFLIST-LOCAL-ELEMENTP-OF-NIL-THM)
(UBYTE2-LISTP-OF-CONS)
(UBYTE2-LISTP-OF-CDR-WHEN-UBYTE2-LISTP)
(UBYTE2-LISTP-WHEN-NOT-CONSP)
(UBYTE2P-OF-CAR-WHEN-UBYTE2-LISTP)
(TRUE-LISTP-WHEN-UBYTE2-LISTP)
(UBYTE2-LISTP-OF-LIST-FIX)
(UBYTE2-LISTP-OF-SFIX)
(UBYTE2-LISTP-OF-INSERT)
(UBYTE2-LISTP-OF-DELETE)
(UBYTE2-LISTP-OF-MERGESORT)
(UBYTE2-LISTP-OF-UNION)
(UBYTE2-LISTP-OF-INTERSECT-1)
(UBYTE2-LISTP-OF-INTERSECT-2)
(UBYTE2-LISTP-OF-DIFFERENCE)
(UBYTE2-LISTP-OF-DUPLICATED-MEMBERS)
(UBYTE2-LISTP-OF-REV)
(UBYTE2-LISTP-OF-APPEND)
(UBYTE2-LISTP-OF-RCONS)
(UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP)
(UBYTE2-LISTP-WHEN-SUBSETP-EQUAL)
(UBYTE2-LISTP-OF-SET-DIFFERENCE-EQUAL)
(UBYTE2-LISTP-OF-INTERSECTION-EQUAL-1)
(UBYTE2-LISTP-OF-INTERSECTION-EQUAL-2)
(UBYTE2-LISTP-OF-UNION-EQUAL)
(UBYTE2-LISTP-OF-TAKE)
(UBYTE2-LISTP-OF-REPEAT)
(UBYTE2P-OF-NTH-WHEN-UBYTE2-LISTP)
(UBYTE2-LISTP-OF-UPDATE-NTH)
(UBYTE2-LISTP-OF-BUTLAST)
(UBYTE2-LISTP-OF-NTHCDR)
(UBYTE2-LISTP-OF-LAST)
(UBYTE2-LISTP-OF-REMOVE)
(UBYTE2-LISTP-OF-REVAPPEND)
(UBYTE2-LIST-FIX$INLINE)
(UBYTE2-LISTP-OF-UBYTE2-LIST-FIX
     (30 1 (:REWRITE UBYTE2-FIX-WHEN-UBYTE2P))
     (22 2
         (:REWRITE UBYTE2P-OF-CAR-WHEN-UBYTE2-LISTP))
     (18 10
         (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
     (15 1 (:DEFINITION UBYTE2-LISTP))
     (12 6
         (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
     (9 5
        (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP))
     (8 8 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (4 4 (:TYPE-PRESCRIPTION UBYTE2P))
     (4 4 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (2 2
        (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS))
     (2 1
        (:REWRITE UBYTE2-LISTP-OF-CDR-WHEN-UBYTE2-LISTP)))
(UBYTE2-LIST-FIX-WHEN-UBYTE2-LISTP
     (32 4
         (:REWRITE UBYTE2-LISTP-OF-CDR-WHEN-UBYTE2-LISTP))
     (28 24
         (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
     (13 3
         (:REWRITE UBYTE2P-OF-CAR-WHEN-UBYTE2-LISTP))
     (9 6
        (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
     (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
     (2 2 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
     (1 1
        (:REWRITE FTY::OPEN-MEMBER-EQUAL-ON-LIST-OF-TAGS)))
(UBYTE2-LIST-FIX$INLINE
     (8 8
        (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
     (6 1
        (:REWRITE UBYTE2P-OF-CAR-WHEN-UBYTE2-LISTP))
     (6 1
        (:REWRITE UBYTE2-LISTP-OF-CDR-WHEN-UBYTE2-LISTP))
     (4 4
        (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP))
     (2 2
        (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP)))
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
     (2 2
        (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
     (1 1
        (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP)))
(UBYTE2-LIST-EQUIV$INLINE)
(UBYTE2-LIST-EQUIV-IS-AN-EQUIVALENCE)
(UBYTE2-LIST-EQUIV-IMPLIES-EQUAL-UBYTE2-LIST-FIX-1)
(UBYTE2-LIST-FIX-UNDER-UBYTE2-LIST-EQUIV)
(EQUAL-OF-UBYTE2-LIST-FIX-1-FORWARD-TO-UBYTE2-LIST-EQUIV)
(EQUAL-OF-UBYTE2-LIST-FIX-2-FORWARD-TO-UBYTE2-LIST-EQUIV)
(UBYTE2-LIST-EQUIV-OF-UBYTE2-LIST-FIX-1-FORWARD)
(UBYTE2-LIST-EQUIV-OF-UBYTE2-LIST-FIX-2-FORWARD)
(CAR-OF-UBYTE2-LIST-FIX-X-UNDER-UBYTE2-EQUIV
     (33 3 (:REWRITE UBYTE2-FIX-WHEN-UBYTE2P))
     (18 3
         (:REWRITE UBYTE2P-OF-CAR-WHEN-UBYTE2-LISTP))
     (18 2
         (:REWRITE UBYTE2-LIST-FIX-WHEN-UBYTE2-LISTP))
     (12 12 (:TYPE-PRESCRIPTION UBYTE2-LISTP))
     (12 12
         (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
     (6 6 (:TYPE-PRESCRIPTION UBYTE2P))
     (6 6
        (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
     (6 6
        (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP))
     (6 1
        (:REWRITE UBYTE2-LISTP-OF-CDR-WHEN-UBYTE2-LISTP))
     (3 3
        (:TYPE-PRESCRIPTION UBYTE2-LIST-FIX$INLINE)))
(CAR-OF-UBYTE2-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-EQUIV)
(CAR-UBYTE2-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-UBYTE2-EQUIV)
(CDR-OF-UBYTE2-LIST-FIX-X-UNDER-UBYTE2-LIST-EQUIV
     (41 3
         (:REWRITE UBYTE2-LISTP-OF-CDR-WHEN-UBYTE2-LISTP))
     (22 2 (:REWRITE UBYTE2-FIX-WHEN-UBYTE2P))
     (20 20
         (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
     (12 2
         (:REWRITE UBYTE2P-OF-CAR-WHEN-UBYTE2-LISTP))
     (4 4 (:TYPE-PRESCRIPTION UBYTE2P))
     (4 4
        (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP)))
(CDR-OF-UBYTE2-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV)
(CDR-UBYTE2-LIST-EQUIV-CONGRUENCE-ON-X-UNDER-UBYTE2-LIST-EQUIV)
(CONS-OF-UBYTE2-FIX-X-UNDER-UBYTE2-LIST-EQUIV
  (34 4
      (:REWRITE UBYTE2-LIST-FIX-WHEN-UBYTE2-LISTP))
  (17 2 (:REWRITE UBYTE2-LISTP-OF-CONS))
  (10 10
      (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
  (8 8
     (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
  (6 6 (:TYPE-PRESCRIPTION UBYTE2-LISTP))
  (5 5
     (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP))
  (2 2
     (:REWRITE
          CDR-OF-UBYTE2-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV)))
(CONS-OF-UBYTE2-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV)
(CONS-UBYTE2-EQUIV-CONGRUENCE-ON-X-UNDER-UBYTE2-LIST-EQUIV)
(CONS-OF-UBYTE2-LIST-FIX-Y-UNDER-UBYTE2-LIST-EQUIV
  (20 2 (:REWRITE UBYTE2-LISTP-OF-CONS))
  (8 8 (:TYPE-PRESCRIPTION UBYTE2P))
  (8 8
     (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
  (8 8
     (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
  (6 2 (:REWRITE UBYTE2-FIX-WHEN-UBYTE2P))
  (5 4
     (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP))
  (2 2
     (:REWRITE CONS-OF-UBYTE2-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV))
  (2 2
     (:REWRITE
          CDR-OF-UBYTE2-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV)))
(CONS-OF-UBYTE2-LIST-FIX-Y-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV)
(CONS-UBYTE2-LIST-EQUIV-CONGRUENCE-ON-Y-UNDER-UBYTE2-LIST-EQUIV)
(CONSP-OF-UBYTE2-LIST-FIX
  (18 2
      (:REWRITE UBYTE2-LIST-FIX-WHEN-UBYTE2-LISTP))
  (11 1 (:REWRITE UBYTE2-FIX-WHEN-UBYTE2P))
  (8 8 (:TYPE-PRESCRIPTION UBYTE2-LISTP))
  (8 8
     (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
  (6 1
     (:REWRITE UBYTE2P-OF-CAR-WHEN-UBYTE2-LISTP))
  (6 1
     (:REWRITE UBYTE2-LISTP-OF-CDR-WHEN-UBYTE2-LISTP))
  (4 4
     (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP))
  (2 2 (:TYPE-PRESCRIPTION UBYTE2P))
  (2 2
     (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
  (1 1
     (:REWRITE
          CDR-OF-UBYTE2-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV)))
(UBYTE2-LIST-FIX-UNDER-IFF
  (18 2
      (:REWRITE UBYTE2-LIST-FIX-WHEN-UBYTE2-LISTP))
  (11 1 (:REWRITE UBYTE2-FIX-WHEN-UBYTE2P))
  (8 8 (:TYPE-PRESCRIPTION UBYTE2-LISTP))
  (8 8
     (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
  (6 1
     (:REWRITE UBYTE2P-OF-CAR-WHEN-UBYTE2-LISTP))
  (6 1
     (:REWRITE UBYTE2-LISTP-OF-CDR-WHEN-UBYTE2-LISTP))
  (4 4
     (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP))
  (2 2 (:TYPE-PRESCRIPTION UBYTE2P))
  (2 2
     (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
  (1 1
     (:REWRITE
          CDR-OF-UBYTE2-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV)))
(UBYTE2-LIST-FIX-OF-CONS
  (21 3
      (:REWRITE UBYTE2-LIST-FIX-WHEN-UBYTE2-LISTP))
  (9 1 (:REWRITE UBYTE2-LISTP-OF-CONS))
  (6 6
     (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
  (6 2 (:REWRITE UBYTE2-FIX-WHEN-UBYTE2P))
  (4 4 (:TYPE-PRESCRIPTION UBYTE2P))
  (4 4 (:TYPE-PRESCRIPTION UBYTE2-LISTP))
  (4 4
     (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
  (3 3
     (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP))
  (1 1
     (:REWRITE
          CONS-OF-UBYTE2-LIST-FIX-Y-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV))
  (1 1
     (:REWRITE CONS-OF-UBYTE2-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV))
  (1 1
     (:REWRITE
          CDR-OF-UBYTE2-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV)))
(LEN-OF-UBYTE2-LIST-FIX
   (35 4
       (:REWRITE UBYTE2-LIST-FIX-WHEN-UBYTE2-LISTP))
   (14 14
       (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
   (13 13 (:TYPE-PRESCRIPTION UBYTE2-LISTP))
   (12 2
       (:REWRITE UBYTE2-LISTP-OF-CDR-WHEN-UBYTE2-LISTP))
   (11 1 (:REWRITE UBYTE2-FIX-WHEN-UBYTE2P))
   (7 7
      (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP))
   (6 1
      (:REWRITE UBYTE2P-OF-CAR-WHEN-UBYTE2-LISTP))
   (2 2 (:TYPE-PRESCRIPTION UBYTE2P))
   (2 2
      (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
   (2 2
      (:REWRITE
           CDR-OF-UBYTE2-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV))
   (1 1 (:REWRITE FTY::EQUAL-OF-LEN)))
(UBYTE2-LIST-FIX-OF-APPEND
  (114 10
       (:REWRITE UBYTE2-LIST-FIX-WHEN-UBYTE2-LISTP))
  (58 2 (:REWRITE UBYTE2-LISTP-OF-APPEND))
  (40 36
      (:REWRITE UBYTE2-LISTP-WHEN-SUBSETP-EQUAL))
  (29 29 (:TYPE-PRESCRIPTION UBYTE2-LISTP))
  (24 2 (:REWRITE UBYTE2-LISTP-OF-LIST-FIX))
  (22 16
      (:REWRITE UBYTE2-LISTP-WHEN-NOT-CONSP))
  (14 4
      (:REWRITE UBYTE2-LISTP-OF-CDR-WHEN-UBYTE2-LISTP))
  (12 12 (:TYPE-PRESCRIPTION TRUE-LIST-FIX))
  (12 2 (:REWRITE UBYTE2-FIX-WHEN-UBYTE2P))
  (6 1
     (:REWRITE UBYTE2P-OF-CAR-WHEN-UBYTE2-LISTP))
  (4 4 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
  (2 2 (:TYPE-PRESCRIPTION UBYTE2P))
  (2 2
     (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
  (2 2
     (:REWRITE
          CDR-OF-UBYTE2-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV))
  (1 1
     (:REWRITE
          CONS-OF-UBYTE2-LIST-FIX-Y-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV))
  (1 1
     (:REWRITE CONS-OF-UBYTE2-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV))
  (1 1
     (:REWRITE CAR-OF-UBYTE2-LIST-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-EQUIV)))
(UBYTE2-LIST-FIX-OF-REPEAT
 (20 2
     (:REWRITE UBYTE2-LIST-FIX-WHEN-UBYTE2-LISTP))
 (16 4 (:REWRITE UBYTE2-FIX-WHEN-UBYTE2P))
 (12 2 (:REWRITE UBYTE2-LISTP-OF-REPEAT))
 (10 10 (:TYPE-PRESCRIPTION UBYTE2P))
 (10 10
     (:REWRITE UBYTE2P-WHEN-MEMBER-EQUAL-OF-UBYTE2-LISTP))
 (2 2 (:TYPE-PRESCRIPTION UBYTE2-LISTP))
 (1 1
    (:REWRITE
         CONS-OF-UBYTE2-LIST-FIX-Y-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV))
 (1 1
    (:REWRITE CONS-OF-UBYTE2-FIX-X-NORMALIZE-CONST-UNDER-UBYTE2-LIST-EQUIV)))
(UBYTE2-LISTP-FORWARD-UNSIGNED-BYTE-LISTP)
(UBYTE2-LISTP-REWRITE-UNSIGNED-BYTE-LISTP)
(UNSIGNED-BYTE-LISTP-REWRITE-UBYTE2-LISTP)
(TRUE-LISTP-WHEN-UBYTE2-LISTP-REWRITE (2 2 (:DEFINITION TRUE-LISTP)))
(UBYTE2-LIST-FIX-OF-TAKE)
(UBYTE2-LIST-FIX-OF-RCONS)
