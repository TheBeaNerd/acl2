(ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR
 (451 451 (:REWRITE DEFAULT-CAR))
 (159 159 (:REWRITE DEFAULT-CDR))
 )
(CHANNEL-HEADERP)
(CHANNEL-HEADERP-OF-LIST
 (10 10 (:REWRITE DEFAULT-CDR))
 (6 3 (:REWRITE DEFAULT-+-2))
 (4 4 (:REWRITE DEFAULT-CAR))
 (3 3 (:TYPE-PRESCRIPTION LEN))
 (3 3 (:REWRITE DEFAULT-+-1))
 )
(STRINGP-OF-CADDR-WHEN-CHANNEL-HEADERP)
(INTEGERP-OF-CADDDR-WHEN-CHANNEL-HEADERP)
(TYPED-IO-LISTP-OF-CDR-AND-CADR-OF-CAR)
(TYPED-IO-LISTP-OF-CDR-GEN
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-CAR))
 )
(OPEN-CHANNEL-LISTP-OF-ADD-PAIR-STRONG
 (55 51 (:REWRITE DEFAULT-CAR))
 (43 30 (:REWRITE DEFAULT-CDR))
 (35 7 (:REWRITE SYMBOL<-ASYMMETRIC))
 (18 15 (:REWRITE SYMBOL<-TRANSITIVE))
 (15 15 (:REWRITE SYMBOL<-TRICHOTOMY))
 )
(OPEN-CHANNEL1-OF-CDR-OF-ASSOC-EQUAL
 (1003 16 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (962 28 (:DEFINITION ORDERED-SYMBOL-ALISTP))
 (324 81 (:REWRITE SYMBOL<-TRICHOTOMY))
 (310 310 (:REWRITE DEFAULT-CAR))
 (216 216 (:TYPE-PRESCRIPTION SYMBOL<))
 (187 187 (:REWRITE DEFAULT-CDR))
 (162 27 (:REWRITE SYMBOL<-ASYMMETRIC))
 (130 130 (:TYPE-PRESCRIPTION ORDERED-SYMBOL-ALISTP))
 (81 81 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(ORDERED-SYMBOL-ALISTP-OF-ADD-PAIR
 (776 719 (:REWRITE DEFAULT-CAR))
 (569 478 (:REWRITE SYMBOL<-TRANSITIVE))
 (327 299 (:REWRITE DEFAULT-CDR))
 )
(OPEN-CHANNELS-P-OF-ADD-PAIR-STRONG
 (42 1 (:DEFINITION ORDERED-SYMBOL-ALISTP))
 (19 5 (:REWRITE SYMBOL<-TRICHOTOMY))
 (17 3 (:REWRITE SYMBOL<-ASYMMETRIC))
 (12 12 (:TYPE-PRESCRIPTION SYMBOL<))
 (10 10 (:REWRITE DEFAULT-CAR))
 (6 6 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(OPEN-CHANNEL1-OF-CONS
 (43 43 (:REWRITE DEFAULT-CDR))
 (23 23 (:REWRITE DEFAULT-CAR))
 (16 8 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-+-1))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(CHANNEL-HEADERP-OF-CADR-OF-ASSOC-EQUAL-IFF
 (2060 51 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (1932 54 (:DEFINITION ORDERED-SYMBOL-ALISTP))
 (894 894 (:REWRITE DEFAULT-CAR))
 (712 712 (:REWRITE DEFAULT-CDR))
 (636 159 (:REWRITE SYMBOL<-TRICHOTOMY))
 (424 424 (:TYPE-PRESCRIPTION SYMBOL<))
 (318 53 (:REWRITE SYMBOL<-ASYMMETRIC))
 (312 312 (:TYPE-PRESCRIPTION ORDERED-SYMBOL-ALISTP))
 (159 159 (:REWRITE SYMBOL<-TRANSITIVE))
 (110 55 (:REWRITE DEFAULT-+-2))
 (55 55 (:REWRITE DEFAULT-+-1))
 (3 1 (:DEFINITION CHARACTER-LISTP))
 )
(CHANNEL-HEADERP-OF-CADR-OF-ASSOC-EQUAL-IFF-2
 (182 5 (:DEFINITION ORDERED-SYMBOL-ALISTP))
 (174 8 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (70 20 (:REWRITE SYMBOL<-TRICHOTOMY))
 (69 69 (:REWRITE DEFAULT-CAR))
 (41 7 (:REWRITE SYMBOL<-ASYMMETRIC))
 (35 35 (:REWRITE DEFAULT-CDR))
 (20 20 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(TYPED-IO-LISTP-OF-CDDDR-OF-ASSOC-EQUAL-AND-CADR-OF-CADR-OF-ASSOC-EQUAL
 (13016 148 (:DEFINITION CHARACTER-LISTP))
 (11300 310 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (10430 283 (:DEFINITION ORDERED-SYMBOL-ALISTP))
 (3630 3630 (:REWRITE DEFAULT-CAR))
 (3384 846 (:REWRITE SYMBOL<-TRICHOTOMY))
 (2569 2569 (:REWRITE DEFAULT-CDR))
 (2256 2256 (:TYPE-PRESCRIPTION SYMBOL<))
 (1965 1965 (:TYPE-PRESCRIPTION ORDERED-SYMBOL-ALISTP))
 (1692 282 (:REWRITE SYMBOL<-ASYMMETRIC))
 (846 846 (:REWRITE SYMBOL<-TRANSITIVE))
 (392 392 (:TYPE-PRESCRIPTION CHARACTER-LISTP))
 (124 44 (:REWRITE OPEN-CHANNEL1-OF-CDR-OF-ASSOC-EQUAL))
 (32 32 (:REWRITE DEFAULT-<-2))
 (32 32 (:REWRITE DEFAULT-<-1))
 (16 4 (:REWRITE TYPED-IO-LISTP-OF-CDR-AND-CADR-OF-CAR))
 )
(TYPED-IO-LISTP-OF-CDDDR-OF-ASSOC-EQUAL-AND-CADR-OF-CADR-OF-ASSOC-EQUAL-2
 (112 3 (:DEFINITION ORDERED-SYMBOL-ALISTP))
 (86 2 (:DEFINITION ASSOC-EQUAL))
 (84 4 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (44 12 (:REWRITE SYMBOL<-TRICHOTOMY))
 (40 40 (:REWRITE DEFAULT-CAR))
 (29 5 (:REWRITE SYMBOL<-ASYMMETRIC))
 (25 25 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(EQUAL-OF-ADD-PAIR-SAME
 (694 35 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (597 589 (:REWRITE DEFAULT-CAR))
 (580 195 (:REWRITE SYMBOL<-TRICHOTOMY))
 (479 89 (:REWRITE SYMBOL<-ASYMMETRIC))
 (305 291 (:REWRITE DEFAULT-CDR))
 (192 190 (:REWRITE SYMBOL<-TRANSITIVE))
 (80 2 (:REWRITE ORDERED-SYMBOL-ALISTP-OF-ADD-PAIR))
 (80 2 (:REWRITE ORDERED-SYMBOL-ALISTP-ADD-PAIR))
 (24 2 (:REWRITE OPEN-CHANNEL-LISTP-OF-ADD-PAIR-STRONG))
 )
(TRUE-LIST-OF-CDDR-OF-ASSOC-EQUAL-WHEN-OPEN-CHANNEL-LISTP
 (607 11 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (578 17 (:DEFINITION ORDERED-SYMBOL-ALISTP))
 (461 461 (:REWRITE DEFAULT-CAR))
 (358 358 (:REWRITE DEFAULT-CDR))
 (352 19 (:REWRITE TYPED-IO-LISTP-OF-CDR-GEN))
 (305 19 (:REWRITE TYPED-IO-LISTP-OF-CDR))
 (192 48 (:REWRITE SYMBOL<-TRICHOTOMY))
 (178 11 (:REWRITE TYPED-IO-LISTP-OF-CDR-AND-CADR-OF-CAR))
 (128 128 (:TYPE-PRESCRIPTION SYMBOL<))
 (96 16 (:REWRITE SYMBOL<-ASYMMETRIC))
 (83 83 (:TYPE-PRESCRIPTION ORDERED-SYMBOL-ALISTP))
 (59 59 (:TYPE-PRESCRIPTION OPEN-CHANNEL1))
 (55 11 (:DEFINITION LEN))
 (51 21 (:DEFINITION TRUE-LISTP))
 (48 48 (:REWRITE SYMBOL<-TRANSITIVE))
 (30 30 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (22 11 (:REWRITE DEFAULT-+-2))
 (11 11 (:REWRITE DEFAULT-+-1))
 )
(NAT-LISTP-OF-CDDR-OF-ASSOC-EQUAL-WHEN-OPEN-CHANNEL-LISTP
 (8131 88 (:REWRITE TYPED-IO-LISTP-OF-CDR-GEN))
 (6907 88 (:REWRITE TYPED-IO-LISTP-OF-CDR))
 (6829 170 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (6357 174 (:DEFINITION ORDERED-SYMBOL-ALISTP))
 (2908 95 (:DEFINITION TRUE-LISTP))
 (2715 2715 (:REWRITE DEFAULT-CAR))
 (2076 519 (:REWRITE SYMBOL<-TRICHOTOMY))
 (1910 1910 (:REWRITE DEFAULT-CDR))
 (1384 1384 (:TYPE-PRESCRIPTION SYMBOL<))
 (1122 1122 (:TYPE-PRESCRIPTION ORDERED-SYMBOL-ALISTP))
 (1038 173 (:REWRITE SYMBOL<-ASYMMETRIC))
 (942 46 (:DEFINITION LEN))
 (519 519 (:REWRITE SYMBOL<-TRANSITIVE))
 (214 28 (:REWRITE TYPED-IO-LISTP-OF-CDR-AND-CADR-OF-CAR))
 (180 180 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (169 169 (:TYPE-PRESCRIPTION OPEN-CHANNEL1))
 (126 126 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (100 50 (:REWRITE DEFAULT-+-2))
 (50 50 (:REWRITE DEFAULT-+-1))
 (39 21 (:REWRITE TRUE-LIST-OF-CDDR-OF-ASSOC-EQUAL-WHEN-OPEN-CHANNEL-LISTP))
 (28 12 (:REWRITE OPEN-CHANNEL1-OF-CDR-OF-ASSOC-EQUAL))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 )
(UNSIGNED-BYTE-LISTP-OF-CDDR-OF-ASSOC-EQUAL-WHEN-OPEN-CHANNEL-LISTP
 (4199 52 (:REWRITE TYPED-IO-LISTP-OF-CDR-GEN))
 (4103 96 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (3841 106 (:DEFINITION ORDERED-SYMBOL-ALISTP))
 (2953 52 (:REWRITE TYPED-IO-LISTP-OF-CDR))
 (1724 1724 (:REWRITE DEFAULT-CAR))
 (1443 57 (:DEFINITION TRUE-LISTP))
 (1260 315 (:REWRITE SYMBOL<-TRICHOTOMY))
 (1215 1215 (:REWRITE DEFAULT-CDR))
 (840 840 (:TYPE-PRESCRIPTION SYMBOL<))
 (646 646 (:TYPE-PRESCRIPTION ORDERED-SYMBOL-ALISTP))
 (630 105 (:REWRITE SYMBOL<-ASYMMETRIC))
 (501 29 (:DEFINITION LEN))
 (315 315 (:REWRITE SYMBOL<-TRANSITIVE))
 (198 20 (:REWRITE TYPED-IO-LISTP-OF-CDR-AND-CADR-OF-CAR))
 (117 117 (:TYPE-PRESCRIPTION OPEN-CHANNEL1))
 (94 94 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (78 78 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (62 31 (:REWRITE DEFAULT-+-2))
 (31 31 (:REWRITE DEFAULT-+-1))
 (23 15 (:REWRITE TRUE-LIST-OF-CDDR-OF-ASSOC-EQUAL-WHEN-OPEN-CHANNEL-LISTP))
 (14 6 (:REWRITE OPEN-CHANNEL1-OF-CDR-OF-ASSOC-EQUAL))
 (2 2 (:REWRITE DEFAULT-COERCE-2))
 (2 2 (:REWRITE DEFAULT-COERCE-1))
 )
(CHARACTER-LISTP-OF-CDDR-OF-ASSOC-EQUAL-WHEN-OPEN-CHANNEL-LISTP
 (1455 22 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (1399 40 (:DEFINITION ORDERED-SYMBOL-ALISTP))
 (772 772 (:REWRITE DEFAULT-CAR))
 (546 546 (:REWRITE DEFAULT-CDR))
 (468 117 (:REWRITE SYMBOL<-TRICHOTOMY))
 (360 21 (:REWRITE TYPED-IO-LISTP-OF-CDR-GEN))
 (315 21 (:REWRITE TYPED-IO-LISTP-OF-CDR))
 (312 312 (:TYPE-PRESCRIPTION SYMBOL<))
 (234 39 (:REWRITE SYMBOL<-ASYMMETRIC))
 (184 184 (:TYPE-PRESCRIPTION ORDERED-SYMBOL-ALISTP))
 (182 12 (:REWRITE TYPED-IO-LISTP-OF-CDR-AND-CADR-OF-CAR))
 (117 117 (:REWRITE SYMBOL<-TRANSITIVE))
 (68 68 (:TYPE-PRESCRIPTION OPEN-CHANNEL1))
 (60 12 (:DEFINITION LEN))
 (49 20 (:DEFINITION TRUE-LISTP))
 (30 30 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (24 12 (:REWRITE DEFAULT-+-2))
 (12 12 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (12 12 (:REWRITE DEFAULT-+-1))
 )
(OPEN-CHANNEL-LISTP-OF-CONS
 (8 8 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(ORDERED-SYMBOL-ALISTP-OF-REMOVE1-ASSOC-EQUAL)
(OPEN-CHANNEL-LISTP-OF-REMOVE1-ASSOC-EQUAL-ALT
 (28 28 (:REWRITE DEFAULT-CAR))
 (24 24 (:REWRITE DEFAULT-CDR))
 )
(OPEN-CHANNELS-P-OF-REMOVE1-ASSOC-EQUAL-ALT)
(OPEN-INPUT-CHANNEL-P1-FORWARD-TO-ASSOC-EQUAL)
(SYMBOLP-WHEN-ASSOC-EQUAL-AND-OPEN-CHANNELS-P
 (256 19 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (107 107 (:REWRITE DEFAULT-CDR))
 (85 85 (:REWRITE SYMBOL<-TRANSITIVE))
 )
(SYMBOLP-WHEN-ASSOC-EQUAL-OF-OPEN-INPUT-CHANNELS-AND-STATE-P1
 (148 16 (:DEFINITION MEMBER-EQUAL))
 (141 141 (:REWRITE DEFAULT-CAR))
 (135 135 (:REWRITE DEFAULT-CDR))
 (81 1 (:DEFINITION WRITTEN-FILE-LISTP))
 (80 40 (:DEFINITION NTH))
 (77 1 (:DEFINITION READABLE-FILES-LISTP))
 (76 1 (:DEFINITION WRITTEN-FILE))
 (72 1 (:DEFINITION READABLE-FILE))
 (59 1 (:DEFINITION READ-FILE-LISTP))
 (55 10 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (55 1 (:DEFINITION WRITABLE-FILE-LISTP))
 (55 1 (:DEFINITION READ-FILE-LISTP1))
 (51 1 (:DEFINITION WRITABLE-FILE-LISTP1))
 (40 5 (:DEFINITION ASSOC-EQUAL))
 (25 5 (:DEFINITION LEN))
 (22 2 (:DEFINITION FGETPROP))
 (18 9 (:DEFINITION TRUE-LISTP))
 (15 1 (:DEFINITION KNOWN-PACKAGE-ALISTP))
 (12 2 (:DEFINITION SYMBOL-ALISTP))
 (12 1 (:DEFINITION TIMER-ALISTP))
 (12 1 (:DEFINITION PLIST-WORLDP))
 (10 5 (:REWRITE SYMBOL<-TRICHOTOMY))
 (10 5 (:REWRITE DEFAULT-+-2))
 (8 8 (:TYPE-PRESCRIPTION OPEN-CHANNEL1))
 (6 6 (:TYPE-PRESCRIPTION TYPED-IO-LISTP))
 (6 2 (:REWRITE TYPED-IO-LISTP-OF-CDR-GEN))
 (6 2 (:REWRITE TYPED-IO-LISTP-OF-CDR-AND-CADR-OF-CAR))
 (6 2 (:REWRITE TYPED-IO-LISTP-OF-CDR))
 (5 5 (:REWRITE SYMBOL<-TRANSITIVE))
 (5 5 (:REWRITE DEFAULT-+-1))
 (4 1 (:DEFINITION SYMBOL-LISTP))
 (3 1 (:DEFINITION RATIONAL-LISTP))
 (3 1 (:DEFINITION INTEGER-LISTP))
 (1 1 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(SYMBOLP-WHEN-ASSOC-EQUAL-OF-OPEN-INPUT-CHANNELS-AND-STATE-P
 (8 1 (:DEFINITION ASSOC-EQUAL))
 (6 2 (:REWRITE STATE-P-IMPLIES-AND-FORWARD-TO-STATE-P1))
 (6 2 (:REWRITE ASSOC-EQUAL-WHEN-ORDERED-SYMBOL-ALISTP-AND-SYMBOL<-OF-CAAR))
 (3 3 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(ASSOC-EQUAL-OF-OPEN-INPUT-CHANNELS-WHEN-OPEN-INPUT-CHANNEL-P)
