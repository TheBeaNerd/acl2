(HONS-ASSOC-EQUAL-HSHRINK-ALIST
     (100 7 (:DEFINITION HONS-ASSOC-EQUAL))
     (32 32 (:REWRITE DEFAULT-CAR))
     (32 8 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (31 1 (:DEFINITION FAST-ALIST-FORK))
     (21 21
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (17 17 (:REWRITE DEFAULT-CDR))
     (16 16 (:TYPE-PRESCRIPTION ALISTP))
     (8 8 (:REWRITE ALISTP-WHEN-ATOM))
     (7 7 (:DEFINITION HONS-EQUAL))
     (3 3
        (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY)))
(HONS-ASSOC-EQUAL-AL-SHRINK (12 1 (:DEFINITION FAST-ALIST-FORK))
                            (4 4 (:REWRITE DEFAULT-CAR))
                            (4 1 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
                            (2 2 (:TYPE-PRESCRIPTION ALISTP))
                            (2 2 (:REWRITE DEFAULT-CDR))
                            (1 1 (:REWRITE ALISTP-WHEN-ATOM)))
(ALIST-EQUIV-AL-SHRINK (2 2
                          (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM)))
(HSHRINK-ALIST-ALIST-EQUIV-APPEND
     (15 1 (:DEFINITION FAST-ALIST-FORK))
     (7 7 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (5 5 (:REWRITE DEFAULT-CAR))
     (5 1 (:DEFINITION BINARY-APPEND))
     (4 4 (:REWRITE DEFAULT-CDR))
     (4 1 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (2 2 (:TYPE-PRESCRIPTION ALISTP))
     (2 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
     (2 2
        (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (2 1
        (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1 1 (:TYPE-PRESCRIPTION FAST-ALIST-FORK))
     (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND))
     (1 1
        (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
     (1 1 (:REWRITE ALISTP-WHEN-ATOM)))
(HONS-ASSOC-EQUAL-MAKE-FAL
     (356 65 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (354 354 (:REWRITE DEFAULT-CAR))
     (213 213 (:REWRITE DEFAULT-CDR))
     (178 178 (:TYPE-PRESCRIPTION ALISTP))
     (135 135 (:TYPE-PRESCRIPTION MAKE-FAL))
     (96 24 (:REWRITE ALISTP-OF-CDR))
     (89 89 (:REWRITE ALISTP-WHEN-ATOM))
     (66 66
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY)))
(MAKE-FAL-ALIST-EQUIV-APPEND (14 1 (:DEFINITION MAKE-FAL))
                             (6 6 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
                             (5 5 (:REWRITE DEFAULT-CAR))
                             (5 1 (:DEFINITION BINARY-APPEND))
                             (4 4 (:REWRITE DEFAULT-CDR))
                             (4 1 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
                             (2 2 (:TYPE-PRESCRIPTION ALISTP))
                             (2 2 (:REWRITE APPEND-WHEN-NOT-CONSP))
                             (2 2
                                (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
                             (2 1
                                (:TYPE-PRESCRIPTION TRUE-LISTP-APPEND))
                             (2 1 (:DEFINITION HONS-ACONS))
                             (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
                             (1 1 (:TYPE-PRESCRIPTION MAKE-FAL))
                             (1 1 (:TYPE-PRESCRIPTION BINARY-APPEND))
                             (1 1 (:REWRITE CONS-CAR-CDR))
                             (1 1 (:REWRITE ALISTP-WHEN-ATOM)))
(SET-EQUIV-IMPLIES-ALIST-EQUIV-FAL-EXTRACT-1
     (20 2 (:DEFINITION MEMBER-EQUAL))
     (20 2 (:DEFINITION FAL-EXTRACT))
     (12 6 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (6 6 (:REWRITE FAL-EXTRACT-WHEN-ATOM))
     (6 6 (:REWRITE DEFAULT-CDR))
     (6 2 (:DEFINITION HONS-GET))
     (4 4 (:REWRITE SUBSETP-MEMBER . 4))
     (4 4 (:REWRITE SUBSETP-MEMBER . 3))
     (4 4 (:REWRITE SUBSETP-MEMBER . 2))
     (4 4 (:REWRITE SUBSETP-MEMBER . 1))
     (4 4 (:REWRITE MEMBER-WHEN-ATOM))
     (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
     (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
     (4 4 (:REWRITE DEFAULT-CAR))
     (2 2
        (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY)))
(ALIST-KEYS-HONS-PUT-LIST
     (323 309 (:REWRITE DEFAULT-CAR))
     (260 239 (:REWRITE DEFAULT-CDR))
     (234 48 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (220 144 (:REWRITE ALIST-KEYS-WHEN-ATOM))
     (100 58
          (:REWRITE APPEND-ATOM-UNDER-LIST-EQUIV))
     (96 96 (:TYPE-PRESCRIPTION ALISTP))
     (66 54
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (55 48 (:REWRITE ALISTP-WHEN-ATOM))
     (47 47
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
     (35 7 (:REWRITE HONS-ASSOC-EQUAL-OF-CONS))
     (30 3 (:DEFINITION MEMBER-EQUAL))
     (6 6 (:REWRITE SUBSETP-MEMBER . 4))
     (6 6 (:REWRITE SUBSETP-MEMBER . 3))
     (6 6 (:REWRITE SUBSETP-MEMBER . 2))
     (6 6 (:REWRITE SUBSETP-MEMBER . 1))
     (6 6 (:REWRITE MEMBER-WHEN-ATOM))
     (6 6 (:REWRITE INTERSECTP-MEMBER . 3))
     (6 6 (:REWRITE INTERSECTP-MEMBER . 2)))
(ALIST-FIX-ALIST-EQUIV (6 3 (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
                       (4 1 (:REWRITE ALIST-FIX-WHEN-ALISTP))
                       (2 2 (:TYPE-PRESCRIPTION ALISTP))
                       (1 1 (:REWRITE ALISTP-WHEN-ATOM))
                       (1 1 (:REWRITE ALIST-FIX-OF-ATOM)))
(NONEMPTY-ALISTP)
(FIRST-KEY)
(NONEMPTY-ALISTP-FIRST-KEY
     (196 37 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (98 98 (:TYPE-PRESCRIPTION ALISTP))
     (86 86 (:REWRITE DEFAULT-CAR))
     (49 49 (:REWRITE ALISTP-WHEN-ATOM))
     (48 12 (:REWRITE ALISTP-OF-CDR))
     (47 47 (:REWRITE DEFAULT-CDR))
     (3 3
        (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY)))
(EMPTY-ALIST-HONS-ASSOC-EQUAL (48 10 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
                              (24 24 (:TYPE-PRESCRIPTION ALISTP))
                              (13 13 (:REWRITE DEFAULT-CAR))
                              (12 12 (:REWRITE ALISTP-WHEN-ATOM))
                              (10 10 (:REWRITE DEFAULT-CDR))
                              (8 2 (:REWRITE ALISTP-OF-CDR)))
(ALIST-EQUIV-IMPLIES-EQUAL-NONEMPTY-ALISTP-1
     (36 4 (:DEFINITION FIRST-KEY))
     (32 8 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (16 16 (:TYPE-PRESCRIPTION ALISTP))
     (16 16 (:REWRITE DEFAULT-CAR))
     (8 8 (:REWRITE DEFAULT-CDR))
     (8 8 (:REWRITE ALISTP-WHEN-ATOM))
     (4 4
        (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM)))
(AL-COVERS-KEYS)
(AL-COVERS-KEYS-TO-SUBSET
     (30 9 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (22 2
         (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
     (21 21
         (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
     (10 10
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
     (10 10
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (10 10 (:REWRITE DEFAULT-CAR))
     (9 9 (:REWRITE SUBSETP-TRANS2))
     (9 9 (:REWRITE SUBSETP-TRANS))
     (5 5 (:REWRITE ALIST-KEYS-WHEN-ATOM))
     (4 4 (:REWRITE DEFAULT-CDR)))
(ALIST-EQUIV-IMPLIES-EQUAL-AL-COVERS-KEYS-2)
(SET-EQUIV-IMPLIES-EQUAL-AL-COVERS-KEYS-1)
(HONS-ASSOC-EQUAL-HONS-ACONS-EACH
     (39 15
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (24 24 (:TYPE-PRESCRIPTION HONS-ACONS-EACH))
     (22 22 (:REWRITE DEFAULT-CAR))
     (19 13 (:REWRITE SUBSETP-MEMBER . 3))
     (13 13 (:REWRITE SUBSETP-MEMBER . 4))
     (13 13 (:REWRITE SUBSETP-MEMBER . 2))
     (13 13 (:REWRITE INTERSECTP-MEMBER . 3))
     (13 13 (:REWRITE INTERSECTP-MEMBER . 2))
     (10 10 (:REWRITE DEFAULT-CDR))
     (2 2 (:REWRITE SUBSETP-TRANS2))
     (2 2 (:REWRITE SUBSETP-TRANS))
     (1 1 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (1 1 (:REWRITE SUBSETP-WHEN-ATOM-LEFT)))
(ALIST-KEYS-HONS-ACONS-EACH (21 9 (:REWRITE ALIST-KEYS-WHEN-ATOM))
                            (12 12 (:TYPE-PRESCRIPTION HONS-ACONS-EACH))
                            (7 7 (:REWRITE DEFAULT-CAR))
                            (4 4 (:REWRITE DEFAULT-CDR)))
(KEYS-EQUIV)
(KEYS-EQUIV-NECC)
(KEYS-EQUIV-WITNESSING-WITNESS-RULE-CORRECT)
(KEYS-EQUIV-INSTANCING-INSTANCE-RULE-CORRECT)
(KEYS-EQUIV-REFL (2 2
                    (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM)))
(KEYS-EQUIV-SYMM (7 7
                    (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM)))
(KEYS-EQUIV-TRANS (11 11
                      (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM)))
(KEYS-EQUIV-IS-AN-EQUIVALENCE)
(KEYS-EQUIV)
(KEYS-EQUIV-IMPLIES-IFF-HONS-ASSOC-EQUAL-2
     (11 11
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM)))
(KEYS-EQUIV-IMPLIES-SET-EQUIV-ALIST-KEYS-1
     (6 6 (:REWRITE ALIST-KEYS-WHEN-ATOM))
     (3 3
        (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM)))
(KEYS-EQUIV-WHEN-ALIST-KEYS (12 1 (:DEFINITION MEMBER-EQUAL))
                            (11 11 (:REWRITE ALIST-KEYS-WHEN-ATOM))
                            (5 5
                               (:TYPE-PRESCRIPTION TRUE-LISTP-OF-ALIST-KEYS))
                            (5 2 (:REWRITE MEMBER-WHEN-ATOM))
                            (4 4 (:REWRITE SUBSETP-MEMBER . 4))
                            (4 4 (:REWRITE INTERSECTP-MEMBER . 3))
                            (4 4 (:REWRITE INTERSECTP-MEMBER . 2))
                            (3 3 (:REWRITE SUBSETP-MEMBER . 2))
                            (2 2 (:REWRITE SUBSETP-TRANS2))
                            (2 2 (:REWRITE SUBSETP-TRANS))
                            (1 1 (:REWRITE DEFAULT-CDR))
                            (1 1 (:REWRITE DEFAULT-CAR)))
