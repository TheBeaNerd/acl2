(DEPGRAPH::INVERT-INNER-LOOP)
(DEPGRAPH::INVERT-INNER-LOOP-CORRECT
     (1678 79
           (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
     (1113 150 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (913 141 (:REWRITE DEFAULT-CDR))
     (842 318
          (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (836 138
          (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
     (706 150 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (619 233
          (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (343 13 (:REWRITE SUBSETP-OF-CONS))
     (318 318 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (318 318 (:REWRITE CONSP-BY-LEN))
     (184 184 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (182 182 (:REWRITE SUBSETP-TRANS2))
     (182 182 (:REWRITE SUBSETP-TRANS))
     (101 101
          (:TYPE-PRESCRIPTION DEPGRAPH::INVERT-INNER-LOOP))
     (97 81 (:REWRITE DEFAULT-CAR))
     (83 83 (:REWRITE SUBSETP-MEMBER . 2))
     (81 81
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
     (81 81 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (78 78 (:REWRITE SUBSETP-MEMBER . 4))
     (78 78 (:REWRITE INTERSECTP-MEMBER . 3))
     (78 78 (:REWRITE INTERSECTP-MEMBER . 2))
     (70 70
         (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP)))
(DEPGRAPH::INVERT-OUTER-LOOP)
(DEPGRAPH::INVERT-OUTER-LOOP-WHEN-ATOM
     (19 19
         (:TYPE-PRESCRIPTION DEPGRAPH::INVERT-OUTER-LOOP))
     (2 1
        (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (1 1 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (1 1 (:REWRITE CONSP-BY-LEN)))
(DEPGRAPH::L1 (316 14
                   (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
              (227 25 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
              (226 10 (:REWRITE SUBSETP-MEMBER . 3))
              (191 32 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
              (182 71
                   (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
              (167 26 (:REWRITE DEFAULT-CDR))
              (159 51
                   (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
              (129 25 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
              (71 71 (:TYPE-PRESCRIPTION TRUE-LISTP))
              (71 71 (:REWRITE CONSP-BY-LEN))
              (63 7 (:REWRITE MEMBER-WHEN-ATOM))
              (40 40 (:REWRITE CONSP-OF-CDR-BY-LEN))
              (35 23
                  (:TYPE-PRESCRIPTION DEPGRAPH::INVERT-OUTER-LOOP))
              (28 28 (:REWRITE SUBSETP-TRANS2))
              (28 28 (:REWRITE SUBSETP-TRANS))
              (16 16
                  (:TYPE-PRESCRIPTION DEPGRAPH::INVERT-INNER-LOOP))
              (16 16
                  (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
              (11 11 (:REWRITE DEFAULT-CAR))
              (11 11 (:REWRITE CAR-WHEN-ALL-EQUALP))
              (10 10 (:REWRITE SUBSETP-MEMBER . 4))
              (10 10 (:REWRITE SUBSETP-MEMBER . 2))
              (10 10 (:REWRITE INTERSECTP-MEMBER . 3))
              (10 10 (:REWRITE INTERSECTP-MEMBER . 2))
              (7 7
                 (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
              (2 2 (:REWRITE CONSP-OF-CDDR-BY-LEN)))
(DEPGRAPH::L2 (425 171
                   (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
              (409 65 (:REWRITE DEFAULT-CDR))
              (378 62 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
              (364 107
                   (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
              (347 60 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
              (342 17
                   (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
              (171 171 (:TYPE-PRESCRIPTION TRUE-LISTP))
              (171 171 (:REWRITE CONSP-BY-LEN))
              (148 23 (:REWRITE MEMBER-WHEN-ATOM))
              (121 3 (:REWRITE SUBSETP-OF-CONS))
              (95 95 (:REWRITE CONSP-OF-CDR-BY-LEN))
              (94 20
                  (:REWRITE DEPGRAPH::INVERT-OUTER-LOOP-WHEN-ATOM))
              (70 70 (:REWRITE SUBSETP-TRANS2))
              (70 70 (:REWRITE SUBSETP-TRANS))
              (67 39
                  (:TYPE-PRESCRIPTION DEPGRAPH::INVERT-OUTER-LOOP))
              (56 56
                  (:TYPE-PRESCRIPTION DEPGRAPH::INVERT-INNER-LOOP))
              (44 44 (:REWRITE SUBSETP-MEMBER . 2))
              (41 41
                  (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
              (30 30
                  (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
              (27 27 (:REWRITE SUBSETP-MEMBER . 4))
              (27 27 (:REWRITE INTERSECTP-MEMBER . 3))
              (27 27 (:REWRITE INTERSECTP-MEMBER . 2))
              (19 19 (:REWRITE DEFAULT-CAR))
              (19 19 (:REWRITE CAR-WHEN-ALL-EQUALP))
              (5 5 (:REWRITE CONSP-OF-CDDR-BY-LEN)))
(DEPGRAPH::INVERT-OUTER-LOOP-CORRECT
     (2100 111
           (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
     (2001 2001
           (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL))
     (1395 541
           (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (1335 270 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
     (1289 213
           (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
     (1216 195 (:REWRITE DEFAULT-CDR))
     (1174 363
           (:REWRITE HONS-ASSOC-EQUAL-WHEN-ATOM))
     (554 14 (:REWRITE SUBSETP-OF-CONS))
     (541 541 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (541 541 (:REWRITE CONSP-BY-LEN))
     (532 74 (:REWRITE MEMBER-WHEN-ATOM))
     (333 221
          (:TYPE-PRESCRIPTION DEPGRAPH::INVERT-OUTER-LOOP))
     (322 322 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (308 308 (:REWRITE SUBSETP-TRANS2))
     (308 308 (:REWRITE SUBSETP-TRANS))
     (200 200
          (:TYPE-PRESCRIPTION DEPGRAPH::INVERT-INNER-LOOP))
     (138 138 (:REWRITE SUBSETP-MEMBER . 2))
     (130 130
          (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
     (95 95 (:REWRITE SUBSETP-MEMBER . 4))
     (95 95 (:REWRITE INTERSECTP-MEMBER . 3))
     (95 95 (:REWRITE INTERSECTP-MEMBER . 2))
     (84 84
         (:REWRITE HONS-ASSOC-EQUAL-WHEN-FOUND-BY-FAL-FIND-ANY))
     (62 62 (:REWRITE DEFAULT-CAR))
     (62 62 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (13 13 (:REWRITE CONSP-OF-CDDR-BY-LEN)))
(DEPGRAPH::INVERT)
(DEPGRAPH::L0 (113 27
                   (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
              (38 10 (:REWRITE DEFAULT-CDR))
              (23 23 (:TYPE-PRESCRIPTION TRUE-LISTP))
              (23 23 (:REWRITE CONSP-BY-LEN))
              (20 20 (:TYPE-PRESCRIPTION PAIRLIS$))
              (15 3 (:REWRITE CONSP-OF-HONS-ASSOC-EQUAL))
              (12 12 (:REWRITE CONSP-OF-CDR-BY-LEN))
              (8 8 (:REWRITE DEFAULT-CAR))
              (8 8 (:REWRITE CAR-WHEN-ALL-EQUALP))
              (2 2 (:REWRITE CONSP-OF-CDDR-BY-LEN)))
(DEPGRAPH::INVERT-CORRECT
     (396 123
          (:REWRITE CONSP-UNDER-IFF-WHEN-TRUE-LISTP))
     (163 19 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
     (139 42 (:REWRITE DEFAULT-CDR))
     (136 22 (:REWRITE PAIRLIS$-WHEN-ATOM))
     (125 71 (:REWRITE ALIST-KEYS-WHEN-ATOM))
     (115 19
          (:REWRITE DEPGRAPH::INVERT-OUTER-LOOP-WHEN-ATOM))
     (87 87 (:TYPE-PRESCRIPTION TRUE-LISTP))
     (87 87 (:REWRITE CONSP-BY-LEN))
     (42 6 (:REWRITE LAST-WHEN-ATOM-OF-CDR))
     (42 6 (:REWRITE CONSP-OF-CAR-WHEN-ALISTP))
     (37 37 (:REWRITE CONSP-OF-CDR-BY-LEN))
     (36 12 (:TYPE-PRESCRIPTION FAST-ALIST-FORK))
     (32 32 (:REWRITE SUBSETP-TRANS2))
     (32 32 (:REWRITE SUBSETP-TRANS))
     (25 25 (:REWRITE SUBSETP-MEMBER . 4))
     (25 25 (:REWRITE INTERSECTP-MEMBER . 3))
     (25 25 (:REWRITE INTERSECTP-MEMBER . 2))
     (24 24 (:REWRITE DEFAULT-CAR))
     (24 24 (:REWRITE CAR-WHEN-ALL-EQUALP))
     (19 19 (:REWRITE SUBSETP-MEMBER . 2))
     (12 12 (:TYPE-PRESCRIPTION ALISTP))
     (11 11
         (:REWRITE MEMBER-EQUAL-WHEN-ALL-EQUALP))
     (6 6 (:REWRITE LAST-WHEN-ATOM))
     (6 6 (:REWRITE ALISTP-WHEN-ATOM)))
