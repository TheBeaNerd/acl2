(F1)
(APPLY$-WARRANT-F1)
(APPLY$-WARRANT-F1-DEFINITION)
(APPLY$-WARRANT-F1-NECC)
(APPLY$-F1
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(G1)
(WARRANT-F1-WRAPPER)
(F1)
(G1
 (10 10 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE DEFAULT-CAR))
 (4 1 (:REWRITE O-P-O-INFP-CAR))
 (3 3 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (2 1 (:REWRITE DEFAULT-+-2))
 (1 1 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (1 1 (:REWRITE O-P-DEF-O-FINP-1))
 (1 1 (:REWRITE DEFAULT-+-1))
 )
(APPLY$-WARRANT-G1)
(APPLY$-WARRANT-G1-DEFINITION)
(APPLY$-WARRANT-G1-NECC)
(APPLY$-G1
 (572 523 (:REWRITE DEFAULT-CDR))
 (488 4 (:DEFINITION TAMEP))
 (156 34 (:REWRITE O-P-O-INFP-CAR))
 (136 128 (:REWRITE DEFAULT-CAR))
 (88 11 (:DEFINITION SYMBOL-LISTP))
 (76 4 (:DEFINITION LENGTH))
 (64 64 (:TYPE-PRESCRIPTION O-P))
 (58 32 (:REWRITE O-P-DEF-O-FINP-1))
 (56 8 (:DEFINITION LEN))
 (32 32 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (26 26 (:TYPE-PRESCRIPTION O-FINP))
 (26 2 (:REWRITE APPLY$-PRIM-ARITY-1))
 (20 4 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (16 8 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE TAMEP-TRUE-CAR/CDR-NESTP))
 (14 5 (:REWRITE APPLY$-PRIMITIVE))
 (14 2 (:REWRITE APPLY$-CONSP-ARITY-1))
 (14 2 (:DEFINITION PAIRLIS$))
 (10 2 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (8 8 (:TYPE-PRESCRIPTION LEN))
 (8 8 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (8 8 (:REWRITE DEFAULT-+-1))
 (8 4 (:REWRITE EV$-OPENER))
 (6 6 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (6 2 (:DEFINITION APPLY$-BADGEP))
 (4 4 (:REWRITE UNTAME-APPLY$-TAKES-ARITY-ARGS))
 (4 4 (:REWRITE DEFAULT-COERCE-2))
 (4 4 (:REWRITE DEFAULT-COERCE-1))
 (4 4 (:REWRITE BADGE-PRIM-TYPE))
 (4 2 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (4 2 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (2 2 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (2 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE APPLY$-USERFN-ARITY-1))
 (2 2 (:META APPLY$-PRIM-META-FN-CORRECT))
 )
(FN-EQUAL-IMPLIES-EQUAL-G1-1)
(F2)
(APPLY$-WARRANT-F2)
(APPLY$-WARRANT-F2-DEFINITION)
(APPLY$-WARRANT-F2-NECC)
(APPLY$-F2
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(F2)
(MY-NATP)
(APPLY$-WARRANT-MY-NATP)
(APPLY$-WARRANT-MY-NATP-DEFINITION)
(APPLY$-WARRANT-MY-NATP-NECC)
(APPLY$-MY-NATP
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(F3
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(APPLY$-WARRANT-F3)
(APPLY$-WARRANT-F3-DEFINITION)
(APPLY$-WARRANT-F3-NECC)
(APPLY$-F3
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(F4
 (1019 1 (:DEFINITION MEMBER-EQUAL))
 (773 8 (:DEFINITION ALWAYS$))
 (682 2 (:REWRITE PLAIN-UQI-INTEGER-LISTP))
 (613 4 (:DEFINITION APPLY$-BADGEP))
 (436 3 (:DEFINITION INTEGER-LISTP))
 (435 8 (:REWRITE APPLY$-SYMBOL-ARITY-1))
 (435 2 (:REWRITE INTEGER-LISTP-IMPLIES-ALWAYS$-INTEGERP))
 (419 8 (:REWRITE APPLY$-BADGEP-PROPERTIES . 1))
 (395 8 (:REWRITE APPLY$-PRIMITIVE))
 (379 8 (:META APPLY$-PRIM-META-FN-CORRECT))
 (321 12 (:DEFINITION SUBSETP-EQUAL))
 (300 33 (:REWRITE SUBSETP-REFLEXIVE-LEMMA))
 (208 4 (:REWRITE APPLY$-BADGEP-PROPERTIES . 2))
 (161 161 (:REWRITE DEFAULT-CDR))
 (144 8 (:DEFINITION LOOP$-AS))
 (99 99 (:TYPE-PRESCRIPTION SUBSETP-EQUAL))
 (97 97 (:REWRITE DEFAULT-CAR))
 (94 2 (:REWRITE PLAIN-UQI-TRUE-LIST-LISTP))
 (67 2 (:REWRITE PLAIN-UQI-ACL2-NUMBER-LISTP))
 (63 6 (:DEFINITION NATP))
 (61 2 (:REWRITE PLAIN-UQI-SYMBOL-LISTP))
 (61 2 (:REWRITE PLAIN-UQI-RATIONAL-LISTP))
 (60 12 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-1))
 (55 8 (:DEFINITION TRUE-LISTP))
 (53 2 (:REWRITE PLAIN-UQI-RATIONAL-LIST-LISTP))
 (48 8 (:DEFINITION CDR-LOOP$-AS-TUPLE))
 (48 8 (:DEFINITION CAR-LOOP$-AS-TUPLE))
 (43 5 (:DEFINITION RATIONAL-LISTP))
 (42 2 (:REWRITE TRUE-LIST-LISTP-IMPLIES-ALWAYS$-TRUE-LISTP))
 (40 40 (:TYPE-PRESCRIPTION ALWAYS$))
 (40 8 (:DEFINITION EMPTY-LOOP$-AS-TUPLEP))
 (36 36 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-3))
 (33 33 (:REWRITE TRANSITIVITY-OF-SUBSETP-EQUAL))
 (33 1 (:REWRITE FANCY-UQI-RATIONAL-LISTP-1))
 (32 16 (:REWRITE APPLY$-PRIMP-BADGE))
 (31 2 (:REWRITE STRUCTURE-OF-LOOP$-AS-ELEMENTS-BRIDGE))
 (30 30 (:TYPE-PRESCRIPTION APPLY$-BADGEP))
 (27 3 (:DEFINITION ACL2-NUMBER-LISTP))
 (26 26 (:REWRITE SUBSETP-IMPLIES-MEMBER))
 (25 25 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (24 24 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (24 24 (:REWRITE MEMBER-EQUAL-NEWVAR-COMPONENTS-2))
 (24 6 (:REWRITE O-P-O-INFP-CAR))
 (24 2 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ALWAYS$-ACL2-NUMBERP))
 (21 3 (:DEFINITION SYMBOL-LISTP))
 (21 1 (:REWRITE FANCY-UQI-TRUE-LIST-1))
 (21 1 (:REWRITE FANCY-UQI-IDENTITY-1))
 (20 2 (:REWRITE SYMBOL-LISTP-IMPLIES-ALWAYS$-SYMBOLP))
 (20 2 (:REWRITE RATIONAL-LISTP-IMPLIES-ALWAYS$-RATIONALP))
 (18 9 (:LINEAR APPLY$-BADGEP-PROPERTIES . 1))
 (18 4 (:DEFINITION WEAK-APPLY$-BADGE-P))
 (18 3 (:DEFINITION ALL-NILS))
 (15 15 (:TYPE-PRESCRIPTION SYMBOL-LISTP))
 (15 15 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (15 15 (:TYPE-PRESCRIPTION ALL-NILS))
 (15 15 (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (12 12 (:TYPE-PRESCRIPTION O-P))
 (12 6 (:REWRITE APPLY$-BADGEP-PROPERTIES . 3))
 (12 1 (:REWRITE FANCY-UQI-ACL2-NUMBER-1))
 (10 10 (:REWRITE RATIONAL-LISTP-IMPLIES-RATIONALP))
 (10 1 (:REWRITE FANCY-UQI-SYMBOL-1))
 (10 1 (:REWRITE FANCY-UQI-RATIONAL-1))
 (10 1 (:REWRITE FANCY-UQI-INTEGER-1))
 (9 9 (:REWRITE INTEGER-LISTP-IMPLIES-INTEGERP))
 (8 8 (:REWRITE APPLY$-CONSP-ARITY-1))
 (8 8 (:REWRITE ALWAYS$-P-LST-IMPLIES-P-ELEMENT))
 (8 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (8 4 (:REWRITE DEFAULT-+-2))
 (7 7 (:LINEAR BOUNDS-POSITION-EQUAL-AC))
 (7 7 (:LINEAR BOUNDS-POSITION-EQUAL))
 (6 6 (:REWRITE O-P-DEF-O-FINP-1))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 3 (:LINEAR APPLY$-BADGEP-PROPERTIES . 2))
 (4 4 (:REWRITE SYMBOL-LISTP-IMPLIES-SYMBOLP))
 (4 4 (:REWRITE DEFAULT-+-1))
 (4 4 (:REWRITE ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP))
 (3 1 (:REWRITE EQUAL-LEN-1))
 (2 2 (:REWRITE PLAIN-UQI-ALWAYS$))
 (1 1 (:REWRITE FANCY-UQI-ALWAYS$-1))
 (1 1 (:DEFINITION IDENTITY))
 )
(MY-CAR)
(APPLY$-WARRANT-MY-CAR)
(APPLY$-WARRANT-MY-CAR-DEFINITION)
(APPLY$-WARRANT-MY-CAR-NECC)
(APPLY$-MY-CAR
 (2 2 (:TYPE-PRESCRIPTION APPLY$-PRIMP))
 (2 2 (:REWRITE DEFAULT-CAR))
 (2 1 (:REWRITE APPLY$-PRIMP-BADGE))
 (2 1 (:REWRITE APPLY$-PRIMITIVE))
 )
(F5
 (5 5 (:REWRITE DEFAULT-CDR))
 (4 4 (:REWRITE TRUE-LIST-LISTP-IMPLIES-TRUE-LISTP))
 (4 1 (:REWRITE O-P-O-INFP-CAR))
 (1 1 (:REWRITE O-P-DEF-O-FINP-1))
 (1 1 (:REWRITE LEN-MEMBER-EQUAL-LOOP$-AS))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
