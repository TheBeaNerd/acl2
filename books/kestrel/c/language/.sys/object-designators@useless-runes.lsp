(TMP-DEFTYPES-NATP-OF-NFIX)
(TMP-DEFTYPES-NFIX-WHEN-NATP)
(C::ADDRESSP
 (156 12 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (60 12 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (60 12 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (48 48 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (36 9 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (24 24 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (24 24 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (24 12 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (24 12 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 )
(C::CONSP-WHEN-ADDRESSP)
(C::TAG-WHEN-ADDRESSP)
(C::ADDRESSP-WHEN-WRONG-TAG)
(C::ADDRESS-FIX$INLINE)
(C::ADDRESSP-OF-ADDRESS-FIX
 (3 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(C::ADDRESS-FIX-WHEN-ADDRESSP
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(C::ADDRESS-FIX$INLINE
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(C::ADDRESS-EQUIV$INLINE)
(C::ADDRESS-EQUIV-IS-AN-EQUIVALENCE)
(C::ADDRESS-EQUIV-IMPLIES-EQUAL-ADDRESS-FIX-1)
(C::ADDRESS-FIX-UNDER-ADDRESS-EQUIV)
(C::EQUAL-OF-ADDRESS-FIX-1-FORWARD-TO-ADDRESS-EQUIV)
(C::EQUAL-OF-ADDRESS-FIX-2-FORWARD-TO-ADDRESS-EQUIV)
(C::ADDRESS-EQUIV-OF-ADDRESS-FIX-1-FORWARD)
(C::ADDRESS-EQUIV-OF-ADDRESS-FIX-2-FORWARD)
(C::TAG-OF-ADDRESS-FIX)
(C::ADDRESS->NUMBER$INLINE
 (4 1 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(C::NATP-OF-ADDRESS->NUMBER)
(C::ADDRESS->NUMBER$INLINE-OF-ADDRESS-FIX-X
 (102 34 (:REWRITE C::ADDRESS-FIX-WHEN-ADDRESSP))
 (68 68 (:TYPE-PRESCRIPTION C::ADDRESSP))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(C::ADDRESS->NUMBER$INLINE-ADDRESS-EQUIV-CONGRUENCE-ON-X)
(C::ADDRESS)
(C::ADDRESSP-OF-ADDRESS
 (6 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(C::ADDRESS->NUMBER-OF-ADDRESS
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(C::ADDRESS-OF-FIELDS
 (3 1 (:REWRITE C::ADDRESS-FIX-WHEN-ADDRESSP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:TYPE-PRESCRIPTION C::ADDRESSP))
 )
(C::ADDRESS-FIX-WHEN-ADDRESS
 (3 1 (:REWRITE C::ADDRESS-FIX-WHEN-ADDRESSP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:TYPE-PRESCRIPTION C::ADDRESSP))
 )
(C::EQUAL-OF-ADDRESS
 (12 12 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(C::ADDRESS-OF-NFIX-NUMBER
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(C::ADDRESS-NAT-EQUIV-CONGRUENCE-ON-NUMBER)
(C::ADDRESS-FIX-REDEF)
(C::TAG-OF-ADDRESS)
(TMP-DEFTYPES-NATP-OF-NFIX)
(TMP-DEFTYPES-NFIX-WHEN-NATP)
(C::OBJDESIGNP
 (4 4 (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
 )
(C::CONSP-WHEN-OBJDESIGNP)
(C::OBJDESIGN-KIND$INLINE)
(C::OBJDESIGN-KIND-POSSIBILITIES)
(C::OBJDESIGN-FIX$INLINE
 (4 4 (:LINEAR ACL2-COUNT-OF-CONSP-POSITIVE))
 )
(C::OBJDESIGNP-OF-OBJDESIGN-FIX
 (218 54 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (105 15 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (102 102 (:TYPE-PRESCRIPTION C::IDENTP))
 (80 6 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (66 6 (:REWRITE NATP-OF-CAR-WHEN-NAT-LISTP))
 (56 14 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (56 6 (:REWRITE C::IDENTP-OF-CAR-WHEN-IDENT-LISTP))
 (42 12 (:REWRITE NAT-LISTP-OF-CDR-WHEN-NAT-LISTP))
 (32 8 (:REWRITE C::IDENT-LISTP-OF-CDR-WHEN-IDENT-LISTP))
 (31 11 (:REWRITE C::ADDRESS-FIX-WHEN-ADDRESSP))
 (24 24 (:TYPE-PRESCRIPTION NATP))
 (20 20 (:TYPE-PRESCRIPTION C::ADDRESSP))
 (20 20 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (16 16 (:REWRITE NAT-LISTP-WHEN-NOT-CONSP))
 (14 14 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (6 6 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::OBJDESIGN-FIX-WHEN-OBJDESIGNP)
(C::OBJDESIGN-FIX$INLINE)
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(C::OBJDESIGN-EQUIV$INLINE)
(C::OBJDESIGN-EQUIV-IS-AN-EQUIVALENCE)
(C::OBJDESIGN-EQUIV-IMPLIES-EQUAL-OBJDESIGN-FIX-1)
(C::OBJDESIGN-FIX-UNDER-OBJDESIGN-EQUIV)
(C::EQUAL-OF-OBJDESIGN-FIX-1-FORWARD-TO-OBJDESIGN-EQUIV)
(C::EQUAL-OF-OBJDESIGN-FIX-2-FORWARD-TO-OBJDESIGN-EQUIV)
(C::OBJDESIGN-EQUIV-OF-OBJDESIGN-FIX-1-FORWARD)
(C::OBJDESIGN-EQUIV-OF-OBJDESIGN-FIX-2-FORWARD)
(C::OBJDESIGN-KIND$INLINE-OF-OBJDESIGN-FIX-X
 (67 43 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (25 17 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (24 24 (:TYPE-PRESCRIPTION C::IDENTP))
 (8 8 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (7 5 (:REWRITE C::ADDRESS-FIX-WHEN-ADDRESSP))
 (6 6 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION C::ADDRESSP))
 )
(C::OBJDESIGN-KIND$INLINE-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::CONSP-OF-OBJDESIGN-FIX)
(C::TAG-WHEN-OBJDESIGNP-FORWARD)
(C::TAG-OF-OBJDESIGN-FIX)
(C::OBJDESIGN-STATIC->NAME$INLINE)
(C::IDENTP-OF-OBJDESIGN-STATIC->NAME
 (3 1 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 )
(C::OBJDESIGN-STATIC->NAME$INLINE-OF-OBJDESIGN-FIX-X
 (13 5 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (8 8 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::OBJDESIGN-STATIC->NAME$INLINE-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-STATIC->NAME-WHEN-WRONG-KIND
 (6 2 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (4 4 (:TYPE-PRESCRIPTION C::IDENTP))
 )
(C::OBJDESIGN-STATIC)
(C::RETURN-TYPE-OF-OBJDESIGN-STATIC
 (6 2 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (4 4 (:TYPE-PRESCRIPTION C::IDENTP))
 )
(C::OBJDESIGN-STATIC->NAME-OF-OBJDESIGN-STATIC)
(C::OBJDESIGN-STATIC-OF-FIELDS
 (3 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::OBJDESIGN-FIX-WHEN-STATIC
 (3 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::EQUAL-OF-OBJDESIGN-STATIC)
(C::OBJDESIGN-STATIC-OF-IDENT-FIX-NAME)
(C::OBJDESIGN-STATIC-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::OBJDESIGN-AUTO->NAME$INLINE)
(C::IDENTP-OF-OBJDESIGN-AUTO->NAME
 (3 1 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 )
(C::OBJDESIGN-AUTO->NAME$INLINE-OF-OBJDESIGN-FIX-X
 (12 4 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (8 8 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (6 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(C::OBJDESIGN-AUTO->NAME$INLINE-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-AUTO->NAME-WHEN-WRONG-KIND
 (6 2 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (4 4 (:TYPE-PRESCRIPTION C::IDENTP))
 )
(C::OBJDESIGN-AUTO->FRAME$INLINE)
(C::NATP-OF-OBJDESIGN-AUTO->FRAME)
(C::OBJDESIGN-AUTO->FRAME$INLINE-OF-OBJDESIGN-FIX-X
 (105 35 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (70 70 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (33 11 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (30 30 (:TYPE-PRESCRIPTION NATP))
 (22 22 (:TYPE-PRESCRIPTION C::IDENTP))
 )
(C::OBJDESIGN-AUTO->FRAME$INLINE-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-AUTO->FRAME-WHEN-WRONG-KIND
 (2 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 )
(C::OBJDESIGN-AUTO->SCOPE$INLINE)
(C::NATP-OF-OBJDESIGN-AUTO->SCOPE)
(C::OBJDESIGN-AUTO->SCOPE$INLINE-OF-OBJDESIGN-FIX-X
 (105 35 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (70 70 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (33 11 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (30 30 (:TYPE-PRESCRIPTION NATP))
 (22 22 (:TYPE-PRESCRIPTION C::IDENTP))
 )
(C::OBJDESIGN-AUTO->SCOPE$INLINE-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-AUTO->SCOPE-WHEN-WRONG-KIND
 (2 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 )
(C::OBJDESIGN-AUTO)
(C::RETURN-TYPE-OF-OBJDESIGN-AUTO
 (12 4 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (6 2 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (4 4 (:TYPE-PRESCRIPTION C::IDENTP))
 )
(C::OBJDESIGN-AUTO->NAME-OF-OBJDESIGN-AUTO)
(C::OBJDESIGN-AUTO->FRAME-OF-OBJDESIGN-AUTO
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(C::OBJDESIGN-AUTO->SCOPE-OF-OBJDESIGN-AUTO
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(C::OBJDESIGN-AUTO-OF-FIELDS
 (8 8 (:TYPE-PRESCRIPTION NATP))
 (3 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::OBJDESIGN-FIX-WHEN-AUTO
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (3 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::EQUAL-OF-OBJDESIGN-AUTO
 (5 5 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(C::OBJDESIGN-AUTO-OF-IDENT-FIX-NAME
 (8 4 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(C::OBJDESIGN-AUTO-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::OBJDESIGN-AUTO-OF-NFIX-FRAME
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 2 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (2 2 (:TYPE-PRESCRIPTION C::IDENTP))
 )
(C::OBJDESIGN-AUTO-NAT-EQUIV-CONGRUENCE-ON-FRAME)
(C::OBJDESIGN-AUTO-OF-NFIX-SCOPE
 (4 4 (:TYPE-PRESCRIPTION NATP))
 (4 2 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (2 2 (:TYPE-PRESCRIPTION C::IDENTP))
 )
(C::OBJDESIGN-AUTO-NAT-EQUIV-CONGRUENCE-ON-SCOPE)
(C::OBJDESIGN-ALLOC->GET$INLINE)
(C::ADDRESSP-OF-OBJDESIGN-ALLOC->GET
 (3 1 (:REWRITE C::ADDRESS-FIX-WHEN-ADDRESSP))
 )
(C::OBJDESIGN-ALLOC->GET$INLINE-OF-OBJDESIGN-FIX-X
 (12 4 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (8 8 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::OBJDESIGN-ALLOC->GET$INLINE-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-ALLOC->GET-WHEN-WRONG-KIND
 (6 2 (:REWRITE C::ADDRESS-FIX-WHEN-ADDRESSP))
 (4 4 (:TYPE-PRESCRIPTION C::ADDRESSP))
 )
(C::OBJDESIGN-ALLOC)
(C::RETURN-TYPE-OF-OBJDESIGN-ALLOC
 (6 2 (:REWRITE C::ADDRESS-FIX-WHEN-ADDRESSP))
 (4 4 (:TYPE-PRESCRIPTION C::ADDRESSP))
 )
(C::OBJDESIGN-ALLOC->GET-OF-OBJDESIGN-ALLOC)
(C::OBJDESIGN-ALLOC-OF-FIELDS
 (3 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::OBJDESIGN-FIX-WHEN-ALLOC
 (3 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::EQUAL-OF-OBJDESIGN-ALLOC)
(C::OBJDESIGN-ALLOC-OF-ADDRESS-FIX-GET)
(C::OBJDESIGN-ALLOC-ADDRESS-EQUIV-CONGRUENCE-ON-GET)
(C::OBJDESIGN-ELEMENT->SUPER$INLINE)
(C::OBJDESIGNP-OF-OBJDESIGN-ELEMENT->SUPER
 (6 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 )
(C::OBJDESIGN-ELEMENT->SUPER$INLINE-OF-OBJDESIGN-FIX-X
 (3 1 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(C::OBJDESIGN-ELEMENT->SUPER$INLINE-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-ELEMENT->SUPER-WHEN-WRONG-KIND)
(C::OBJDESIGN-ELEMENT->INDEX$INLINE)
(C::NATP-OF-OBJDESIGN-ELEMENT->INDEX)
(C::OBJDESIGN-ELEMENT->INDEX$INLINE-OF-OBJDESIGN-FIX-X
 (138 46 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (92 92 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (8 8 (:TYPE-PRESCRIPTION NATP))
 )
(C::OBJDESIGN-ELEMENT->INDEX$INLINE-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-ELEMENT->INDEX-WHEN-WRONG-KIND
 (2 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 )
(C::OBJDESIGN-ELEMENT)
(C::RETURN-TYPE-OF-OBJDESIGN-ELEMENT
 (184 2 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (112 112 (:TYPE-PRESCRIPTION LEN))
 (100 28 (:REWRITE FTY::EQUAL-OF-LEN))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (10 10 (:TYPE-PRESCRIPTION NATP))
 (8 8 (:TYPE-PRESCRIPTION C::IDENTP))
 (6 2 (:REWRITE TMP-DEFTYPES-NFIX-WHEN-NATP))
 (2 2 (:TYPE-PRESCRIPTION C::ADDRESSP))
 )
(C::OBJDESIGN-ELEMENT->SUPER-OF-OBJDESIGN-ELEMENT
 (27 6 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (12 12 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (9 9 (:TYPE-PRESCRIPTION C::OBJDESIGN-ELEMENT))
 )
(C::OBJDESIGN-ELEMENT->INDEX-OF-OBJDESIGN-ELEMENT
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(C::OBJDESIGN-ELEMENT-OF-FIELDS
 (7 3 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (4 4 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (4 4 (:TYPE-PRESCRIPTION NATP))
 )
(C::OBJDESIGN-FIX-WHEN-ELEMENT
 (7 3 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (4 4 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(C::EQUAL-OF-OBJDESIGN-ELEMENT
 (3 3 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(C::OBJDESIGN-ELEMENT-OF-OBJDESIGN-FIX-SUPER)
(C::OBJDESIGN-ELEMENT-OBJDESIGN-EQUIV-CONGRUENCE-ON-SUPER)
(C::OBJDESIGN-ELEMENT-OF-NFIX-INDEX
 (4 2 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION NATP))
 )
(C::OBJDESIGN-ELEMENT-NAT-EQUIV-CONGRUENCE-ON-INDEX)
(C::OBJDESIGN-MEMBER->SUPER$INLINE)
(C::OBJDESIGNP-OF-OBJDESIGN-MEMBER->SUPER
 (6 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 )
(C::OBJDESIGN-MEMBER->SUPER$INLINE-OF-OBJDESIGN-FIX-X
 (3 1 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (2 2 (:TYPE-PRESCRIPTION C::IDENTP))
 )
(C::OBJDESIGN-MEMBER->SUPER$INLINE-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-MEMBER->SUPER-WHEN-WRONG-KIND)
(C::OBJDESIGN-MEMBER->NAME$INLINE)
(C::IDENTP-OF-OBJDESIGN-MEMBER->NAME
 (3 1 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 )
(C::OBJDESIGN-MEMBER->NAME$INLINE-OF-OBJDESIGN-FIX-X
 (15 5 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (10 10 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::OBJDESIGN-MEMBER->NAME$INLINE-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-MEMBER->NAME-WHEN-WRONG-KIND
 (6 2 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (4 4 (:TYPE-PRESCRIPTION C::IDENTP))
 )
(C::OBJDESIGN-MEMBER)
(C::RETURN-TYPE-OF-OBJDESIGN-MEMBER
 (184 2 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (112 112 (:TYPE-PRESCRIPTION LEN))
 (100 28 (:REWRITE FTY::EQUAL-OF-LEN))
 (12 12 (:TYPE-PRESCRIPTION C::IDENTP))
 (10 10 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (6 2 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (2 2 (:TYPE-PRESCRIPTION C::ADDRESSP))
 )
(C::OBJDESIGN-MEMBER->SUPER-OF-OBJDESIGN-MEMBER
 (27 6 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (12 12 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (9 9 (:TYPE-PRESCRIPTION C::OBJDESIGN-MEMBER))
 )
(C::OBJDESIGN-MEMBER->NAME-OF-OBJDESIGN-MEMBER)
(C::OBJDESIGN-MEMBER-OF-FIELDS
 (7 3 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (4 4 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::OBJDESIGN-FIX-WHEN-MEMBER
 (7 3 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (4 4 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::EQUAL-OF-OBJDESIGN-MEMBER)
(C::OBJDESIGN-MEMBER-OF-OBJDESIGN-FIX-SUPER)
(C::OBJDESIGN-MEMBER-OBJDESIGN-EQUIV-CONGRUENCE-ON-SUPER)
(C::OBJDESIGN-MEMBER-OF-IDENT-FIX-NAME
 (4 2 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::OBJDESIGN-MEMBER-IDENT-EQUIV-CONGRUENCE-ON-NAME)
(C::OBJDESIGN-FIX-REDEF
 (18 6 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (12 12 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 )
(C::OBJDESIGN-COUNT
 (8 4 (:REWRITE C::OBJDESIGN-FIX-WHEN-STATIC))
 (8 4 (:REWRITE C::OBJDESIGN-FIX-WHEN-AUTO))
 (8 4 (:REWRITE C::OBJDESIGN-FIX-WHEN-ALLOC))
 )
(C::NATP-OF-OBJDESIGN-COUNT)
(C::OBJDESIGN-COUNT)
(C::OBJDESIGN-COUNT-OF-OBJDESIGN-FIX-X
 (3 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-STATIC))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-MEMBER))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-ELEMENT))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-AUTO))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-ALLOC))
 )
(C::OBJDESIGN-COUNT-OBJDESIGN-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-COUNT-OF-OBJDESIGN-ELEMENT
 (5 5 (:TYPE-PRESCRIPTION C::OBJDESIGN-KIND$INLINE))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-STATIC))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-MEMBER))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-ELEMENT))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-AUTO))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-ALLOC))
 )
(C::OBJDESIGN-COUNT-OF-OBJDESIGN-ELEMENT->SUPER)
(C::OBJDESIGN-COUNT-OF-OBJDESIGN-MEMBER
 (5 5 (:TYPE-PRESCRIPTION C::OBJDESIGN-KIND$INLINE))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-STATIC))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-MEMBER))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-ELEMENT))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-AUTO))
 (2 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-ALLOC))
 )
(C::OBJDESIGN-COUNT-OF-OBJDESIGN-MEMBER->SUPER)
(C::OBJDESIGN-OPTIONP)
(C::CONSP-WHEN-OBJDESIGN-OPTIONP)
(C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP)
(C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP)
(C::OBJDESIGN-OPTION-FIX$INLINE)
(C::OBJDESIGN-OPTIONP-OF-OBJDESIGN-OPTION-FIX
 (20 4 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (16 2 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 )
(C::OBJDESIGN-OPTION-FIX-WHEN-OBJDESIGN-OPTIONP
 (16 4 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (16 3 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 )
(C::OBJDESIGN-OPTION-FIX$INLINE
 (16 4 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (16 3 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT
 (5 1 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (2 1 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 )
(C::OBJDESIGN-OPTION-EQUIV$INLINE)
(C::OBJDESIGN-OPTION-EQUIV-IS-AN-EQUIVALENCE)
(C::OBJDESIGN-OPTION-EQUIV-IMPLIES-EQUAL-OBJDESIGN-OPTION-FIX-1)
(C::OBJDESIGN-OPTION-FIX-UNDER-OBJDESIGN-OPTION-EQUIV)
(C::EQUAL-OF-OBJDESIGN-OPTION-FIX-1-FORWARD-TO-OBJDESIGN-OPTION-EQUIV)
(C::EQUAL-OF-OBJDESIGN-OPTION-FIX-2-FORWARD-TO-OBJDESIGN-OPTION-EQUIV)
(C::OBJDESIGN-OPTION-EQUIV-OF-OBJDESIGN-OPTION-FIX-1-FORWARD)
(C::OBJDESIGN-OPTION-EQUIV-OF-OBJDESIGN-OPTION-FIX-2-FORWARD)
(C::DEFOPTION-LEMMA-OBJDESIGN-FIX-NONNIL)
(C::OBJDESIGN-OPTION-FIX-UNDER-IFF
 (8 1 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-OBJDESIGN-OPTIONP))
 (8 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (7 2 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (7 2 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (5 5 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (5 5 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTIONP))
 )
(C::OBJDESIGN-OPTION-EQUIV-REFINES-OBJDESIGN-EQUIV
 (48 6 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (34 8 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (22 22 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (22 8 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (18 18 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTIONP))
 (16 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-OBJDESIGN-OPTIONP))
 )
(C::OBJDESIGN-OPTION-NONE)
(C::RETURN-TYPE-OF-OBJDESIGN-OPTION-NONE)
(C::OBJDESIGN-OPTION-FIX-WHEN-NONE)
(C::EQUAL-OF-OBJDESIGN-OPTION-NONE
 (5 3 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (3 2 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (3 1 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-OBJDESIGN-OPTIONP))
 )
(C::OBJDESIGN-OPTION-SOME->VAL$INLINE
 (11 2 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (9 3 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 )
(C::OBJDESIGNP-OF-OBJDESIGN-OPTION-SOME->VAL)
(C::OBJDESIGN-OPTION-SOME->VAL$INLINE-OF-OBJDESIGN-OPTION-FIX-X
 (48 11 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (25 9 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (24 3 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-OBJDESIGN-OPTIONP))
 (23 23 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTIONP))
 (5 5 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (4 4 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTION-FIX$INLINE))
 (2 2 (:REWRITE C::OBJDESIGN-OPTIONP-OF-OBJDESIGN-OPTION-FIX))
 (2 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-UNDER-IFF))
 )
(C::OBJDESIGN-OPTION-SOME->VAL$INLINE-OBJDESIGN-OPTION-EQUIV-CONGRUENCE-ON-X)
(C::OBJDESIGN-OPTION-SOME->VAL-WHEN-WRONG-KIND)
(C::OBJDESIGN-OPTION-SOME
 (8 2 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (5 1 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (3 3 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTIONP))
 )
(C::RETURN-TYPE-OF-OBJDESIGN-OPTION-SOME)
(C::OBJDESIGN-OPTION-SOME->VAL-OF-OBJDESIGN-OPTION-SOME
 (6 3 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 )
(C::OBJDESIGN-OPTION-SOME-OF-FIELDS
 (11 3 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (8 3 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (7 1 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-OBJDESIGN-OPTIONP))
 (6 6 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTIONP))
 (1 1 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 )
(C::OBJDESIGN-OPTION-FIX-WHEN-SOME
 (11 3 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (8 3 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (8 1 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-OBJDESIGN-OPTIONP))
 (7 7 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTIONP))
 (1 1 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 )
(C::EQUAL-OF-OBJDESIGN-OPTION-SOME
 (33 17 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (22 19 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (4 4 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 )
(C::OBJDESIGN-OPTION-SOME-OF-OBJDESIGN-FIX-VAL
 (10 2 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (4 4 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTIONP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 )
(C::OBJDESIGN-OPTION-SOME-OBJDESIGN-EQUIV-CONGRUENCE-ON-VAL)
(C::OBJDESIGN-OPTION-FIX-REDEF
 (16 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-OBJDESIGN-OPTIONP))
 (10 2 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 (6 6 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTIONP))
 (4 4 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (4 2 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (2 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 )
(C::OBJECT-DISJOINTP)
(C::BOOLEANP-OF-OBJECT-DISJOINTP)
(C::OBJECT-DISJOINTP-COMMUTATIVE)
(C::OBJECT-DISJOINTP-OF-OBJDESIGN-FIX-OBJDES1
 (8 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (5 1 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTIONP))
 (2 1 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 )
(C::OBJECT-DISJOINTP-OBJDESIGN-EQUIV-CONGRUENCE-ON-OBJDES1)
(C::OBJECT-DISJOINTP-OF-OBJDESIGN-FIX-OBJDES2
 (8 1 (:REWRITE C::OBJDESIGN-FIX-WHEN-OBJDESIGNP))
 (5 1 (:REWRITE C::OBJDESIGNP-WHEN-OBJDESIGN-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::OBJDESIGNP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJDESIGN-OPTIONP))
 (2 1 (:REWRITE C::OBJDESIGN-OPTIONP-WHEN-OBJDESIGNP))
 )
(C::OBJECT-DISJOINTP-OBJDESIGN-EQUIV-CONGRUENCE-ON-OBJDES2)
