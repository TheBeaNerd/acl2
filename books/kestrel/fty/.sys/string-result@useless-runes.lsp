(TMP-DEFTYPES-STRINGP-OF-STR-FIX$INLINE)
(STRING-RESULTP)
(CONSP-WHEN-STRING-RESULTP)
(STRING-RESULT-KIND$INLINE)
(STRING-RESULT-KIND-POSSIBILITIES)
(STRING-RESULT-FIX$INLINE)
(STRING-RESULTP-OF-STRING-RESULT-FIX
 (21 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (1 1 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(STRING-RESULT-FIX-WHEN-STRING-RESULTP
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(STRING-RESULT-FIX$INLINE
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(FTY::TMP-DEFFIXTYPE-IDEMPOTENT)
(STRING-RESULT-EQUIV$INLINE)
(STRING-RESULT-EQUIV-IS-AN-EQUIVALENCE)
(STRING-RESULT-EQUIV-IMPLIES-EQUAL-STRING-RESULT-FIX-1)
(STRING-RESULT-FIX-UNDER-STRING-RESULT-EQUIV)
(EQUAL-OF-STRING-RESULT-FIX-1-FORWARD-TO-STRING-RESULT-EQUIV)
(EQUAL-OF-STRING-RESULT-FIX-2-FORWARD-TO-STRING-RESULT-EQUIV)
(STRING-RESULT-EQUIV-OF-STRING-RESULT-FIX-1-FORWARD)
(STRING-RESULT-EQUIV-OF-STRING-RESULT-FIX-2-FORWARD)
(STRING-RESULT-KIND$INLINE-OF-STRING-RESULT-FIX-X
 (6 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (5 1 (:DEFINITION FTY::RESERRP))
 (2 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (1 1 (:REWRITE STRING-RESULT-FIX-WHEN-STRING-RESULTP))
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(STRING-RESULT-KIND$INLINE-STRING-RESULT-EQUIV-CONGRUENCE-ON-X)
(STRING-RESULT-OK->GET$INLINE)
(STRINGP-OF-STRING-RESULT-OK->GET)
(STRING-RESULT-OK->GET$INLINE-OF-STRING-RESULT-FIX-X
 (45 15 (:REWRITE STRING-RESULT-FIX-WHEN-STRING-RESULTP))
 (30 30 (:TYPE-PRESCRIPTION STRING-RESULTP))
 )
(STRING-RESULT-OK->GET$INLINE-STRING-RESULT-EQUIV-CONGRUENCE-ON-X)
(STRING-RESULT-OK->GET-WHEN-WRONG-KIND
 (2 2 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(STRING-RESULT-OK)
(RETURN-TYPE-OF-STRING-RESULT-OK
 (1 1 (:REWRITE STR-FIX-WHEN-STRINGP))
 )
(STRING-RESULT-OK->GET-OF-STRING-RESULT-OK)
(STRING-RESULT-OK-OF-FIELDS
 (3 1 (:REWRITE STRING-RESULT-FIX-WHEN-STRING-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION STRING-RESULTP))
 )
(STRING-RESULT-FIX-WHEN-OK
 (3 1 (:REWRITE STRING-RESULT-FIX-WHEN-STRING-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION STRING-RESULTP))
 )
(EQUAL-OF-STRING-RESULT-OK)
(STRING-RESULT-OK-OF-STR-FIX-GET)
(STRING-RESULT-OK-STREQV-CONGRUENCE-ON-GET)
(STRING-RESULT-ERR->GET$INLINE
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(RESERRP-OF-STRING-RESULT-ERR->GET
 (93 3 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (15 6 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 )
(STRING-RESULT-ERR->GET$INLINE-OF-STRING-RESULT-FIX-X
 (92 3 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (86 3 (:DEFINITION FTY::RESERRP))
 (64 12 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (32 32 (:TYPE-PRESCRIPTION STRIP-CARS))
 (21 3 (:DEFINITION ALISTP))
 (12 12 (:TYPE-PRESCRIPTION ALISTP))
 (12 4 (:REWRITE STRING-RESULT-FIX-WHEN-STRING-RESULTP))
 (8 8 (:TYPE-PRESCRIPTION STRING-RESULTP))
 (3 3 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (3 3 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (3 3 (:DEFINITION STRIP-CARS))
 )
(STRING-RESULT-ERR->GET$INLINE-STRING-RESULT-EQUIV-CONGRUENCE-ON-X)
(STRING-RESULT-ERR->GET-WHEN-WRONG-KIND
 (3 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (1 1 (:DEFINITION FTY::RESERRP))
 )
(STRING-RESULT-ERR
 (1 1 (:DEFINITION STRIP-CARS))
 (1 1 (:DEFINITION ALISTP))
 )
(RETURN-TYPE-OF-STRING-RESULT-ERR)
(STRING-RESULT-ERR->GET-OF-STRING-RESULT-ERR
 (50 8 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (36 1 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (34 1 (:DEFINITION FTY::RESERRP))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (9 1 (:DEFINITION ALISTP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (3 3 (:REWRITE FTY::EQUAL-OF-CONS-BY-EQUAL-OF-STRIP-CARS))
 (3 1 (:DEFINITION STRIP-CARS))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 )
(STRING-RESULT-ERR-OF-FIELDS
 (42 2 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (38 2 (:DEFINITION FTY::RESERRP))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (10 4 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (8 2 (:DEFINITION ALISTP))
 (3 1 (:REWRITE STRING-RESULT-FIX-WHEN-STRING-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION STRING-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (2 2 (:DEFINITION STRIP-CARS))
 )
(STRING-RESULT-FIX-WHEN-ERR
 (22 2 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (19 1 (:DEFINITION FTY::RESERRP))
 (10 10 (:TYPE-PRESCRIPTION STRIP-CARS))
 (5 2 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (4 4 (:TYPE-PRESCRIPTION ALISTP))
 (4 1 (:DEFINITION ALISTP))
 (3 1 (:REWRITE STRING-RESULT-FIX-WHEN-STRING-RESULTP))
 (2 2 (:TYPE-PRESCRIPTION STRING-RESULTP))
 (1 1 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (1 1 (:DEFINITION STRIP-CARS))
 )
(EQUAL-OF-STRING-RESULT-ERR
 (150 6 (:REWRITE FTY::RESERR-FIX-WHEN-RESERRP))
 (132 6 (:DEFINITION FTY::RESERRP))
 (52 4 (:REWRITE OMAP::ALISTP-WHEN-MAPP))
 (42 6 (:DEFINITION ALISTP))
 (29 23 (:REWRITE FTY::PROVE-EQUAL-OF-CONS-WHEN-FIRST-QUOTEP))
 (20 20 (:TYPE-PRESCRIPTION STRIP-CARS))
 (20 4 (:REWRITE OMAP::MFIX-IMPLIES-MAPP))
 (20 4 (:REWRITE OMAP::MAPP-WHEN-NOT-EMPTY))
 (18 18 (:REWRITE DEFAULT-CDR))
 (16 16 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (13 13 (:REWRITE DEFAULT-CAR))
 (12 6 (:DEFINITION STRIP-CARS))
 (10 2 (:REWRITE FTY::RESERRP-WHEN-RESERR-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION OMAP::MFIX))
 (8 8 (:TYPE-PRESCRIPTION OMAP::EMPTY))
 (8 8 (:TYPE-PRESCRIPTION ALISTP))
 (8 4 (:REWRITE OMAP::MFIX-WHEN-MAPP))
 (8 4 (:REWRITE OMAP::MAPP-NON-NIL-IMPLIES-NON-EMPTY))
 (4 4 (:TYPE-PRESCRIPTION FTY::RESERRP))
 (4 4 (:TYPE-PRESCRIPTION FTY::RESERR-OPTIONP))
 (4 2 (:REWRITE FTY::RESERR-OPTIONP-WHEN-RESERRP))
 )
(STRING-RESULT-ERR-OF-RESERR-FIX-GET)
(STRING-RESULT-ERR-RESERR-EQUIV-CONGRUENCE-ON-GET)
(STRING-RESULT-FIX-REDEF
 (9 3 (:REWRITE STRING-RESULT-FIX-WHEN-STRING-RESULTP))
 (6 6 (:TYPE-PRESCRIPTION STRING-RESULTP))
 )
(STRING-RESULTP-WHEN-STRINGP)
(STRING-RESULTP-WHEN-RESERRP)
(NOT-RESERRP-WHEN-STRINGP)
(STRINGP-WHEN-STRING-RESULTP-AND-NOT-RESERRP)
