(PRIME-FIX
 (1 1 (:TYPE-PRESCRIPTION PRIME-FIX))
 )
(PRIMEP-OF-PRIME-FIX
 (3 3 (:TYPE-PRESCRIPTION PRIME-FIX))
 )
(PRIME-FIX-WHEN-PRIMEP
 (19 19 (:TYPE-PRESCRIPTION PRIME-FIX))
 )
(POSP-OF-PRIME-FIX
 (38 2 (:REWRITE PRIME-FIX-WHEN-PRIMEP))
 (36 4 (:DEFINITION DM::LEAST-DIVISOR))
 (31 31 (:TYPE-PRESCRIPTION PRIME-FIX))
 (24 4 (:DEFINITION DM::DIVIDES))
 (12 4 (:REWRITE COMMUTATIVITY-OF-*))
 (10 9 (:REWRITE DEFAULT-<-2))
 (9 9 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE DEFAULT-*-2))
 (8 8 (:REWRITE DEFAULT-*-1))
 (2 2 (:TYPE-PRESCRIPTION DM::PRIMEP))
 )
