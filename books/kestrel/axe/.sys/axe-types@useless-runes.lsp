(MOST-GENERAL-TYPE)
(MOST-GENERAL-TYPEP)
(EMPTY-TYPE)
(EMPTY-TYPEP)
(BOOLEAN-TYPE$INLINE)
(BOOLEAN-TYPEP)
(BV-TYPEP)
(MAKE-BV-TYPE$INLINE
 (1 1 (:TYPE-PRESCRIPTION MAKE-BV-TYPE$INLINE))
 )
(BV-TYPEP-OF-MAKE-BV-TYPE
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 )
(NATP-OF-MAKE-BV-TYPE-TYPE)
(MAKE-BV-TYPE-TYPE-IFF
 (20 10 (:TYPE-PRESCRIPTION NATP-OF-MAKE-BV-TYPE-TYPE))
 (10 10 (:TYPE-PRESCRIPTION NATP))
 )
(<-OF-0-AND-MAKE-BV-TYPE
 (6 3 (:TYPE-PRESCRIPTION NATP-OF-MAKE-BV-TYPE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:TYPE-PRESCRIPTION MAKE-BV-TYPE$INLINE))
 )
(BV-TYPE-WIDTH$INLINE
 (1 1 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 )
(BV-TYPE-WIDTH-OF-MAKE-BV-TYPE
 (12 3 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 (6 3 (:TYPE-PRESCRIPTION NATP-OF-MAKE-BV-TYPE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 (3 3 (:TYPE-PRESCRIPTION MAKE-BV-TYPE$INLINE))
 )
(RATIONALP-OF-BV-TYPE-WIDTH
 (5 5 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 )
(NATP-OF-BV-TYPE-WIDTH
 (5 5 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 )
(LIST-TYPEP)
(MAKE-LIST-TYPE)
(LIST-TYPEP-OF-MAKE-LIST-TYPE
 (4 2 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-+-1))
 )
(LIST-TYPE-ELEMENT-TYPE)
(LIST-TYPE-LEN-TYPE)
(LIST-TYPE-LEN-TYPE-OF-MAKE-LIST-TYPE)
(LIST-TYPE-ELEMENT-TYPE-OF-MAKE-LIST-TYPE)
(AXE-TYPEP)
(NOT-AXE-TYPEP-OF-NIL)
(AXE-TYPEP-OF-MAKE-BV-TYPE)
(BV-ARRAY-TYPEP)
(BV-ARRAY-TYPEP-FORWARD-TO-LIST-TYPEP)
(MAKE-BV-ARRAY-TYPE
 (6 3 (:TYPE-PRESCRIPTION NATP-OF-MAKE-BV-TYPE-TYPE))
 (3 3 (:TYPE-PRESCRIPTION MAKE-BV-TYPE$INLINE))
 )
(LIST-TYPEP-OF-MAKE-BV-ARRAY-TYPE)
(AXE-TYPEP-OF-MAKE-BV-ARRAY-TYPE)
(BV-ARRAY-TYPE-ELEMENT-WIDTH
 (10 5 (:TYPE-PRESCRIPTION NATP-OF-BV-TYPE-WIDTH))
 (5 5 (:TYPE-PRESCRIPTION BV-TYPEP))
 (5 5 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 )
(BV-ARRAY-TYPE-ELEMENT-WIDTH-OF-MAKE-BV-ARRAY-TYPE)
(NATP-OF-BV-TYPE-ELEMENT-WIDTH
 (1 1 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 )
(BV-ARRAY-TYPE-LEN)
(NATP-OF-BV-ARRAY-TYPE-LEN)
(BV-ARRAY-TYPE-LEN-OF-MAKE-BV-ARRAY-TYPE)
(NOT-BV-ARRAY-TYPEP-OF-MAKE-BV-TYPE)
(UNION-TYPES
 (14 14 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 )
(AXE-TYPEP-OF-UNION-TYPES
 (2343 2343 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 (967 375 (:REWRITE DEFAULT-<-1))
 (703 375 (:REWRITE DEFAULT-<-2))
 )
(INTERSECT-TYPES
 (24 24 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 )
(INTERSECT-TYPES-SAFE
 (24 24 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 (8 4 (:REWRITE DEFAULT-<-2))
 (8 4 (:REWRITE DEFAULT-<-1))
 )
(AXE-TYPEP-OF-INTERSECT-TYPES-SAFE
 (58 58 (:TYPE-PRESCRIPTION BV-TYPE-WIDTH$INLINE))
 (14 6 (:REWRITE DEFAULT-<-2))
 (14 6 (:REWRITE DEFAULT-<-1))
 )
(NOT-BV-ARRAY-TYPEP-WHEN-BV-TYPEP-CHEAP)
(NOT-BOOLEAN-TYPEP-WHEN-BV-TYPEP-CHEAP)
(NOT-BOOLEAN-TYPEP-WHEN-BV-ARRAY-TYPEP-CHEAP)
