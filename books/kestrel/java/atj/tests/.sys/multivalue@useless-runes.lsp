(ADD-SUB)
(DIFF-TYPES
 (17 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-OCT-DIGIT-CHAR-LIST*P))
 (17 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-HEX-DIGIT-CHAR-LIST*P))
 (12 1 (:REWRITE STR::OCT-DIGIT-CHAR-LIST*P-OF-CONS))
 (12 1 (:REWRITE STR::HEX-DIGIT-CHAR-LIST*P-OF-CONS))
 (11 1 (:REWRITE STR::CHARACTER-LISTP-WHEN-DEC-DIGIT-CHAR-LIST*P))
 (8 1 (:REWRITE STR::DEC-DIGIT-CHAR-LIST*P-OF-CONS))
 (4 4 (:REWRITE STR::OCT-DIGIT-CHAR-P-WHEN-MEMBER-EQUAL-OF-OCT-DIGIT-CHAR-LIST*P))
 (4 4 (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-MEMBER-EQUAL-OF-HEX-DIGIT-CHAR-LIST*P))
 (4 2 (:REWRITE STR::OCT-DIGIT-CHAR-P-WHEN-NONZERO-OCT-DIGIT-CHAR-P))
 (4 2 (:REWRITE STR::HEX-DIGIT-CHAR-P-WHEN-NONZERO-HEX-DIGIT-CHAR-P))
 (4 2 (:REWRITE STR::DEC-DIGIT-CHAR-P-WHEN-NONZERO-DEC-DIGIT-CHAR-P))
 (3 3 (:TYPE-PRESCRIPTION STR::OCT-DIGIT-CHAR-P$INLINE))
 (3 3 (:TYPE-PRESCRIPTION STR::HEX-DIGIT-CHAR-P$INLINE))
 (3 3 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-P$INLINE))
 (2 2 (:TYPE-PRESCRIPTION STR::NONZERO-OCT-DIGIT-CHAR-P$INLINE))
 (2 2 (:TYPE-PRESCRIPTION STR::NONZERO-HEX-DIGIT-CHAR-P$INLINE))
 (2 2 (:TYPE-PRESCRIPTION STR::NONZERO-DEC-DIGIT-CHAR-P$INLINE))
 (2 2 (:REWRITE STR::OCT-DIGIT-CHAR-LIST*P-WHEN-SUBSETP-EQUAL))
 (2 2 (:REWRITE STR::HEX-DIGIT-CHAR-LIST*P-WHEN-SUBSETP-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION STR::OCT-DIGIT-CHAR-LIST*P))
 (1 1 (:TYPE-PRESCRIPTION STR::HEX-DIGIT-CHAR-LIST*P))
 (1 1 (:TYPE-PRESCRIPTION STR::DEC-DIGIT-CHAR-LIST*P))
 (1 1 (:REWRITE STR::OCT-DIGIT-CHAR-LIST*P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE STR::HEX-DIGIT-CHAR-LIST*P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE STR::DEC-DIGIT-CHAR-LIST*P-WHEN-NOT-CONSP))
 )
(ATJ-ADD-SUB-INPUT-X-AINTEGER)
(ATJ-ADD-SUB-INPUT-Y-AINTEGER)
(ATJ-ADD-SUB-OUTPUT-1-AINTEGER
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(ATJ-ADD-SUB-OUTPUT-0-AINTEGER
 (2 2 (:REWRITE DEFAULT-+-2))
 (2 2 (:REWRITE DEFAULT-+-1))
 (1 1 (:REWRITE DEFAULT-UNARY-MINUS))
 )
(ATJ-DIFF-TYPES-INPUT-C-ACHARACTER)
(ATJ-DIFF-TYPES-OUTPUT-2-ACHARACTER
 (1 1 (:REWRITE DEFAULT-CHAR-CODE))
 )
(ATJ-DIFF-TYPES-OUTPUT-1-ASTRING
 (1 1 (:REWRITE DEFAULT-CHAR-CODE))
 )
(ATJ-DIFF-TYPES-OUTPUT-0-AINTEGER
 (1 1 (:REWRITE DEFAULT-CHAR-CODE))
 )
