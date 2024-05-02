(GL::LOGHEAD-OF-INTEGER-LENGTH-NONNEG
 (1516 18 (:REWRITE LOGHEAD-IDENTITY))
 (1414 34 (:DEFINITION UNSIGNED-BYTE-P))
 (1264 26 (:DEFINITION INTEGER-RANGE-P))
 (769 19 (:REWRITE ZIP-OPEN))
 (710 5 (:REWRITE BITOPS::LOGBITP-UPPER-BOUND))
 (649 4 (:REWRITE IFIX-EQUAL-TO-NONZERO))
 (592 16 (:REWRITE UNSIGNED-BYTE-P-PLUS))
 (549 5 (:DEFINITION LOGBITP**))
 (461 8 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (441 6 (:DEFINITION BITMASKP**))
 (216 97 (:REWRITE DEFAULT-<-2))
 (216 44 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (185 11 (:DEFINITION BIT->BOOL$INLINE))
 (148 97 (:REWRITE DEFAULT-<-1))
 (140 128 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (138 138 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (136 136 (:TYPE-PRESCRIPTION BITP))
 (136 136 (:META CANCEL_PLUS-LESSP-CORRECT))
 (133 3 (:REWRITE BITOPS::LOGCONS-EQUAL-CONSTANT))
 (119 86 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (116 2 (:REWRITE INEQUALITY-WITH-NFIX-HYP-2))
 (114 22 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (107 13 (:LINEAR BITOPS::LOGCAR-BOUND))
 (101 39 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
 (100 24 (:REWRITE ZP-WHEN-GT-0))
 (92 92 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (78 39 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
 (59 24 (:REWRITE ZP-WHEN-INTEGERP))
 (55 24 (:REWRITE DEFAULT-+-2))
 (48 12 (:REWRITE <-0-+-NEGATIVE-1))
 (43 43 (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (41 41 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (35 5 (:REWRITE NEGP-WHEN-LESS-THAN-0))
 (34 34 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (34 34 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (34 30 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (34 4 (:REWRITE NFIX-POSITIVE-TO-NON-ZP))
 (33 33 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (33 33 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (30 30 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (24 24 (:REWRITE DEFAULT-+-1))
 (22 7 (:REWRITE NATP-WHEN-GTE-0))
 (21 21 (:REWRITE ZP-OPEN))
 (20 20 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (20 20 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (20 20 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (17 17 (:TYPE-PRESCRIPTION LOGBITP))
 (16 5 (:REWRITE NFIX-WHEN-NOT-NATP))
 (15 1 (:LINEAR BITOPS::INTEGER-LENGTH-EXPT-UPPER-BOUND-N))
 (13 1 (:REWRITE BFIX-WHEN-NOT-1))
 (12 12 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (12 12 (:REWRITE EXPONENTS-ADD))
 (10 10 (:LINEAR BITOPS::INTEGER-LENGTH-MONOTONIC))
 (8 8 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (7 7 (:REWRITE NATP-WHEN-INTEGERP))
 (6 2 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
 (5 5 (:TYPE-PRESCRIPTION ZIP))
 (5 5 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (5 5 (:LINEAR BITOPS::LOGBITP-UPPER-BOUND))
 (5 5 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-LESS-THAN-EXP))
 (5 5 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-GREATER-THAN-EXP))
 (5 5 (:LINEAR BITOPS::INTEGER-LENGTH-BOUNDED-BY-EXPT))
 (4 4 (:REWRITE INEQUALITY-WITH-NFIX-HYP-1))
 (4 4 (:REWRITE IFIX-EQUAL-TO-NONZERO-CONST))
 (3 1 (:REWRITE FOLD-CONSTS-IN-+))
 (2 1 (:REWRITE BFIX-WHEN-NOT-BITP))
 (2 1 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (2 1 (:REWRITE BFIX-WHEN-BITP))
 (2 1 (:REWRITE BFIX-WHEN-BIT->BOOL))
 )
(GL::INTEGER-LENGTH-LTE-BY-COMPARE-NONNEG
 (853 7 (:REWRITE BITOPS::LOGBITP-UPPER-BOUND))
 (728 3 (:DEFINITION LOGBITP**))
 (330 3 (:REWRITE ZP-WHEN-GT-0))
 (322 7 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (301 7 (:DEFINITION BITMASKP**))
 (219 3 (:LINEAR BITOPS::INTEGER-LENGTH-OF-LOGCDR-WEAK))
 (199 39 (:REWRITE DEFAULT-+-2))
 (195 33 (:REWRITE ZIP-OPEN))
 (190 62 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (180 3 (:REWRITE ZP-WHEN-INTEGERP))
 (146 10 (:DEFINITION BIT->BOOL$INLINE))
 (144 144 (:TYPE-PRESCRIPTION BITP))
 (132 3 (:LINEAR BITOPS::INTEGER-LENGTH-OF-LOGCDR-STRONG))
 (122 122 (:TYPE-PRESCRIPTION NATP))
 (92 20 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (67 67 (:TYPE-PRESCRIPTION LOGCAR-TYPE))
 (66 10 (:LINEAR BITOPS::LOGCAR-BOUND))
 (55 23 (:REWRITE DEFAULT-<-2))
 (40 40 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (40 40 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (39 39 (:REWRITE DEFAULT-+-1))
 (38 23 (:REWRITE DEFAULT-<-1))
 (35 35 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (21 3 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
 (19 19 (:TYPE-PRESCRIPTION LOGBITP))
 (16 16 (:LINEAR BITOPS::INTEGER-LENGTH-MONOTONIC))
 (16 4 (:REWRITE NATP-WHEN-GTE-0))
 (13 9 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (12 3 (:REWRITE NEGP-WHEN-LESS-THAN-0))
 (11 4 (:REWRITE NATP-WHEN-INTEGERP))
 (8 8 (:LINEAR BITOPS::LOGBITP-UPPER-BOUND))
 (8 8 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-LESS-THAN-EXP))
 (8 8 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-GREATER-THAN-EXP))
 (8 8 (:LINEAR BITOPS::INTEGER-LENGTH-BOUNDED-BY-EXPT))
 (7 4 (:REWRITE NATP-RW))
 (3 3 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:TYPE-PRESCRIPTION BITOPS::LOGXOR-NATP-TYPE-2))
 (1 1 (:TYPE-PRESCRIPTION BITOPS::LOGXOR-NATP-TYPE-1))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE BITOPS::LOGCDR->-CONST))
 (1 1 (:REWRITE BITOPS::LOGCDR-<-CONST))
 )
(GL::INTEGER-LENGTH-LTE-BY-COMPARE-NEG
 (1203 8 (:REWRITE BITOPS::LOGBITP-UPPER-BOUND))
 (922 4 (:DEFINITION LOGBITP**))
 (677 8 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (653 8 (:DEFINITION BITMASKP**))
 (592 336 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (361 26 (:REWRITE ZIP-OPEN))
 (291 4 (:REWRITE ZP-WHEN-INTEGERP))
 (275 4 (:REWRITE ZP-WHEN-GT-0))
 (243 243 (:TYPE-PRESCRIPTION NATP))
 (199 62 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (187 46 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (186 12 (:DEFINITION BIT->BOOL$INLINE))
 (169 2 (:LINEAR BITOPS::INTEGER-LENGTH-OF-LOGCDR-WEAK))
 (141 23 (:REWRITE DEFAULT-+-2))
 (132 24 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (129 129 (:TYPE-PRESCRIPTION BITP))
 (90 12 (:LINEAR BITOPS::LOGCAR-BOUND))
 (90 8 (:LINEAR BITOPS::INTEGER-LENGTH-LESS))
 (80 80 (:TYPE-PRESCRIPTION LOGCAR-TYPE))
 (76 35 (:REWRITE DEFAULT-<-2))
 (51 35 (:REWRITE DEFAULT-<-1))
 (50 50 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (50 50 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (40 40 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (27 6 (:REWRITE NATP-WHEN-INTEGERP))
 (26 17 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (25 4 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
 (24 6 (:REWRITE NATP-WHEN-GTE-0))
 (23 23 (:REWRITE DEFAULT-+-1))
 (20 20 (:TYPE-PRESCRIPTION LOGBITP))
 (16 16 (:LINEAR BITOPS::INTEGER-LENGTH-MONOTONIC))
 (15 6 (:REWRITE NATP-RW))
 (10 2 (:LINEAR BITOPS::INTEGER-LENGTH-OF-LOGCDR-STRONG))
 (8 8 (:LINEAR BITOPS::LOGBITP-UPPER-BOUND))
 (8 8 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-LESS-THAN-EXP))
 (8 8 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-GREATER-THAN-EXP))
 (8 8 (:LINEAR BITOPS::INTEGER-LENGTH-BOUNDED-BY-EXPT))
 (4 4 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (4 1 (:REWRITE NEGP-WHEN-LESS-THAN-0))
 (2 2 (:TYPE-PRESCRIPTION POSP))
 (2 2 (:REWRITE ZP-OPEN))
 (1 1 (:TYPE-PRESCRIPTION BITOPS::LOGXOR-NATP-TYPE-2))
 (1 1 (:TYPE-PRESCRIPTION BITOPS::LOGXOR-NATP-TYPE-1))
 (1 1 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (1 1 (:REWRITE NEGP-WHEN-INTEGERP))
 (1 1 (:REWRITE BITOPS::LOGCDR-<-CONST))
 )
(GL::FLOOR-OF-NEGATIONS
 (218 4 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (154 8 (:REWRITE NIQ-TYPE . 3))
 (90 12 (:REWRITE COMMUTATIVITY-OF-*))
 (62 62 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (56 8 (:REWRITE NIQ-TYPE . 2))
 (56 4 (:REWRITE DISTRIBUTIVITY))
 (37 30 (:REWRITE DEFAULT-*-1))
 (36 30 (:REWRITE DEFAULT-*-2))
 (28 20 (:REWRITE /R-WHEN-ABS-NUMERATOR=1))
 (26 20 (:REWRITE DEFAULT-+-2))
 (22 20 (:REWRITE DEFAULT-+-1))
 (20 14 (:REWRITE DEFAULT-<-1))
 (15 10 (:REWRITE DEFAULT-UNARY-/))
 (14 14 (:REWRITE DEFAULT-<-2))
 (14 14 (:META CANCEL_PLUS-LESSP-CORRECT))
 (14 12 (:REWRITE DEFAULT-UNARY-MINUS))
 (8 8 (:REWRITE RATIONAL-IMPLIES2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (5 5 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (5 5 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (5 4 (:REWRITE DEFAULT-NUMERATOR))
 (4 4 (:REWRITE RATIONALP-*))
 (4 4 (:REWRITE NUMERATOR-WHEN-INTEGERP))
 (4 4 (:REWRITE NFIX-WHEN-NOT-NATP))
 (4 4 (:REWRITE NFIX-WHEN-NATP))
 (4 4 (:REWRITE INVERSE-OF-*))
 (4 4 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (4 4 (:REWRITE IFIX-WHEN-INTEGERP))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 2 (:REWRITE DEFAULT-DENOMINATOR))
 (2 2 (:REWRITE INTEGERP==>DENOMINATOR=1))
 )
(GL::LOGEXT-OF-INTEGER-LENGTH-BOUND
 (440 4 (:REWRITE LOGEXT-IDENTITY))
 (410 4 (:DEFINITION SIGNED-BYTE-P))
 (352 4 (:DEFINITION INTEGER-RANGE-P))
 (350 350 (:TYPE-PRESCRIPTION BITOPS::INTEGER-LENGTH-TYPE-PRESCRIPTION-STRONG))
 (286 143 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (248 2 (:REWRITE BITOPS::SIGNED-BYTE-P-OF-LOGCDR))
 (209 16 (:REWRITE ZIP-OPEN))
 (114 57 (:REWRITE DEFAULT-<-2))
 (114 38 (:REWRITE DEFAULT-+-2))
 (107 3 (:REWRITE BITOPS::LOGCONS-EQUAL-CONSTANT))
 (103 57 (:REWRITE DEFAULT-<-1))
 (96 32 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (90 45 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
 (90 45 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
 (90 45 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NATP))
 (76 76 (:TYPE-PRESCRIPTION BITP))
 (72 52 (:REWRITE EXPT-WITH-VIOLATED-GUARDS))
 (63 63 (:META CANCEL_PLUS-LESSP-CORRECT))
 (48 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (46 46 (:TYPE-PRESCRIPTION POSP))
 (44 44 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (44 44 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (38 38 (:REWRITE DEFAULT-+-1))
 (30 25 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (28 28 (:LINEAR EXPT-IS-INCREASING-FOR-BASE>1))
 (28 7 (:REWRITE NATP-WHEN-GTE-0))
 (21 6 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (20 20 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (20 20 (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS))
 (16 16 (:LINEAR BITOPS::INTEGER-LENGTH-MONOTONIC))
 (16 4 (:REWRITE DEFAULT-*-2))
 (14 14 (:LINEAR BITOPS::EXPT-2-LOWER-BOUND-BY-LOGBITP))
 (13 1 (:REWRITE BFIX-WHEN-NOT-1))
 (8 8 (:LINEAR BITOPS::LOGBITP-UPPER-BOUND))
 (8 8 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-LESS-THAN-EXP))
 (8 8 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-GREATER-THAN-EXP))
 (8 8 (:LINEAR BITOPS::INTEGER-LENGTH-BOUNDED-BY-EXPT))
 (7 7 (:REWRITE NATP-WHEN-INTEGERP))
 (6 6 (:REWRITE ZP-WHEN-INTEGERP))
 (6 6 (:REWRITE ZP-OPEN))
 (6 6 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (5 5 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (5 5 (:REWRITE IFIX-EQUAL-TO-NONZERO-CONST))
 (5 1 (:LINEAR BITOPS::INTEGER-LENGTH-OF-LOGCDR-STRONG))
 (4 4 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (4 4 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (4 4 (:REWRITE DEFAULT-*-1))
 (4 4 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (4 2 (:REWRITE MINUS-CANCELLATION-ON-LEFT))
 (3 3 (:TYPE-PRESCRIPTION ZIP))
 (3 3 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (2 2 (:DEFINITION FIX))
 (2 1 (:REWRITE BFIX-WHEN-NOT-BITP))
 (2 1 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (2 1 (:REWRITE BFIX-WHEN-BITP))
 (2 1 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (1 1 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 )
(GL::MOD-OF-NEGATIVES
 (52 52 (:TYPE-PRESCRIPTION MOD-TYPE . 4))
 (52 52 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (52 52 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (52 52 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (44 44 (:META CANCEL_PLUS-LESSP-CORRECT))
 (32 8 (:REWRITE <-MINUS-ZERO))
 (32 8 (:REWRITE <-0-MINUS))
 (28 28 (:REWRITE DEFAULT-<-2))
 (28 28 (:REWRITE DEFAULT-<-1))
 (24 8 (:REWRITE DEFAULT-UNARY-MINUS))
 (24 4 (:LINEAR MOD-BOUNDED-BY-MODULUS))
 (20 10 (:REWRITE DEFAULT-*-2))
 (20 10 (:REWRITE DEFAULT-*-1))
 (18 3 (:REWRITE DEFAULT-+-2))
 (15 2 (:REWRITE MOD-=-0 . 2))
 (12 12 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 2))
 (12 12 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (12 12 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (12 12 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (12 2 (:LINEAR MOD-TYPE . 4))
 (12 2 (:LINEAR MOD-TYPE . 3))
 (12 2 (:LINEAR MOD-TYPE . 2))
 (12 2 (:LINEAR MOD-TYPE . 1))
 (10 2 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (10 2 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (10 2 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (10 2 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (8 2 (:REWRITE FLOOR-TYPE-4 . 3))
 (8 2 (:REWRITE FLOOR-TYPE-4 . 2))
 (8 2 (:REWRITE FLOOR-TYPE-3 . 3))
 (8 2 (:REWRITE FLOOR-TYPE-3 . 2))
 (8 2 (:REWRITE FLOOR-=-X/Y . 3))
 (8 2 (:REWRITE FLOOR-=-X/Y . 2))
 (7 1 (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
 (6 6 (:REWRITE DEFAULT-UNARY-/))
 (6 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:REWRITE RECIPROCAL-MINUS))
 (2 2 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (1 1 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (1 1 (:META CANCEL_PLUS-EQUAL-CORRECT))
 )
(GL::INTEGER-LENGTH-OF-MOD
 (215 6 (:DEFINITION INTEGER-LENGTH**))
 (148 148 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (148 148 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (102 1 (:REWRITE NATP-RW))
 (63 1 (:REWRITE NATP-WHEN-GTE-0))
 (56 6 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (51 3 (:REWRITE ZIP-OPEN))
 (50 6 (:REWRITE DEFAULT-+-2))
 (38 38 (:REWRITE DEFAULT-<-2))
 (38 38 (:REWRITE DEFAULT-<-1))
 (38 38 (:META CANCEL_PLUS-LESSP-CORRECT))
 (37 7 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (34 10 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (34 10 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (34 10 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (34 10 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (34 10 (:REWRITE MOD-=-0 . 2))
 (32 4 (:REWRITE MOD-TYPE))
 (24 6 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (18 18 (:REWRITE DEFAULT-UNARY-/))
 (18 18 (:REWRITE DEFAULT-*-2))
 (18 18 (:REWRITE DEFAULT-*-1))
 (16 1 (:REWRITE NATP-WHEN-INTEGERP))
 (12 3 (:REWRITE MOD-=-0 . 1))
 (10 10 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (10 4 (:LINEAR MOD-TYPE . 1))
 (8 8 (:TYPE-PRESCRIPTION BITP))
 (7 4 (:LINEAR MOD-TYPE . 2))
 (6 6 (:REWRITE DEFAULT-+-1))
 (6 6 (:LINEAR BITOPS::INTEGER-LENGTH-MONOTONIC))
 (3 3 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (3 3 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (3 3 (:LINEAR BITOPS::LOGBITP-UPPER-BOUND))
 (3 3 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-LESS-THAN-EXP))
 (3 3 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-GREATER-THAN-EXP))
 (3 3 (:LINEAR BITOPS::INTEGER-LENGTH-BOUNDED-BY-EXPT))
 (2 2 (:TYPE-PRESCRIPTION LOGCDR-TYPE))
 (1 1 (:TYPE-PRESCRIPTION NATP))
 )
(GL::INTEGER-LENGTH-OF-PLUS-1
 (4890 10 (:REWRITE BITOPS::LOGBITP-UPPER-BOUND))
 (3900 20 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (3843 23 (:DEFINITION BITMASKP**))
 (2946 10 (:DEFINITION LOGBITP**))
 (2732 1294 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (1481 1481 (:TYPE-PRESCRIPTION NATP))
 (1092 218 (:REWRITE DEFAULT-+-2))
 (1049 20 (:REWRITE BITOPS::LOGCAR-OF-+))
 (910 164 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (747 20 (:DEFINITION LOGXOR**))
 (724 51 (:REWRITE BFIX-WHEN-NOT-1))
 (616 131 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (576 31 (:REWRITE SIMPLIFY-BIT-FUNCTIONS))
 (567 20 (:REWRITE BITOPS::LOGCONS-B-0))
 (428 218 (:REWRITE DEFAULT-+-1))
 (394 394 (:TYPE-PRESCRIPTION BITP))
 (352 47 (:LINEAR BITOPS::LOGCAR-BOUND))
 (254 254 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (254 254 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (237 15 (:REWRITE NATP-WHEN-INTEGERP))
 (197 10 (:REWRITE BITOPS::BIT->BOOL-OF-B-NOT))
 (197 10 (:REWRITE BITOPS::B-NOT-EQUAL-1))
 (192 15 (:REWRITE NATP-RW))
 (188 23 (:DEFINITION BIT->BOOL$INLINE))
 (174 15 (:REWRITE NATP-WHEN-GTE-0))
 (172 86 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-2))
 (172 86 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-POSP-1))
 (172 86 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NEGP))
 (172 86 (:TYPE-PRESCRIPTION BITOPS::LOGCONS-NATP))
 (162 72 (:REWRITE DEFAULT-<-1))
 (150 150 (:TYPE-PRESCRIPTION BITP-OF-B-XOR))
 (144 144 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (117 72 (:REWRITE DEFAULT-<-2))
 (106 106 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (102 102 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (102 51 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (102 51 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (86 86 (:TYPE-PRESCRIPTION NEGP))
 (82 41 (:REWRITE BFIX-WHEN-NOT-BITP))
 (82 41 (:REWRITE BFIX-WHEN-BITP))
 (81 81 (:META CANCEL_PLUS-LESSP-CORRECT))
 (81 9 (:REWRITE BITOPS::LOGCDR-<-CONST))
 (70 70 (:TYPE-PRESCRIPTION BITP-OF-B-NOT))
 (50 50 (:TYPE-PRESCRIPTION LOGBITP))
 (47 47 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (40 20 (:LINEAR BITOPS::B-XOR-BOUND))
 (32 32 (:LINEAR BITOPS::INTEGER-LENGTH-MONOTONIC))
 (30 30 (:TYPE-PRESCRIPTION BITP-OF-B-AND))
 (20 10 (:LINEAR BITOPS::B-NOT-BOUND))
 (17 17 (:REWRITE-QUOTED-CONSTANT NFIX-UNDER-NAT-EQUIV))
 (17 17 (:REWRITE-QUOTED-CONSTANT BFIX-UNDER-BIT-EQUIV))
 (16 16 (:LINEAR BITOPS::LOGBITP-UPPER-BOUND))
 (16 16 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-LESS-THAN-EXP))
 (16 16 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-GREATER-THAN-EXP))
 (16 16 (:LINEAR BITOPS::INTEGER-LENGTH-BOUNDED-BY-EXPT))
 (15 15 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (10 10 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (10 10 (:REWRITE BITOPS::BXOR-TO-BNOT))
 )
(GL::INTEGER-LENGTH-OF-LOGNOT
 (6 6 (:TYPE-PRESCRIPTION BITOPS::INTEGER-LENGTH-TYPE-PRESCRIPTION-STRONG))
 (6 3 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
 (6 3 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NATP))
 (3 3 (:TYPE-PRESCRIPTION NEGP))
 (3 3 (:TYPE-PRESCRIPTION NATP))
 )
(GL::INTEGER-LENGTH-OF-ABS
 (257 257 (:TYPE-PRESCRIPTION BITOPS::INTEGER-LENGTH-TYPE-PRESCRIPTION-STRONG))
 (244 2 (:REWRITE BITOPS::LOGBITP-UPPER-BOUND))
 (184 4 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (172 4 (:DEFINITION BITMASKP**))
 (169 2 (:DEFINITION LOGBITP**))
 (150 80 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (122 3 (:LINEAR BITOPS::INTEGER-LENGTH-LESS))
 (94 22 (:REWRITE DEFAULT-+-2))
 (58 35 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (54 4 (:DEFINITION BIT->BOOL$INLINE))
 (44 44 (:TYPE-PRESCRIPTION BITP))
 (40 12 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (40 12 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (34 3 (:REWRITE NATP-WHEN-INTEGERP))
 (34 3 (:REWRITE NATP-WHEN-GTE-0))
 (34 3 (:REWRITE NATP-RW))
 (32 32 (:TYPE-PRESCRIPTION NATP))
 (32 32 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (32 6 (:LINEAR BITOPS::LOGCAR-BOUND))
 (30 22 (:REWRITE DEFAULT-+-1))
 (26 2 (:REWRITE BFIX-WHEN-NOT-1))
 (24 4 (:REWRITE FOLD-CONSTS-IN-+))
 (23 23 (:TYPE-PRESCRIPTION LOGCDR-TYPE))
 (23 12 (:REWRITE DEFAULT-<-1))
 (21 3 (:REWRITE <-+-NEGATIVE-0-2))
 (20 20 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (18 12 (:REWRITE DEFAULT-<-2))
 (15 15 (:META CANCEL_PLUS-LESSP-CORRECT))
 (10 10 (:TYPE-PRESCRIPTION LOGBITP))
 (10 5 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
 (10 5 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NATP))
 (10 2 (:REWRITE UNICITY-OF-0))
 (8 8 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (8 2 (:REWRITE EQUAL-MINUS-MINUS))
 (7 7 (:REWRITE DEFAULT-UNARY-MINUS))
 (6 6 (:LINEAR BITOPS::INTEGER-LENGTH-MONOTONIC))
 (5 5 (:TYPE-PRESCRIPTION NEGP))
 (4 4 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (4 2 (:REWRITE BFIX-WHEN-NOT-BITP))
 (4 2 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (4 2 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (3 3 (:LINEAR BITOPS::LOGBITP-UPPER-BOUND))
 (3 3 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-LESS-THAN-EXP))
 (3 3 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-GREATER-THAN-EXP))
 (3 3 (:LINEAR BITOPS::INTEGER-LENGTH-BOUNDED-BY-EXPT))
 (2 2 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (1 1 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 )
(GL::INTEGER-LENGTH-OF-BETWEEN-ABS-AND-MINUS-ABS
 (4619 68 (:REWRITE BITOPS::LOGBITP-UPPER-BOUND))
 (3845 26 (:DEFINITION LOGBITP**))
 (2781 73 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (2562 73 (:DEFINITION BITMASKP**))
 (1282 21 (:REWRITE ZP-WHEN-INTEGERP))
 (1164 94 (:DEFINITION BIT->BOOL$INLINE))
 (546 217 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (527 21 (:REWRITE ZP-WHEN-GT-0))
 (512 151 (:REWRITE DEFAULT-+-2))
 (484 107 (:LINEAR BITOPS::LOGCAR-BOUND))
 (453 453 (:TYPE-PRESCRIPTION BITP))
 (408 398 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (389 161 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (370 198 (:REWRITE DEFAULT-<-2))
 (365 365 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (297 198 (:REWRITE DEFAULT-<-1))
 (247 247 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (214 214 (:TYPE-PRESCRIPTION LOGBITP))
 (207 207 (:META CANCEL_PLUS-LESSP-CORRECT))
 (195 16 (:REWRITE BFIX-WHEN-NOT-1))
 (193 193 (:TYPE-PRESCRIPTION LOGCDR-TYPE))
 (185 151 (:REWRITE DEFAULT-+-1))
 (131 3 (:REWRITE BITOPS::LOGCAR-OF-+))
 (122 3 (:DEFINITION LOGXOR**))
 (101 3 (:REWRITE BITOPS::LOGCONS-B-0))
 (96 96 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (69 69 (:REWRITE DEFAULT-UNARY-MINUS))
 (60 4 (:REWRITE NATP-WHEN-INTEGERP))
 (60 4 (:REWRITE NATP-RW))
 (50 4 (:REWRITE NATP-WHEN-GTE-0))
 (47 3 (:REWRITE BITOPS::BIT->BOOL-OF-B-NOT))
 (47 3 (:REWRITE BITOPS::B-NOT-EQUAL-1))
 (42 6 (:REWRITE <-+-NEGATIVE-0-2))
 (41 21 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
 (38 32 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (32 32 (:TYPE-PRESCRIPTION BIT->BOOL$INLINE))
 (32 16 (:REWRITE BFIX-WHEN-NOT-BIT->BOOL))
 (32 16 (:REWRITE BFIX-WHEN-BIT->BOOL))
 (26 26 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (26 13 (:REWRITE BFIX-WHEN-NOT-BITP))
 (22 11 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NEGP))
 (22 11 (:TYPE-PRESCRIPTION BITOPS::LOGNOT-NATP))
 (21 21 (:TYPE-PRESCRIPTION BITP-OF-B-NOT))
 (16 4 (:REWRITE EQUAL-MINUS-MINUS))
 (12 12 (:LINEAR BITOPS::LOGBITP-UPPER-BOUND))
 (12 12 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-LESS-THAN-EXP))
 (12 12 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-GREATER-THAN-EXP))
 (12 12 (:LINEAR BITOPS::INTEGER-LENGTH-BOUNDED-BY-EXPT))
 (12 3 (:REWRITE UNICITY-OF-0))
 (11 11 (:TYPE-PRESCRIPTION ZIP))
 (11 11 (:TYPE-PRESCRIPTION NEGP))
 (10 10 (:REWRITE FOLD-CONSTS-IN-+))
 (6 3 (:LINEAR BITOPS::B-NOT-BOUND))
 (3 3 (:REWRITE-QUOTED-CONSTANT IFIX-UNDER-INT-EQUIV))
 (3 3 (:REWRITE BITOPS::BXOR-TO-BNOT))
 )
(GL::INTEGER-LENGTH-OF-REM
 (1556 8 (:REWRITE BITOPS::LOGBITP-UPPER-BOUND))
 (1226 10 (:REWRITE BITOPS::LOGBITP-WHEN-BITMASKP))
 (1196 10 (:DEFINITION BITMASKP**))
 (1090 44 (:REWRITE REM-X-Y-=-X . 2))
 (1061 1061 (:TYPE-PRESCRIPTION REM-TYPE . 2))
 (1061 1061 (:TYPE-PRESCRIPTION REM-TYPE . 1))
 (824 4 (:DEFINITION LOGBITP**))
 (777 23 (:DEFINITION INTEGER-LENGTH**))
 (656 20 (:REWRITE ZIP-OPEN))
 (498 114 (:REWRITE DEFAULT-<-2))
 (480 114 (:REWRITE DEFAULT-<-1))
 (385 69 (:TYPE-PRESCRIPTION BITOPS::LOGCDR-NATP))
 (362 98 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (354 4 (:REWRITE GL::INTEGER-LENGTH-LTE-BY-COMPARE-NONNEG))
 (354 4 (:REWRITE GL::INTEGER-LENGTH-LTE-BY-COMPARE-NEG))
 (353 37 (:REWRITE BITOPS::LOGCDR-OF-BIT))
 (252 24 (:REWRITE BITOPS::LOGCAR-OF-BIT))
 (246 12 (:DEFINITION BIT->BOOL$INLINE))
 (196 27 (:REWRITE DEFAULT-+-2))
 (164 44 (:REWRITE REM-=-0 . 2))
 (150 12 (:LINEAR BITOPS::LOGCAR-BOUND))
 (150 4 (:REWRITE NATP-RW))
 (128 16 (:REWRITE REM-TYPE))
 (124 26 (:LINEAR REM-TYPE . 1))
 (114 114 (:META CANCEL_PLUS-LESSP-CORRECT))
 (106 4 (:REWRITE NATP-WHEN-GTE-0))
 (92 92 (:REWRITE DEFAULT-UNARY-/))
 (92 92 (:REWRITE DEFAULT-*-2))
 (92 92 (:REWRITE DEFAULT-*-1))
 (90 2 (:REWRITE ZP-WHEN-INTEGERP))
 (82 82 (:TYPE-PRESCRIPTION LOGCAR-TYPE))
 (80 80 (:TYPE-PRESCRIPTION BITP))
 (76 16 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (76 16 (:REWRITE IFIX-WHEN-INTEGERP))
 (68 10 (:REWRITE DEFAULT-UNARY-MINUS))
 (64 16 (:REWRITE REM-=-0 . 1))
 (62 26 (:LINEAR REM-TYPE . 2))
 (60 4 (:REWRITE NATP-WHEN-INTEGERP))
 (56 2 (:REWRITE ZP-WHEN-GT-0))
 (50 50 (:TYPE-PRESCRIPTION BITMASKP$INLINE))
 (38 38 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (38 38 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (35 35 (:TYPE-PRESCRIPTION LOGCDR-TYPE))
 (30 30 (:TYPE-PRESCRIPTION NATP))
 (28 28 (:TYPE-PRESCRIPTION LOGBITP))
 (27 27 (:REWRITE DEFAULT-+-1))
 (20 20 (:LINEAR BITOPS::INTEGER-LENGTH-MONOTONIC))
 (16 16 (:TYPE-PRESCRIPTION IFIX))
 (16 16 (:LINEAR BITOPS::LOGCDR-<=-LOGCDR))
 (10 10 (:LINEAR BITOPS::LOGBITP-UPPER-BOUND))
 (10 10 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-LESS-THAN-EXP))
 (10 10 (:LINEAR BITOPS::INTEGER-LENGTH-WHEN-GREATER-THAN-EXP))
 (10 10 (:LINEAR BITOPS::INTEGER-LENGTH-BOUNDED-BY-EXPT))
 (4 4 (:REWRITE BITOPS::NORMALIZE-LOGBITP-WHEN-MODS-EQUAL))
 (2 2 (:REWRITE BITOPS::LOGBITP-0-OF-BIT))
 )
(GL::TRUNCATE-IS-FLOOR
 (1297 26 (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT))
 (841 52 (:REWRITE NIQ-TYPE . 3))
 (348 26 (:REWRITE DISTRIBUTIVITY))
 (346 346 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 (320 52 (:REWRITE NIQ-TYPE . 2))
 (280 249 (:REWRITE DEFAULT-*-2))
 (280 249 (:REWRITE DEFAULT-*-1))
 (147 116 (:REWRITE DEFAULT-<-1))
 (138 112 (:REWRITE DEFAULT-+-2))
 (118 118 (:META CANCEL_PLUS-LESSP-CORRECT))
 (116 116 (:REWRITE DEFAULT-<-2))
 (112 112 (:REWRITE DEFAULT-+-1))
 (105 103 (:REWRITE DEFAULT-UNARY-/))
 (78 26 (:REWRITE COMMUTATIVITY-OF-+))
 (55 53 (:REWRITE DEFAULT-UNARY-MINUS))
 (32 8 (:LINEAR NIQ-TYPE))
 (26 26 (:REWRITE NFIX-WHEN-NOT-NATP))
 (26 26 (:REWRITE NFIX-WHEN-NATP))
 (26 26 (:REWRITE INVERSE-OF-*))
 (26 26 (:REWRITE IFIX-WHEN-NOT-INTEGERP))
 (26 26 (:REWRITE IFIX-WHEN-INTEGERP))
 (13 13 (:REWRITE DEFAULT-NUMERATOR))
 (12 6 (:LINEAR X*Y>1-POSITIVE))
 (9 9 (:REWRITE DEFAULT-DENOMINATOR))
 (8 8 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (8 8 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-TYPE-3 . 1))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (6 6 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 1))
 (4 4 (:REWRITE-QUOTED-CONSTANT FIX-UNDER-NUMBER-EQUIV))
 (3 3 (:TYPE-PRESCRIPTION TRUNCATE-TYPE . 4))
 (3 3 (:TYPE-PRESCRIPTION TRUNCATE-TYPE . 3))
 (3 3 (:TYPE-PRESCRIPTION TRUNCATE-TYPE . 2))
 (3 3 (:TYPE-PRESCRIPTION TRUNCATE-TYPE . 1))
 )
(GL::REM-IS-MOD
 (179 55 (:REWRITE DEFAULT-UNARY-MINUS))
 (145 145 (:TYPE-PRESCRIPTION FLOOR-TYPE-1 . 2))
 (144 144 (:TYPE-PRESCRIPTION MOD-TYPE . 3))
 (144 144 (:TYPE-PRESCRIPTION MOD-TYPE . 2))
 (144 144 (:TYPE-PRESCRIPTION MOD-TYPE . 1))
 (143 69 (:REWRITE DEFAULT-*-2))
 (140 23 (:REWRITE DEFAULT-+-2))
 (120 69 (:REWRITE DEFAULT-*-1))
 (116 5 (:LINEAR X*Y>1-POSITIVE))
 (81 76 (:REWRITE DEFAULT-<-2))
 (76 76 (:REWRITE DEFAULT-<-1))
 (76 76 (:META CANCEL_PLUS-LESSP-CORRECT))
 (67 2 (:LINEAR FLOOR-BOUNDED-BY-/))
 (62 20 (:REWRITE FLOOR-TYPE-3 . 3))
 (58 16 (:REWRITE FLOOR-=-X/Y . 2))
 (49 47 (:REWRITE DEFAULT-UNARY-/))
 (48 10 (:REWRITE MOD-=-0 . 2))
 (41 20 (:REWRITE FLOOR-TYPE-4 . 2))
 (41 20 (:REWRITE FLOOR-TYPE-3 . 2))
 (36 20 (:REWRITE FLOOR-TYPE-4 . 3))
 (34 10 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 3))
 (31 10 (:REWRITE MOD-X-Y-=-X-FOR-RATIONALS . 2))
 (23 23 (:REWRITE DEFAULT-+-1))
 (21 21 (:TYPE-PRESCRIPTION REM-TYPE . 4))
 (21 21 (:TYPE-PRESCRIPTION REM-TYPE . 3))
 (21 21 (:TYPE-PRESCRIPTION REM-TYPE . 2))
 (21 21 (:TYPE-PRESCRIPTION REM-TYPE . 1))
 (21 21 (:TYPE-PRESCRIPTION INTEGERP-REM))
 (19 10 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 2))
 (16 1 (:REWRITE REM-X-Y-=-X . 2))
 (15 3 (:REWRITE FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT))
 (15 2 (:LINEAR MOD-TYPE . 2))
 (10 10 (:REWRITE THIS-NEEDS-TO-BE-ADDED-TO-QUOTIENT-REMAINDER-LEMMAS))
 (10 10 (:REWRITE MOD-X-Y-=-X+Y-FOR-RATIONALS . 3))
 (6 6 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (6 6 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (6 2 (:REWRITE RECIPROCAL-MINUS))
 (6 1 (:REWRITE REM-=-0 . 2))
 (4 1 (:LINEAR FLOOR-TYPE-2 . 2))
 (4 1 (:LINEAR FLOOR-TYPE-2 . 1))
 (2 2 (:LINEAR MOD-TYPE . 3))
 (2 2 (:LINEAR MOD-TYPE . 1))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 (1 1 (:LINEAR FLOOR-TYPE-1 . 2))
 (1 1 (:LINEAR FLOOR-TYPE-1 . 1))
 )
