(X::BYTES-LOADED-AT-ADDRESS-64
 (891 3 (:REWRITE X::CANONICAL-ADDRESS-P-HACK))
 (529 11 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN))
 (465 9 (:REWRITE BVCHOP-IDENTITY))
 (228 3 (:LINEAR BVCHOP-UPPER-BOUND-LINEAR-STRONG))
 (216 12 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (210 3 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL5-ALT))
 (159 3 (:LINEAR BVCHOP-UPPER-BOUND))
 (152 7 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL4))
 (150 3 (:REWRITE X::<-OF-BVCHOP-SAME))
 (144 6 (:REWRITE <-OF-+-CANCEL-1-1+))
 (141 9 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (140 20 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (132 10 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (112 2 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-LIMITS-THM-4))
 (68 38 (:REWRITE BOUND-FROM-NATP-FACT))
 (64 38 (:REWRITE NOT-<-WHEN-SBVLT))
 (63 3 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (52 52 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (48 2 (:REWRITE <-OF-+-CANCEL-2-2))
 (48 2 (:REWRITE <-OF-+-CANCEL-1+-2))
 (46 40 (:REWRITE DEFAULT-<-1))
 (46 38 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (45 24 (:REWRITE DEFAULT-+-2))
 (45 3 (:DEFINITION LEN))
 (44 44 (:REWRITE BOUND-WHEN-USB2))
 (44 44 (:REWRITE <-WHEN-SBVLT-CONSTANTS))
 (44 44 (:REWRITE <-WHEN-BVLT))
 (44 44 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (44 44 (:REWRITE <-OF-BV-AND-CONSTANT))
 (44 44 (:REWRITE <-FROM-<=-FREE))
 (42 40 (:REWRITE DEFAULT-<-2))
 (38 38 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (38 38 (:REWRITE NOT-<-OF-CONSTANT-AND-BV))
 (38 38 (:REWRITE BOUND-WHEN-USB))
 (38 38 (:REWRITE <-OF-NEGATIVE-WHEN-USBP))
 (38 38 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (38 38 (:REWRITE <-OF-CONSTANT-WHEN-<=-OF-CONSTANT-INTEGER))
 (38 38 (:REWRITE <-OF-CONSTANT-WHEN-<-OF-CONSTANT-INTEGER))
 (30 6 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-LIMITS-THM-1))
 (30 3 (:LINEAR BVCHOP-WHEN-TOP-BIT-1-LINEAR-CHEAP))
 (25 24 (:REWRITE DEFAULT-+-1))
 (24 24 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (24 24 (:REWRITE PLUS-BVCAT-WITH-0-ALT))
 (24 24 (:REWRITE PLUS-BVCAT-WITH-0))
 (24 24 (:REWRITE +-OF-MINUS-CONSTANT-VERSION))
 (24 6 (:REWRITE LEN-WHEN-ATOM))
 (24 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (24 3 (:LINEAR BVCHOP-WHEN-TOP-BIT-0-LINEAR-CHEAP))
 (24 2 (:REWRITE <-OF-+-CANCEL-1+-2+))
 (18 18 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (18 18 (:TYPE-PRESCRIPTION NATP-OF-BVCHOP-TYPE))
 (18 18 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (18 7 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL3))
 (18 2 (:DEFINITION TRUE-LISTP))
 (15 15 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (14 14 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (12 12 (:REWRITE UNSIGNED-BYTE-P-WHEN-ZP-CHEAP))
 (12 12 (:REWRITE UNSIGNED-BYTE-P-WHEN-TOP-BIT-0))
 (12 12 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND-<=-VERSION))
 (12 12 (:REWRITE REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER))
 (12 12 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL2))
 (12 6 (:REWRITE GETBIT-WHEN-NOT-0))
 (11 11 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-LIMITS-THM-3))
 (9 9 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (9 9 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (9 9 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (9 9 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (9 9 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (9 9 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (9 9 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (9 9 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (9 9 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (9 9 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (9 9 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (9 9 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (9 9 (:REWRITE BVCHOP-WHEN-GETBIT-AND-BVCHOP-KNOWN))
 (9 9 (:REWRITE BVCHOP-SUBST-WHEN-EQUAL-OF-BVCHOPS-GEN))
 (9 9 (:REWRITE BVCHOP-SUBST-CONSTANT-FROM-LOGEXT))
 (9 9 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (9 9 (:REWRITE BVCHOP-OF-EXPT-ALT))
 (9 9 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (7 7 (:REWRITE FOLD-CONSTS-IN-+))
 (7 7 (:REWRITE +-COMBINE-CONSTANTS))
 (6 6 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (6 6 (:REWRITE GETBIT-WHEN-BVLT-OF-SMALL))
 (6 6 (:REWRITE GETBIT-TOO-HIGH-CHEAP-FREE))
 (6 6 (:REWRITE GETBIT-TOO-HIGH-CHEAP))
 (6 6 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-OF-+-WHEN-CANONICAL-ADDRESS-P-OF-+-SPECIAL))
 (6 6 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-LIMITS-THM-2))
 (6 6 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-LIMITS-THM-0))
 (6 6 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (6 6 (:REWRITE <-OF-+-AND-+-COMBINE-CONSTANTS))
 (6 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (6 3 (:REWRITE GETBIT-WHEN-NOT-1))
 (5 5 (:REWRITE PLUS-OF-MINUS-SUBST-CONSTANT))
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (5 5 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (5 5 (:REWRITE CONSP-BY-LEN))
 (5 5 (:REWRITE +-OF-MINUS))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (4 4 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (4 4 (:REWRITE SET::IN-SET))
 (4 4 (:REWRITE |(< 0 (len x))|))
 (4 4 (:LINEAR LEN-WHEN-PREFIXP))
 (3 3 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (3 3 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (3 3 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL6))
 (3 3 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL5))
 (3 3 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (2 2 (:REWRITE X86ISA::X86P-BASE))
 (2 2 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE <-OF-+-CANCEL-1-2))
 (2 2 (:LINEAR X86ISA::MEMBER-P-POS-VALUE))
 (2 2 (:LINEAR X86ISA::MEMBER-P-POS-1-VALUE))
 )
(X::ADDRESSES-OF-SUBSEQUENT-STACK-SLOTS-AUX)
(X::ADDRESSES-OF-SUBSEQUENT-STACK-SLOTS-AUX-OPENER
 (58 4 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (50 10 (:REWRITE DEFAULT-+-2))
 (49 3 (:REWRITE ZP-WHEN-INTEGERP))
 (48 4 (:REWRITE +-COMBINE-CONSTANTS))
 (29 3 (:REWRITE ZP-WHEN-GT-0))
 (25 5 (:REWRITE INTEGERP-IMPLIES-ACL2-NUMBERP))
 (10 10 (:REWRITE PLUS-OF-MINUS-SUBST-CONSTANT))
 (10 10 (:REWRITE PLUS-BVCAT-WITH-0-ALT))
 (10 10 (:REWRITE PLUS-BVCAT-WITH-0))
 (10 10 (:REWRITE DEFAULT-+-1))
 (10 10 (:REWRITE +-OF-MINUS-CONSTANT-VERSION))
 (10 10 (:REWRITE +-OF-MINUS))
 (6 6 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (6 6 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE))
 (6 6 (:REWRITE INTEGERP-WHEN-SIGNED-BYTE-P))
 (6 6 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (6 6 (:REWRITE DEFAULT-<-2))
 (6 6 (:REWRITE DEFAULT-<-1))
 (6 6 (:REWRITE BOUND-WHEN-USB2))
 (6 6 (:REWRITE <-WHEN-SBVLT-CONSTANTS))
 (6 6 (:REWRITE <-WHEN-BVLT))
 (6 6 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (6 6 (:REWRITE <-OF-BV-AND-CONSTANT))
 (6 6 (:REWRITE <-FROM-<=-FREE))
 (5 5 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (5 5 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (5 5 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (5 3 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (4 3 (:REWRITE NOT-<-WHEN-SBVLT))
 (3 3 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (3 3 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (3 3 (:REWRITE NOT-<-OF-CONSTANT-AND-BV))
 (3 3 (:REWRITE BOUND-WHEN-USB))
 (3 3 (:REWRITE BOUND-FROM-NATP-FACT))
 (3 3 (:REWRITE <-OF-NEGATIVE-WHEN-USBP))
 (3 3 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:REWRITE <-OF-CONSTANT-WHEN-<=-OF-CONSTANT-INTEGER))
 (3 3 (:REWRITE <-OF-CONSTANT-WHEN-<-OF-CONSTANT-INTEGER))
 (1 1 (:REWRITE ZP-OPEN))
 )
(X::CANONICAL-ADDRESS-LISTP-OF-ADDRESSES-OF-SUBSEQUENT-STACK-SLOTS-AUX
 (3491 39 (:REWRITE SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P))
 (2048 180 (:REWRITE BOUND-FROM-NATP-FACT))
 (1868 43 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (1822 42 (:REWRITE NATP-WHEN-INTEGERP-CHEAP))
 (1620 240 (:REWRITE DEFAULT-<-1))
 (1443 11 (:REWRITE SIGNED-BYTE-P-OF-+))
 (560 20 (:REWRITE ACL2-NUMBERP-OF-CAR-WHEN-ACL2-NUMBER-LISTP))
 (540 20 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (540 20 (:REWRITE INTEGERP-IMPLIES-ACL2-NUMBERP))
 (535 15 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-CONSTANT-STRONG))
 (520 40 (:REWRITE RATIONALP-OF-CAR-WHEN-RATIONAL-LISTP))
 (505 10 (:DEFINITION ACL2-NUMBER-LISTP))
 (410 20 (:DEFINITION RATIONAL-LISTP))
 (352 8 (:REWRITE NATP-OF-+-WHEN-NATP-AND-NATP))
 (344 180 (:REWRITE NOT-<-WHEN-SBVLT))
 (340 30 (:REWRITE INTEGERP-OF-CAR-WHEN-INTEGER-LISTP))
 (275 10 (:DEFINITION INTEGER-LISTP))
 (270 39 (:REWRITE SIGNED-BYTE-P-WHEN-TOP-BIT-0))
 (261 261 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (240 240 (:REWRITE DEFAULT-<-2))
 (240 240 (:REWRITE BOUND-WHEN-USB2))
 (240 240 (:REWRITE <-WHEN-SBVLT-CONSTANTS))
 (240 240 (:REWRITE <-WHEN-BVLT))
 (240 240 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (240 240 (:REWRITE <-OF-BV-AND-CONSTANT))
 (240 240 (:REWRITE <-FROM-<=-FREE))
 (199 15 (:REWRITE UNSIGNED-BYTE-P-OF-+))
 (190 180 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (180 180 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (180 180 (:REWRITE NOT-<-OF-CONSTANT-AND-BV))
 (180 180 (:REWRITE BOUND-WHEN-USB))
 (180 180 (:REWRITE <-OF-NEGATIVE-WHEN-USBP))
 (180 180 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (180 180 (:REWRITE <-OF-CONSTANT-WHEN-<-OF-CONSTANT-INTEGER))
 (160 40 (:REWRITE RATIONAL-LISTP-WHEN-NOT-CONSP))
 (157 15 (:REWRITE USB-PLUS-FROM-BOUNDS))
 (150 30 (:REWRITE X86ISA::INTEGERP-OF-CAR-WHEN-BYTE-LISTP))
 (140 140 (:TYPE-PRESCRIPTION RATIONAL-LISTP))
 (110 10 (:REWRITE X86ISA::BYTE-LISTP-BECOMES-ALL-UNSIGNED-BYTE-P))
 (102 38 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (88 88 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (80 80 (:TYPE-PRESCRIPTION ALL-UNSIGNED-BYTE-P))
 (80 20 (:REWRITE INTEGER-LISTP-WHEN-NOT-CONSP))
 (80 20 (:REWRITE ACL2-NUMBER-LISTP-WHEN-NOT-CONSP))
 (70 70 (:TYPE-PRESCRIPTION INTEGER-LISTP))
 (70 70 (:TYPE-PRESCRIPTION ACL2-NUMBER-LISTP))
 (66 66 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (66 33 (:REWRITE GETBIT-WHEN-NOT-0))
 (64 64 (:REWRITE SMALL-INT-HACK))
 (64 64 (:REWRITE PLUS-BVCAT-WITH-0-ALT))
 (64 64 (:REWRITE PLUS-BVCAT-WITH-0))
 (64 64 (:REWRITE DEFAULT-+-2))
 (64 64 (:REWRITE DEFAULT-+-1))
 (64 64 (:REWRITE +-OF-MINUS-CONSTANT-VERSION))
 (60 30 (:REWRITE INTEGERP-OF-CAR-WHEN-ALL-INTEGERP-CHEAP))
 (60 10 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-FOR-CAR))
 (60 10 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-ALL-UNSIGNED-BYTE-P))
 (60 1 (:REWRITE UNSIGNED-BYTE-P-OF-+-OF-MINUS-ALT))
 (59 59 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (59 59 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (51 51 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (51 51 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE))
 (51 51 (:REWRITE INTEGERP-WHEN-SIGNED-BYTE-P))
 (51 51 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (50 50 (:REWRITE DEFAULT-CDR))
 (50 50 (:REWRITE DEFAULT-CAR))
 (50 10 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP-2))
 (50 10 (:REWRITE UNSIGNED-BYTE-P-OF-CAR-WHEN-UNSIGNED-BYTE-LISTP))
 (44 44 (:REWRITE UNSIGNED-BYTE-P-WHEN-ZP-CHEAP))
 (44 44 (:REWRITE UNSIGNED-BYTE-P-WHEN-TOP-BIT-0))
 (44 44 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND-<=-VERSION))
 (43 43 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (43 43 (:REWRITE REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER))
 (42 42 (:TYPE-PRESCRIPTION NATP))
 (40 40 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-LISTP))
 (40 40 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (40 40 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (40 40 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (40 40 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (40 40 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (40 40 (:REWRITE CONSP-BY-LEN))
 (40 40 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (40 40 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (40 40 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (40 20 (:REWRITE RATIONAL-LISTP-OF-CDR-WHEN-RATIONAL-LISTP))
 (39 39 (:REWRITE SIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER-FREE))
 (39 39 (:REWRITE SIGNED-BYTE-P-WHEN-SIGNED-BYTE-P))
 (39 39 (:REWRITE BITOPS::SIGNED-BYTE-P-MONOTONICITY))
 (39 39 (:REWRITE SIGNED-BYTE-P-LONGER))
 (39 39 (:REWRITE BITOPS::SIGNED-BYTE-P-INCR))
 (38 38 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (38 38 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (38 38 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (38 38 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (38 38 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (33 33 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (33 33 (:REWRITE GETBIT-WHEN-BVLT-OF-SMALL))
 (33 33 (:REWRITE GETBIT-TOO-HIGH-CHEAP-FREE))
 (33 33 (:REWRITE GETBIT-TOO-HIGH-CHEAP))
 (32 10 (:REWRITE X86ISA::CDR-CANONICAL-ADDRESS-LISTP))
 (30 30 (:TYPE-PRESCRIPTION ALL-INTEGERP))
 (28 28 (:REWRITE SIGNED-BYTE-WHEN-NOT-INTEGERP-CHEAP))
 (28 28 (:REWRITE SIGNED-BYTE-WHEN-<=-OF-0-CHEAP))
 (28 28 (:REWRITE X86ISA::SIGNED-BYTE-P-WHEN-BETWEEN-CANONICAL-ADDRESSES))
 (25 25 (:REWRITE PLUS-OF-MINUS-SUBST-CONSTANT))
 (25 25 (:REWRITE +-OF-MINUS))
 (20 20 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-TAKE-AND-NTHCDR))
 (20 20 (:REWRITE UNSIGNED-BYTE-LISTP-WHEN-NOT-CONSP))
 (20 20 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (20 20 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (20 10 (:REWRITE INTEGER-LISTP-OF-CDR-WHEN-INTEGER-LISTP))
 (20 10 (:REWRITE ACL2-NUMBER-LISTP-OF-CDR-WHEN-ACL2-NUMBER-LISTP))
 (15 15 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-LIMITS-THM-3))
 (15 15 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL2))
 (15 15 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN))
 (14 14 (:REWRITE DEFAULT-*-2))
 (14 14 (:REWRITE DEFAULT-*-1))
 (12 12 (:REWRITE FOLD-CONSTS-IN-+))
 (11 11 (:REWRITE X86ISA::SIGNED-BYTE-P-LIMITS-THM))
 (10 10 (:TYPE-PRESCRIPTION X86ISA::BYTE-LISTP))
 (6 6 (:REWRITE DEFAULT-UNARY-MINUS))
 (5 5 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2))
 (5 5 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1))
 (5 5 (:REWRITE NOT-EQUAL-WHEN-NOT-EQUAL-BVCHOP))
 (5 5 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM-ALT))
 (5 5 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM))
 (5 5 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P-ALT))
 (5 5 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P))
 (5 5 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (5 5 (:REWRITE EQUAL-WHEN-BVLT))
 (5 5 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (5 5 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (5 5 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (5 5 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (5 5 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (5 5 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (5 5 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (5 5 (:REWRITE EQUAL-CONSTANT-WHEN-SLICE-EQUAL-CONSTANT))
 (5 5 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SLICE-EQUAL-CONSTANT))
 (5 5 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (5 5 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (5 5 (:REWRITE ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-1))
 (4 4 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (4 4 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (4 1 (:REWRITE BOOLAND-COMMUTATIVE))
 (2 2 (:REWRITE BOOLAND-OF-CONSTANT-ARG2))
 (2 2 (:REWRITE BOOLAND-OF-CONSTANT-ARG1))
 (1 1 (:TYPE-PRESCRIPTION BOOLAND))
 )
(X::ADDRESSES-OF-SUBSEQUENT-STACK-SLOTS)
(X::STANDARD-STATE-ASSUMPTION-64)
(X::STANDARD-ASSUMPTIONS-CORE-64
 (1128 5 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN))
 (207 33 (:REWRITE <-OF-+-ARG1-WHEN-NEGATIVE-CONSTANT))
 (178 26 (:REWRITE <-OF-+-ARG2-WHEN-NEGATIVE-CONSTANT))
 (120 24 (:REWRITE <-OF-+-COMBINE-CONSTANTS-2))
 (120 3 (:REWRITE BVCHOP-IDENTITY))
 (104 4 (:REWRITE <-OF-+-CANCEL-3-1))
 (98 32 (:REWRITE BOUND-FROM-NATP-FACT))
 (94 5 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (84 4 (:REWRITE <-OF-+-CANCEL-2-1))
 (80 4 (:REWRITE <-OF-+-CANCEL-2-2))
 (77 2 (:REWRITE X86ISA::CR0BITS-P-WHEN-UNSIGNED-BYTE-P))
 (73 1 (:REWRITE BVCHOP-NOT-0-WHEN-LOW-BIT-NOT-0))
 (72 47 (:REWRITE DEFAULT-<-1))
 (65 47 (:REWRITE DEFAULT-<-2))
 (61 1 (:REWRITE BVCHOP-NOT-0-WHEN-GETBIT-NOT-0))
 (53 2 (:REWRITE X86ISA::CR4BITS-P-WHEN-UNSIGNED-BYTE-P))
 (52 31 (:REWRITE DEFAULT-+-2))
 (48 48 (:REWRITE BOUND-WHEN-USB2))
 (48 48 (:REWRITE <-WHEN-SBVLT-CONSTANTS))
 (48 48 (:REWRITE <-WHEN-BVLT))
 (48 48 (:REWRITE <-TIGHTEN-WHEN-SLICE-IS-0))
 (48 48 (:REWRITE <-OF-BV-AND-CONSTANT))
 (48 48 (:REWRITE <-FROM-<=-FREE))
 (42 32 (:REWRITE NOT-<-WHEN-SBVLT))
 (41 41 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (40 2 (:LINEAR GETBIT-BOUND-LINEAR))
 (33 32 (:REWRITE NOT-<-WHEN-SBVLT-ALT))
 (33 31 (:REWRITE DEFAULT-+-1))
 (32 32 (:REWRITE USE-<=-BOUND-TO-DROP-<=-HYP))
 (32 32 (:REWRITE NOT-<-OF-CONSTANT-AND-BV))
 (32 32 (:REWRITE BOUND-WHEN-USB))
 (32 32 (:REWRITE <-OF-NEGATIVE-WHEN-USBP))
 (32 32 (:REWRITE <-OF-CONSTANT-WHEN-UNSIGNED-BYTE-P-SIZE-PARAM))
 (32 32 (:REWRITE <-OF-CONSTANT-WHEN-<=-OF-CONSTANT-INTEGER))
 (32 32 (:REWRITE <-OF-CONSTANT-WHEN-<-OF-CONSTANT-INTEGER))
 (32 6 (:REWRITE SMALL-INT-HACK))
 (31 31 (:REWRITE X86ISA::XR-BASE))
 (31 31 (:REWRITE PLUS-BVCAT-WITH-0-ALT))
 (31 31 (:REWRITE PLUS-BVCAT-WITH-0))
 (31 31 (:REWRITE +-OF-MINUS-CONSTANT-VERSION))
 (26 1 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (24 21 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM))
 (24 3 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-3BITS-P))
 (22 3 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL4))
 (21 21 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-2))
 (21 21 (:REWRITE REWRITE-BV-EQUALITY-WHEN-SIZES-DONT-MATCH-1))
 (21 21 (:REWRITE NOT-EQUAL-WHEN-NOT-EQUAL-BVCHOP))
 (21 21 (:REWRITE NOT-EQUAL-OF-CONSTANT-AND-BV-TERM-ALT))
 (21 21 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P-ALT))
 (21 21 (:REWRITE NOT-EQUAL-CONSTANT-WHEN-UNSIGNED-BYTE-P))
 (21 21 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (21 21 (:REWRITE EQUAL-WHEN-BVLT))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (21 21 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (21 21 (:REWRITE EQUAL-CONSTANT-WHEN-SLICE-EQUAL-CONSTANT))
 (21 21 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SLICE-EQUAL-CONSTANT))
 (21 21 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (21 21 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (21 21 (:REWRITE ADD-BVCHOPS-TO-EQUALITY-OF-SBPS-1))
 (21 3 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL1))
 (19 19 (:REWRITE <-OF-+-COMBINE-CONSTANTS-1))
 (19 3 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-LIMITS-THM-2))
 (15 1 (:DEFINITION LEN))
 (14 4 (:LINEAR X86ISA::N64P-XR-CTR))
 (12 6 (:REWRITE GETBIT-WHEN-NOT-0))
 (12 2 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (11 5 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (11 3 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-LIMITS-THM-1))
 (11 3 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-LIMITS-THM-0))
 (10 5 (:REWRITE GETBIT-WHEN-NOT-1))
 (10 1 (:LINEAR BVCHOP-WHEN-TOP-BIT-1-LINEAR-CHEAP))
 (9 9 (:REWRITE <-OF-+-CANCEL-1-2))
 (9 1 (:DEFINITION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (8 8 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (8 8 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (8 4 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (8 4 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (8 2 (:REWRITE LEN-WHEN-ATOM))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-RFLAGSBITS-P))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-MXCSRBITS-P))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-EVEX-PREFIXES-P))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-CR4BITS-P))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-CR0BITS-P))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-32BITS-P))
 (8 1 (:REWRITE X86ISA::UNSIGNED-BYTE-P-WHEN-22BITS-P))
 (8 1 (:LINEAR BVCHOP-WHEN-TOP-BIT-0-LINEAR-CHEAP))
 (6 6 (:TYPE-PRESCRIPTION X86ISA::3BITS-P))
 (6 6 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (6 6 (:REWRITE GETBIT-WHEN-BVLT-OF-SMALL))
 (6 6 (:REWRITE GETBIT-TOO-HIGH-CHEAP-FREE))
 (6 6 (:REWRITE GETBIT-TOO-HIGH-CHEAP))
 (6 3 (:REWRITE X86ISA::3BITS-P-WHEN-UNSIGNED-BYTE-P))
 (6 2 (:REWRITE GETBIT-OF-0-WHEN-BITP))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P-2))
 (5 5 (:REWRITE USE-ALL-UNSIGNED-BYTE-P))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-WHEN-ZP-CHEAP))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-WHEN-TOP-BIT-0))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-TIGHTEN-WHEN-SLICE-IS-0))
 (5 5 (:REWRITE BITOPS::UNSIGNED-BYTE-P-INCR))
 (5 5 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND-<=-VERSION))
 (5 5 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (5 5 (:REWRITE REWRITE-UNSIGNED-BYTE-P-WHEN-TERM-SIZE-IS-LARGER))
 (5 5 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-LIMITS-THM-3))
 (5 5 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL2))
 (5 5 (:REWRITE X::<-OF-READ-AND-NON-POSITIVE))
 (4 4 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (4 4 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (4 4 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (4 4 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (4 4 (:REWRITE <-OF-+-AND-+-COMBINE-CONSTANTS))
 (4 2 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 2 (:REWRITE GETBIT-IDENTITY))
 (3 3 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (3 3 (:REWRITE INTEGERP-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:REWRITE INTEGERP-WHEN-SIGNED-BYTE-P))
 (3 3 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-OF-+-WHEN-CANONICAL-ADDRESS-P-OF-+-SPECIAL))
 (3 3 (:REWRITE X86ISA::CANONICAL-ADDRESS-P-BETWEEN-SPECIAL3))
 (3 3 (:REWRITE BVCHOP-WHEN-TOP-BIT-NOT-1-FAKE-FREE))
 (3 3 (:REWRITE BVCHOP-WHEN-GETBIT-AND-BVCHOP-KNOWN))
 (3 3 (:REWRITE BVCHOP-SUBST-WHEN-EQUAL-OF-BVCHOPS-GEN))
 (3 3 (:REWRITE BVCHOP-SUBST-CONSTANT-FROM-LOGEXT))
 (3 3 (:REWRITE BVCHOP-OF-EXPT-ALT))
 (3 3 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::RFLAGSBITS-P$INLINE))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::MXCSRBITS-P))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::EVEX-PREFIXES-P$INLINE))
 (2 2 (:TYPE-PRESCRIPTION SET::EMPTYP-TYPE))
 (2 2 (:TYPE-PRESCRIPTION BITP))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::32BITS-P))
 (2 2 (:TYPE-PRESCRIPTION X86ISA::22BITS-P))
 (2 2 (:REWRITE TRUE-LISTP-WHEN-UNSIGNED-BYTE-LISTP))
 (2 2 (:REWRITE X::READ-WHEN-PROGRAM-AT-GEN))
 (2 2 (:REWRITE X::READ-IN-TERMS-OF-NTH-AND-POS-ERIC-8-BYTES))
 (2 2 (:REWRITE X::READ-CHOP-CONSTANT-ADDRESS))
 (2 2 (:REWRITE PLUS-OF-MINUS-SUBST-CONSTANT))
 (2 2 (:REWRITE SET::IN-SET))
 (2 2 (:REWRITE GETBIT-IDENTITY-FREE))
 (2 2 (:REWRITE DEFAULT-CDR))
 (2 2 (:REWRITE DEFAULT-*-2))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-PREFIXMAP-P . 1))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 2))
 (2 2 (:REWRITE VL::CONSP-WHEN-MEMBER-EQUAL-OF-VL-NAMEDB-NAMESET-P . 1))
 (2 2 (:REWRITE CONSP-BY-LEN))
 (2 2 (:REWRITE +-OF-MINUS))
 (2 2 (:LINEAR LEN-WHEN-PREFIXP))
 (2 2 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (2 1 (:REWRITE X86ISA::RFLAGSBITS-P-WHEN-UNSIGNED-BYTE-P))
 (2 1 (:REWRITE X86ISA::MXCSRBITS-P-WHEN-UNSIGNED-BYTE-P))
 (2 1 (:REWRITE X86ISA::EVEX-PREFIXES-P-WHEN-UNSIGNED-BYTE-P))
 (2 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (2 1 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (2 1 (:REWRITE BVCHOP-IMPOSSIBLE-VALUE))
 (2 1 (:REWRITE X86ISA::32BITS-P-WHEN-UNSIGNED-BYTE-P))
 (2 1 (:REWRITE X86ISA::22BITS-P-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE X86ISA::X86P-BASE))
 (1 1 (:REWRITE NOT-EQUAL-OF-BVCHOP-WHEN-EQUAL-OF-GETBIT))
 (1 1 (:REWRITE NOT-EQUAL-BVCHOP-WHEN-NOT-EQUAL-BVCHOP))
 (1 1 (:REWRITE X86ISA::MXCSRBITS->ZM-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE X86ISA::MXCSRBITS->UM-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE X86ISA::MXCSRBITS->RC-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE X86ISA::MXCSRBITS->PM-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE X86ISA::MXCSRBITS->OM-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE X86ISA::MXCSRBITS->IM-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE X86ISA::MXCSRBITS->FTZ-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE X86ISA::MXCSRBITS->DM-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE X86ISA::MXCSRBITS->DAZ-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-IMPOSSIBLE-ALT))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-IMPOSSIBLE))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (1 1 (:REWRITE EQUAL-OF-BVCHOP-AND-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (1 1 (:REWRITE EQUAL-OF-+-WHEN-NEGATIVE-CONSTANT))
 (1 1 (:REWRITE EQUAL-OF-+-COMBINE-CONSTANTS))
 (1 1 (:REWRITE X86ISA::CR4BITS->OSFXSR-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE X86ISA::CR0BITS->TS-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE X86ISA::CR0BITS->EM-OF-WRITE-WITH-MASK))
 (1 1 (:REWRITE CONSP-OF-CDR-BY-LEN))
 (1 1 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (1 1 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (1 1 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (1 1 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-LISTP-CHEAP))
 (1 1 (:REWRITE ALL-UNSIGNED-BYTE-P-WHEN-NOT-CONSP))
 (1 1 (:REWRITE ALL-UNSIGNED-BYTE-P-FROM-ALL-UNSIGNED-BYTE-P-NARROWER))
 (1 1 (:LINEAR X86ISA::MEMBER-P-POS-VALUE))
 (1 1 (:LINEAR X86ISA::MEMBER-P-POS-1-VALUE))
 )
(X::STANDARD-ASSUMPTIONS-MACH-O-64)
(X::STANDARD-ASSUMPTIONS-PE-64)
(X::STANDARD-ASSUMPTIONS-ELF-64)
