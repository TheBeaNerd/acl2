(SBVLT-REWRITE
 (2645 32 (:REWRITE LOGEXT-WHEN-NEGATIVE))
 (1953 63 (:DEFINITION EXPT))
 (882 63 (:REWRITE ZIP-OPEN))
 (756 8 (:REWRITE <-OF-LOGEXT-TRUE))
 (706 16 (:REWRITE LOGEXT-WHEN-SIGNED-BYTE-P))
 (680 10 (:DEFINITION SIGNED-BYTE-P))
 (578 2 (:REWRITE <-OF-LOGEXT-FALSE))
 (394 332 (:REWRITE DEFAULT-+-2))
 (356 332 (:REWRITE DEFAULT-+-1))
 (344 56 (:REWRITE BVCHOP-IDENTITY))
 (310 10 (:DEFINITION INTEGER-RANGE-P))
 (245 178 (:REWRITE DEFAULT-<-2))
 (243 178 (:REWRITE DEFAULT-<-1))
 (208 56 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (189 63 (:REWRITE FOLD-CONSTS-IN-+))
 (189 63 (:REWRITE DEFAULT-*-2))
 (180 180 (:REWRITE <-WHEN-BVLT))
 (156 156 (:REWRITE BOUND-WHEN-USB))
 (123 123 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (112 56 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (104 56 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (99 11 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (88 8 (:LINEAR <-OF-LOGEXT-SAME-LINEAR))
 (84 28 (:REWRITE DEFAULT-UNARY-MINUS))
 (74 74 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (74 74 (:REWRITE EQUAL-WHEN-BVLT))
 (74 74 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (74 74 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (74 74 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (74 74 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (74 74 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (74 74 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (74 74 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (74 74 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (74 74 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (70 70 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (63 63 (:REWRITE DEFAULT-*-1))
 (62 31 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (62 31 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (58 58 (:TYPE-PRESCRIPTION POSP))
 (56 56 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (56 56 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (56 56 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (56 56 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (56 56 (:REWRITE BVCHOP-SUBST-CONSTANT-FROM-LOGEXT))
 (56 56 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (56 56 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (56 8 (:DEFINITION NATP))
 (55 55 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (48 48 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (48 48 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (48 48 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (48 48 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (31 31 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (31 31 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (31 31 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (26 16 (:REWRITE LOGEXT-WHEN-I-IS-NOT-AN-INTEGER))
 (22 22 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (19 19 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (16 16 (:REWRITE LOGEXT-WHEN-SIZE-NOT-POSP))
 (15 15 (:REWRITE BVCHOP-BOUND))
 (14 2 (:REWRITE BVLT-WHEN-NOT-POSP-ARG1))
 (11 11 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (11 11 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (11 11 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (11 6 (:REWRITE LOGEXT-NEGATIVE))
 (10 10 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (8 8 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (7 7 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (4 2 (:REWRITE BVLT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (4 2 (:REWRITE BVLT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (2 2 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER2))
 (2 2 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER))
 (2 2 (:REWRITE NOT-BVLT-WHEN-BVLT-OPPOSITE-SMALLER-AND-UNSIGNED-BYTE-P))
 (2 2 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<=-OF-CONSTANT))
 (2 2 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<-OF-CONSTANT))
 (2 2 (:REWRITE BVLT-WHEN-NOT-BVLT))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-WIDER))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-REVERSE))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-MUST-BE-FAKE-FREE))
 (2 2 (:REWRITE BVLT-WHEN-BVLT-FALSE))
 (2 2 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST-ALT))
 (2 2 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST))
 (2 2 (:REWRITE BVLT-TRIM-CONSTANT-ARG2))
 (2 2 (:REWRITE BVLT-TRIM-CONSTANT-ARG1))
 (2 2 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK-CONSTANTS))
 (2 2 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK))
 (2 2 (:REWRITE BVLT-TRANSITIVE-5-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-5-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-4-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-4-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-3-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-3-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-2-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-2-A))
 (2 2 (:REWRITE BVLT-TRANSITIVE-1-B))
 (2 2 (:REWRITE BVLT-TRANSITIVE-1-A))
 (2 2 (:REWRITE BVLT-OF-MAX-MINUS-1-ARG2-CONSTANT-VERSION))
 (2 2 (:REWRITE BVLT-OF-MAX-CONSTANT-VERSION))
 (2 2 (:REWRITE BVLT-MAX-ARG3-CONSTANT-VERSION))
 (2 2 (:REWRITE BVLT-FALSE-WHEN-BVLT-BETTER))
 (2 2 (:REWRITE BVLT-FALSE-WHEN-BVLT))
 (2 1 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG3))
 (2 1 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG2))
 (2 1 (:REWRITE NOT-SBVLT-WHEN-SBVLT-REV-CHEAP))
 (1 1 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-OF-SIZE))
 (1 1 (:REWRITE SBVLT-WHEN-<))
 (1 1 (:REWRITE SBVLT-TRIM-CONSTANT-RIGHT))
 (1 1 (:REWRITE SBVLT-TRIM-CONSTANT-LEFT))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-FREE-BACK))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-FREE))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-3-B))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-3-A))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-2-B))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-2-A))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-1-B))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-1-A))
 (1 1 (:REWRITE SBVLT-SUBST-CONSTANT-SAME-ARG2))
 (1 1 (:REWRITE SBVLT-SUBST-CONSTANT-ALT))
 (1 1 (:REWRITE SBVLT-SUBST-CONSTANT))
 (1 1 (:REWRITE SBVLT-OF-MINUS-ONE))
 (1 1 (:REWRITE NOT-SBVLT-OF-MAXINT))
 )
(MYIF-OF-SBVLT-OF-0-AND-EQUAL-OF-0
 (81 1 (:REWRITE NOT-SBVLT-OF-MAXINT))
 (58 1 (:DEFINITION EXPT))
 (23 2 (:REWRITE COMMUTATIVITY-OF-+))
 (19 8 (:REWRITE DEFAULT-+-2))
 (18 1 (:REWRITE ZIP-OPEN))
 (17 2 (:REWRITE FOLD-CONSTS-IN-+))
 (9 9 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (9 9 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (8 8 (:REWRITE DEFAULT-+-1))
 (6 2 (:REWRITE DEFAULT-*-2))
 (5 4 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (5 1 (:REWRITE UNICITY-OF-0))
 (4 4 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (4 4 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (4 4 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (4 1 (:DEFINITION FIX))
 (3 3 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (3 3 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (3 3 (:REWRITE EQUAL-WHEN-BVLT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (3 3 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (3 3 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (3 3 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 2 (:DEFINITION NOT))
 (2 1 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG3))
 (2 1 (:REWRITE NOT-SBVLT-WHEN-SBVLT-REV-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION BOOLEANP))
 (1 1 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-OF-SIZE))
 (1 1 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG2))
 (1 1 (:REWRITE SBVLT-WHEN-<))
 (1 1 (:REWRITE SBVLT-TRIM-CONSTANT-RIGHT))
 (1 1 (:REWRITE SBVLT-TRIM-CONSTANT-LEFT))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-FREE-BACK))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-FREE))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-3-B))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-3-A))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-2-B))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-2-A))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-1-B))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-1-A))
 (1 1 (:REWRITE SBVLT-SUBST-CONSTANT-SAME-ARG2))
 (1 1 (:REWRITE SBVLT-SUBST-CONSTANT-ALT))
 (1 1 (:REWRITE SBVLT-SUBST-CONSTANT))
 (1 1 (:REWRITE SBVLT-OF-MINUS-ONE))
 (1 1 (:REWRITE DEFAULT-<-2))
 (1 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE BOUND-WHEN-USB))
 (1 1 (:REWRITE <-WHEN-BVLT))
 )
(SBVLT-BECOMES-BVLT-BETTER
 (102 8 (:REWRITE BOUND-WHEN-USB))
 (62 2 (:DEFINITION EXPT))
 (28 2 (:REWRITE ZIP-OPEN))
 (19 15 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-+-1))
 (15 8 (:REWRITE DEFAULT-<-2))
 (12 2 (:REWRITE COMMUTATIVITY-OF-+))
 (8 8 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE <-WHEN-BVLT))
 (7 1 (:REWRITE BVLT-WHEN-NOT-POSP-ARG1))
 (6 2 (:REWRITE FOLD-CONSTS-IN-+))
 (6 2 (:REWRITE DEFAULT-*-2))
 (4 4 (:REWRITE BVCHOP-SUBST-CONSTANT-FROM-LOGEXT))
 (4 2 (:REWRITE GETBIT-WHEN-NOT-1))
 (4 2 (:REWRITE GETBIT-WHEN-NOT-0))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (2 2 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (2 2 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (2 2 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (2 2 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (2 2 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (2 2 (:REWRITE EQUAL-WHEN-BVLT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (2 2 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (2 2 (:REWRITE EQUAL-OF-BOOLEANS-CHEAP))
 (2 2 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (2 2 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (2 2 (:REWRITE DEFAULT-*-1))
 (2 1 (:REWRITE NOT-SBVLT-WHEN-SBVLT-REV-CHEAP))
 (1 1 (:TYPE-PRESCRIPTION POSP))
 (1 1 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-OF-SIZE))
 (1 1 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG3))
 (1 1 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG2))
 (1 1 (:REWRITE SBVLT-WHEN-<))
 (1 1 (:REWRITE SBVLT-TRIM-CONSTANT-RIGHT))
 (1 1 (:REWRITE SBVLT-TRIM-CONSTANT-LEFT))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-FREE-BACK))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-FREE))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-3-B))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-3-A))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-2-B))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-2-A))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-1-B))
 (1 1 (:REWRITE SBVLT-TRANSITIVE-1-A))
 (1 1 (:REWRITE SBVLT-SUBST-CONSTANT-SAME-ARG2))
 (1 1 (:REWRITE SBVLT-SUBST-CONSTANT-ALT))
 (1 1 (:REWRITE SBVLT-SUBST-CONSTANT))
 (1 1 (:REWRITE SBVLT-OF-MINUS-ONE))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (1 1 (:REWRITE NOT-SBVLT-OF-MAXINT))
 (1 1 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER2))
 (1 1 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER))
 (1 1 (:REWRITE NOT-BVLT-WHEN-BVLT-OPPOSITE-SMALLER-AND-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<=-OF-CONSTANT))
 (1 1 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<-OF-CONSTANT))
 (1 1 (:REWRITE BVLT-WHEN-NOT-BVLT))
 (1 1 (:REWRITE BVLT-WHEN-BVLT-WIDER))
 (1 1 (:REWRITE BVLT-WHEN-BVLT-REVERSE))
 (1 1 (:REWRITE BVLT-WHEN-BVLT-MUST-BE-FAKE-FREE))
 (1 1 (:REWRITE BVLT-WHEN-BVLT-FALSE))
 (1 1 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST-ALT))
 (1 1 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST))
 (1 1 (:REWRITE BVLT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVLT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (1 1 (:REWRITE BVLT-TRIM-CONSTANT-ARG2))
 (1 1 (:REWRITE BVLT-TRIM-CONSTANT-ARG1))
 (1 1 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK-CONSTANTS))
 (1 1 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK))
 (1 1 (:REWRITE BVLT-TRANSITIVE-5-B))
 (1 1 (:REWRITE BVLT-TRANSITIVE-5-A))
 (1 1 (:REWRITE BVLT-TRANSITIVE-4-B))
 (1 1 (:REWRITE BVLT-TRANSITIVE-4-A))
 (1 1 (:REWRITE BVLT-TRANSITIVE-3-B))
 (1 1 (:REWRITE BVLT-TRANSITIVE-3-A))
 (1 1 (:REWRITE BVLT-TRANSITIVE-2-B))
 (1 1 (:REWRITE BVLT-TRANSITIVE-2-A))
 (1 1 (:REWRITE BVLT-TRANSITIVE-1-B))
 (1 1 (:REWRITE BVLT-TRANSITIVE-1-A))
 (1 1 (:REWRITE BVLT-OF-MAX-MINUS-1-ARG2-CONSTANT-VERSION))
 (1 1 (:REWRITE BVLT-OF-MAX-CONSTANT-VERSION))
 (1 1 (:REWRITE BVLT-MAX-ARG3-CONSTANT-VERSION))
 (1 1 (:REWRITE BVLT-FALSE-WHEN-BVLT-BETTER))
 (1 1 (:REWRITE BVLT-FALSE-WHEN-BVLT))
 (1 1 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (1 1 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 )
(SBVLT-BECOMES-BVLT
 (1382 16 (:REWRITE SBVLT-TRANSITIVE-FREE))
 (1190 17 (:REWRITE LOGEXT-WHEN-SIGNED-BYTE-P))
 (1156 17 (:DEFINITION SIGNED-BYTE-P))
 (1147 37 (:DEFINITION EXPT))
 (527 17 (:DEFINITION INTEGER-RANGE-P))
 (518 37 (:REWRITE ZIP-OPEN))
 (362 12 (:REWRITE NOT-SBVLT-OF-MAXINT))
 (227 118 (:REWRITE DEFAULT-<-2))
 (222 202 (:REWRITE DEFAULT-+-2))
 (222 37 (:REWRITE COMMUTATIVITY-OF-+))
 (202 202 (:REWRITE DEFAULT-+-1))
 (182 13 (:LINEAR GETBIT-BOUND-LINEAR))
 (158 118 (:REWRITE DEFAULT-<-1))
 (143 143 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (119 119 (:REWRITE <-WHEN-BVLT))
 (111 37 (:REWRITE FOLD-CONSTS-IN-+))
 (111 37 (:REWRITE DEFAULT-*-2))
 (98 98 (:REWRITE BOUND-WHEN-USB))
 (98 26 (:REWRITE BVCHOP-WITH-N-NEGATIVE))
 (96 48 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (74 48 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (56 56 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (53 53 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (53 53 (:REWRITE EQUAL-WHEN-BVLT))
 (53 53 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (53 53 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (53 53 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (53 53 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (53 53 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (53 53 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (53 53 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (53 53 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (53 53 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (51 17 (:REWRITE DEFAULT-UNARY-MINUS))
 (48 48 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (48 48 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (48 48 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (48 26 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER))
 (46 26 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-POSP))
 (40 40 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (37 37 (:REWRITE DEFAULT-*-1))
 (34 17 (:REWRITE LOGEXT-WHEN-I-IS-NOT-AN-INTEGER))
 (34 17 (:REWRITE LOGBITP-WHEN-J-IS-NOT-INTEGERP))
 (34 17 (:REWRITE LOGAPP-WHEN-NOT-INTEGERP-ARG2))
 (33 33 (:REWRITE BVCHOP-SUBST-CONSTANT-FROM-LOGEXT))
 (33 33 (:REWRITE BVCHOP-IDENTITY-CHEAP))
 (31 31 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (31 31 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (31 31 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (31 7 (:REWRITE BVLT-WHEN-NOT-POSP-ARG1))
 (27 16 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG3))
 (27 3 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR))
 (26 26 (:REWRITE BVCHOP-WITH-N-NOT-AN-INTEGER))
 (26 26 (:REWRITE BVCHOP-WHEN-SIZE-IS-NOT-NATP))
 (26 26 (:REWRITE BVCHOP-WHEN-NOT-NATP-ARG1-CHEAP))
 (26 26 (:REWRITE BVCHOP-WHEN-I-IS-NOT-AN-INTEGER-CHEAP))
 (26 26 (:REWRITE BVCHOP-SUBST-CONSTANT))
 (25 16 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG2))
 (24 24 (:TYPE-PRESCRIPTION POSP))
 (24 12 (:REWRITE NOT-SBVLT-WHEN-SBVLT-REV-CHEAP))
 (19 16 (:REWRITE SBVLT-WHEN-<))
 (17 17 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (17 17 (:REWRITE LOGEXT-WHEN-SIZE-NOT-POSP))
 (17 17 (:REWRITE LOGAPP-WHEN-NOT-NATP-ARG1))
 (17 17 (:REWRITE LOGAPP-WHEN-NOT-INTEGERP-ARG3))
 (16 16 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-OF-SIZE))
 (16 16 (:REWRITE SBVLT-TRIM-CONSTANT-RIGHT))
 (16 16 (:REWRITE SBVLT-TRIM-CONSTANT-LEFT))
 (16 16 (:REWRITE SBVLT-TRANSITIVE-2-B))
 (16 16 (:REWRITE SBVLT-TRANSITIVE-2-A))
 (16 16 (:REWRITE SBVLT-TRANSITIVE-1-B))
 (16 16 (:REWRITE SBVLT-TRANSITIVE-1-A))
 (16 16 (:REWRITE SBVLT-SUBST-CONSTANT-SAME-ARG2))
 (16 16 (:REWRITE SBVLT-SUBST-CONSTANT-ALT))
 (16 16 (:REWRITE SBVLT-SUBST-CONSTANT))
 (16 16 (:REWRITE SBVLT-OF-MINUS-ONE))
 (13 7 (:REWRITE BVLT-WHEN-ARG1-IS-NOT-AN-INTEGER))
 (12 12 (:REWRITE SBVLT-TRANSITIVE-FREE-BACK))
 (12 12 (:REWRITE SBVLT-TRANSITIVE-3-B))
 (12 12 (:REWRITE SBVLT-TRANSITIVE-3-A))
 (12 7 (:REWRITE BVLT-WHEN-ARG2-IS-NOT-AN-INTEGER))
 (7 7 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER2))
 (7 7 (:REWRITE NOT-BVLT-WHEN-NOT-BVLT-NARROWER))
 (7 7 (:REWRITE NOT-BVLT-WHEN-BVLT-OPPOSITE-SMALLER-AND-UNSIGNED-BYTE-P))
 (7 7 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<=-OF-CONSTANT))
 (7 7 (:REWRITE NOT-BVLT-OF-CONSTANT-WHEN-<-OF-CONSTANT))
 (7 7 (:REWRITE BVLT-WHEN-NOT-BVLT))
 (7 7 (:REWRITE BVLT-WHEN-BVLT-WIDER))
 (7 7 (:REWRITE BVLT-WHEN-BVLT-REVERSE))
 (7 7 (:REWRITE BVLT-WHEN-BVLT-MUST-BE-FAKE-FREE))
 (7 7 (:REWRITE BVLT-WHEN-BVLT-FALSE))
 (7 7 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST-ALT))
 (7 7 (:REWRITE BVLT-WHEN-BVCHOP-KNOWN-SUBST))
 (7 7 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK-CONSTANTS))
 (7 7 (:REWRITE BVLT-TRANSITIVE-FREE2-BACK))
 (7 7 (:REWRITE BVLT-OF-MAX-MINUS-1-ARG2-CONSTANT-VERSION))
 (7 7 (:REWRITE BVLT-FALSE-WHEN-BVLT-BETTER))
 (7 7 (:REWRITE BVLT-FALSE-WHEN-BVLT))
 (6 6 (:LINEAR <=-OF-BVCHOP-SAME-LINEAR-2))
 (5 5 (:REWRITE BVLT-TRIM-CONSTANT-ARG2))
 (5 5 (:REWRITE BVLT-TRIM-CONSTANT-ARG1))
 (5 5 (:REWRITE BVLT-TRANSITIVE-5-B))
 (5 5 (:REWRITE BVLT-TRANSITIVE-5-A))
 (5 5 (:REWRITE BVLT-TRANSITIVE-4-B))
 (5 5 (:REWRITE BVLT-TRANSITIVE-4-A))
 (5 5 (:REWRITE BVLT-TRANSITIVE-3-B))
 (5 5 (:REWRITE BVLT-TRANSITIVE-3-A))
 (5 5 (:REWRITE BVLT-TRANSITIVE-2-B))
 (5 5 (:REWRITE BVLT-TRANSITIVE-2-A))
 (5 5 (:REWRITE BVLT-TRANSITIVE-1-B))
 (5 5 (:REWRITE BVLT-TRANSITIVE-1-A))
 (5 5 (:REWRITE BVLT-OF-MAX-CONSTANT-VERSION))
 (5 5 (:REWRITE BVLT-MAX-ARG3-CONSTANT-VERSION))
 (3 3 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (3 3 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (3 3 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (3 3 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-WHEN-SIZE-IS-NEGATIVE-LIMITED))
 (2 2 (:REWRITE UNSIGNED-BYTE-P-FALSE-WHEN-NOT-LONGER))
 (1 1 (:REWRITE BVCHOP-NUMERIC-BOUND))
 (1 1 (:REWRITE BVCHOP-BOUND))
 )
(BOOLOR-OF-SBVLT-OF-CONSTANT-AND-SBVLT-OF-CONSTANT
 (7296 150 (:DEFINITION EXPT))
 (5673 54 (:REWRITE <-OF-LOGEXT-TRUE))
 (4567 54 (:REWRITE <-OF-LOGEXT-FALSE))
 (3854 58 (:REWRITE LOGEXT-WHEN-SIGNED-BYTE-P))
 (3744 52 (:DEFINITION SIGNED-BYTE-P))
 (2659 58 (:REWRITE LOGEXT-WHEN-TOP-BIT-0))
 (2566 248 (:REWRITE COMMUTATIVITY-OF-+))
 (2492 150 (:REWRITE ZIP-OPEN))
 (1822 248 (:REWRITE FOLD-CONSTS-IN-+))
 (1612 52 (:DEFINITION INTEGER-RANGE-P))
 (1601 950 (:REWRITE DEFAULT-+-2))
 (1357 1357 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (1357 1357 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (1196 52 (:LINEAR GETBIT-BOUND-LINEAR))
 (996 646 (:REWRITE DEFAULT-<-1))
 (950 950 (:REWRITE DEFAULT-+-1))
 (950 646 (:REWRITE DEFAULT-<-2))
 (746 746 (:REWRITE <-WHEN-BVLT))
 (744 248 (:REWRITE DEFAULT-*-2))
 (727 727 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (704 104 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (688 133 (:DEFINITION POSP))
 (624 624 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (605 55 (:LINEAR <-OF-LOGEXT-SAME-LINEAR))
 (525 75 (:REWRITE +-OF---AND-0))
 (490 98 (:REWRITE UNICITY-OF-0))
 (392 98 (:DEFINITION FIX))
 (390 390 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (390 390 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (390 390 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (385 55 (:LINEAR <=-OF-LOGEXT-LINEAR-UPPER))
 (385 55 (:LINEAR <-OF-LOGEXT-LINEAR-LOWER))
 (385 55 (:DEFINITION NATP))
 (382 382 (:REWRITE BOUND-WHEN-USB))
 (300 100 (:REWRITE DEFAULT-UNARY-MINUS))
 (248 248 (:REWRITE DEFAULT-*-1))
 (219 58 (:REWRITE LOGEXT-WHEN-SIZE-NOT-POSP))
 (208 104 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (208 104 (:REWRITE GETBIT-WHEN-NOT-1))
 (208 104 (:REWRITE GETBIT-WHEN-NOT-0))
 (208 104 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (179 104 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (150 150 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (150 150 (:REWRITE EQUAL-WHEN-BVLT))
 (150 150 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (150 150 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (150 150 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (150 150 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (150 150 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (150 150 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (150 150 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (150 150 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (150 150 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (150 150 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (133 133 (:TYPE-PRESCRIPTION POSP))
 (112 112 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (110 58 (:REWRITE LOGEXT-WHEN-I-IS-NOT-AN-INTEGER))
 (104 104 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (104 104 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (55 55 (:TYPE-PRESCRIPTION NATP))
 (55 55 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (55 55 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (55 55 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (52 52 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (46 5 (:REWRITE SBVLT-BECOMES-BVLT-BETTER))
 (10 5 (:REWRITE NOT-SBVLT-WHEN-SBVLT-REV-CHEAP))
 (9 5 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG3))
 (9 5 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG2))
 (5 5 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-OF-SIZE))
 (5 5 (:REWRITE SBVLT-WHEN-<))
 (5 5 (:REWRITE SBVLT-TRIM-CONSTANT-RIGHT))
 (5 5 (:REWRITE SBVLT-TRIM-CONSTANT-LEFT))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-FREE-BACK))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-FREE))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-3-B))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-3-A))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-2-B))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-2-A))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-1-B))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-1-A))
 (5 5 (:REWRITE SBVLT-SUBST-CONSTANT-SAME-ARG2))
 (5 5 (:REWRITE SBVLT-SUBST-CONSTANT-ALT))
 (5 5 (:REWRITE SBVLT-SUBST-CONSTANT))
 (5 5 (:REWRITE SBVLT-OF-MINUS-ONE))
 (5 5 (:REWRITE NOT-SBVLT-OF-MAXINT))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (3 3 (:REWRITE BOOLOR-OF-CONSTANT-ARG2))
 (3 3 (:REWRITE BOOLOR-OF-CONSTANT-ARG1))
 )
(BOOLOR-OF-SBVLT-OF-CONSTANT-AND-SBVLT-OF-CONSTANT-2
 (6252 132 (:DEFINITION EXPT))
 (4487 48 (:REWRITE <-OF-LOGEXT-TRUE))
 (3854 58 (:REWRITE LOGEXT-WHEN-SIGNED-BYTE-P))
 (3831 48 (:REWRITE <-OF-LOGEXT-FALSE))
 (3744 52 (:DEFINITION SIGNED-BYTE-P))
 (2659 58 (:REWRITE LOGEXT-WHEN-TOP-BIT-0))
 (2168 132 (:REWRITE ZIP-OPEN))
 (2152 212 (:REWRITE COMMUTATIVITY-OF-+))
 (1612 52 (:DEFINITION INTEGER-RANGE-P))
 (1516 212 (:REWRITE FOLD-CONSTS-IN-+))
 (1367 824 (:REWRITE DEFAULT-+-2))
 (1255 1255 (:TYPE-PRESCRIPTION RATIONALP-EXPT-TYPE-PRESCRIPTION))
 (1255 1255 (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE))
 (1196 52 (:LINEAR GETBIT-BOUND-LINEAR))
 (888 550 (:REWRITE DEFAULT-<-1))
 (848 550 (:REWRITE DEFAULT-<-2))
 (824 824 (:REWRITE DEFAULT-+-1))
 (704 104 (:REWRITE GETBIT-WHEN-N-IS-NEGATIVE))
 (644 644 (:REWRITE <-WHEN-BVLT))
 (636 212 (:REWRITE DEFAULT-*-2))
 (624 624 (:TYPE-PRESCRIPTION GETBIT-TYPE))
 (619 619 (:REWRITE INTEGERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (525 75 (:REWRITE +-OF---AND-0))
 (448 85 (:DEFINITION POSP))
 (400 80 (:REWRITE UNICITY-OF-0))
 (341 31 (:LINEAR <-OF-LOGEXT-SAME-LINEAR))
 (336 336 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (336 336 (:REWRITE ACL2-NUMBERP-WHEN-UNSIGNED-BYTE-P))
 (336 336 (:REWRITE ACL2-NUMBERP-FROM-UNSIGNED-BYTE-P-SIZE-PARAM))
 (328 328 (:REWRITE BOUND-WHEN-USB))
 (320 80 (:DEFINITION FIX))
 (282 94 (:REWRITE DEFAULT-UNARY-MINUS))
 (219 58 (:REWRITE LOGEXT-WHEN-SIZE-NOT-POSP))
 (217 31 (:LINEAR <=-OF-LOGEXT-LINEAR-UPPER))
 (217 31 (:LINEAR <-OF-LOGEXT-LINEAR-LOWER))
 (217 31 (:DEFINITION NATP))
 (212 212 (:REWRITE DEFAULT-*-1))
 (208 104 (:REWRITE GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER))
 (208 104 (:REWRITE GETBIT-WHEN-NOT-1))
 (208 104 (:REWRITE GETBIT-WHEN-NOT-0))
 (208 104 (:REWRITE GETBIT-TOO-HIGH-CHEAP-2))
 (179 104 (:REWRITE GETBIT-WHEN-NOT-INTEGERP-ARG1))
 (132 132 (:REWRITE EQUAL-WHEN-BVLT-ALT))
 (132 132 (:REWRITE EQUAL-WHEN-BVLT))
 (132 132 (:REWRITE EQUAL-OF-CONSTANT-WHEN-SBVLT))
 (132 132 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-2))
 (132 132 (:REWRITE EQUAL-OF-CONSTANT-WHEN-NOT-BVLT-CONSTANT-1))
 (132 132 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2-ALT))
 (132 132 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-2))
 (132 132 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1-ALT))
 (132 132 (:REWRITE EQUAL-OF-CONSTANT-WHEN-BVLT-CONSTANT-1))
 (132 132 (:REWRITE EQUAL-OF-0-WHEN-BVLT))
 (132 132 (:REWRITE EQUAL-CONSTANT-WHEN-NOT-SBVLT))
 (132 132 (:REWRITE EQUAL-CONSTANT-WHEN-BVCHOP-EQUAL-CONSTANT-FALSE))
 (112 112 (:TYPE-PRESCRIPTION UNSIGNED-BYTE-P))
 (110 58 (:REWRITE LOGEXT-WHEN-I-IS-NOT-AN-INTEGER))
 (104 104 (:REWRITE GETBIT-WHEN-SLICE-IS-KNOWN-CONSTANT))
 (104 104 (:REWRITE GETBIT-WHEN-EQUAL-OF-CONSTANT-AND-BVCHOP-CONSTANT-VERSION))
 (85 85 (:TYPE-PRESCRIPTION POSP))
 (52 52 (:TYPE-PRESCRIPTION SIGNED-BYTE-P))
 (46 5 (:REWRITE SBVLT-BECOMES-BVLT-BETTER))
 (31 31 (:TYPE-PRESCRIPTION NATP))
 (31 31 (:REWRITE SIZE-NON-NEGATIVE-WHEN-UNSIGNED-BYTE-P-FREE))
 (31 31 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P-SIZE-ARG))
 (31 31 (:REWRITE NATP-WHEN-UNSIGNED-BYTE-P))
 (10 5 (:REWRITE NOT-SBVLT-WHEN-SBVLT-REV-CHEAP))
 (9 5 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG3))
 (9 5 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-ARG2))
 (5 5 (:REWRITE SBVLT-WHEN-NOT-INTEGERP-OF-SIZE))
 (5 5 (:REWRITE SBVLT-WHEN-<))
 (5 5 (:REWRITE SBVLT-TRIM-CONSTANT-RIGHT))
 (5 5 (:REWRITE SBVLT-TRIM-CONSTANT-LEFT))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-FREE-BACK))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-FREE))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-3-B))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-3-A))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-2-B))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-2-A))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-1-B))
 (5 5 (:REWRITE SBVLT-TRANSITIVE-1-A))
 (5 5 (:REWRITE SBVLT-SUBST-CONSTANT-SAME-ARG2))
 (5 5 (:REWRITE SBVLT-SUBST-CONSTANT-ALT))
 (5 5 (:REWRITE SBVLT-SUBST-CONSTANT))
 (5 5 (:REWRITE SBVLT-OF-MINUS-ONE))
 (5 5 (:REWRITE NOT-SBVLT-OF-MAXINT))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-UNSIGNED-BYTE-P-SMALLER))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-WHEN-<=-CHEAP))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUNDS))
 (4 4 (:REWRITE UNSIGNED-BYTE-P-FROM-BOUND))
 (3 3 (:REWRITE BOOLOR-OF-CONSTANT-ARG2))
 (3 3 (:REWRITE BOOLOR-OF-CONSTANT-ARG1))
 )
