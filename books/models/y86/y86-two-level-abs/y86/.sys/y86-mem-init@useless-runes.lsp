(RMBYTES
 (4 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE LOGAND-ASH-THM-1))
 (2 1 (:TYPE-PRESCRIPTION NATP-RM08))
 (1 1 (:REWRITE ZP-OPEN))
 (1 1 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 )
(M86-CLEAR-MEM-DWORD-ADDR
 (88 2 (:REWRITE LOGAND-ASH-THM-1))
 (31 31 (:TYPE-PRESCRIPTION LOGAND-GREATER-OR-EQUAL-TO-ZERO))
 (25 25 (:REWRITE DEFAULT-<-2))
 (25 25 (:REWRITE DEFAULT-<-1))
 (6 2 (:LINEAR N64P-LOGAND-N64P-LESS-THAN-18446744073709551616))
 (5 2 (:LINEAR N48P-LOGAND-N48P-LESS-THAN-281474976710656))
 (5 2 (:LINEAR LOGAND-LESS-THAN-OR-EQUAL))
 (5 1 (:LINEAR N20P-LOGAND-N20P-LESS-THAN-1048576))
 (5 1 (:LINEAR N16P-LOGAND-N16P-LESS-THAN-65536))
 (5 1 (:LINEAR N12P-LOGAND-N12P-LESS-THAN-4096))
 (5 1 (:LINEAR N08P-LOGAND-N08P-LESS-THAN-256))
 (5 1 (:LINEAR N05P-LOGAND-N05P-LESS-THAN-32))
 (5 1 (:LINEAR N04P-LOGAND-N04P-LESS-THAN-16))
 (5 1 (:LINEAR N03P-LOGAND-N03P-LESS-THAN-8))
 (5 1 (:LINEAR N02P-LOGAND-N02P-LESS-THAN-4))
 (5 1 (:LINEAR N01P-LOGAND-N01P-LESS-THAN-2))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 (3 1 (:LINEAR N32P-LOGAND-N32P-LESS-THAN-4294967296))
 (3 1 (:LINEAR N30P-LOGAND-N30P-LESS-THAN-1073741824))
 (3 1 (:LINEAR N24P-LOGAND-N24P-LESS-THAN-16777216))
 (2 2 (:REWRITE ZP-OPEN))
 (2 2 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 )
(ASH-ADDR--2-IS-LESS-WITH-EXPLODED-N32P
 (1 1 (:REWRITE GL::SHAPE-SPEC-OBJ-IN-RANGE-BACKCHAIN-INTEGER-2))
 )
(M86-CLEAR-MEM
 (18 18 (:REWRITE DEFAULT-<-2))
 (18 18 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-+-2))
 (3 3 (:REWRITE DEFAULT-+-1))
 )
(M86-REGP
 (4 4 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (2 1 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (1 1 (:TYPE-PRESCRIPTION ATOM-LISTP))
 )
(M86-REG-UPDATES
 (782 263 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (512 512 (:TYPE-PRESCRIPTION BOOLEANP))
 (270 263 (:REWRITE LOGAND-ASH-THM-1))
 (24 24 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (20 10 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (13 13 (:REWRITE DEFAULT-<-2))
 (13 13 (:REWRITE DEFAULT-<-1))
 (7 7 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 (3 1 (:DEFINITION NATP))
 )
(M86-MEMP)
(M86-MEM-UPDATES
 (30 28 (:REWRITE DEFAULT-<-1))
 (28 28 (:REWRITE DEFAULT-<-2))
 (26 26 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (22 11 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (2 2 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(M32-GET-REGS-AND-FLAGS
 (16 8 (:TYPE-PRESCRIPTION NATP-RGFI))
 (2 1 (:TYPE-PRESCRIPTION NATP-EIP))
 )
(M86-CLEAR-REGS)
(INIT-Y86-STATE
 (208 78 (:REWRITE EQUAL-OF-BOOLEANS-REWRITE))
 (128 128 (:TYPE-PRESCRIPTION BOOLEANP))
 (80 78 (:REWRITE LOGAND-ASH-THM-1))
 (74 74 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (48 8 (:REWRITE ALISTP-WHEN-HONS-DUPLICITY-ALIST-P))
 (32 25 (:REWRITE DEFAULT-<-1))
 (25 25 (:REWRITE DEFAULT-<-2))
 (24 8 (:REWRITE HONS-DUPLICITY-ALIST-P-WHEN-NOT-CONSP))
 (16 16 (:TYPE-PRESCRIPTION HONS-DUPLICITY-ALIST-P))
 (15 1 (:DEFINITION M86-MEMP))
 (14 7 (:REWRITE CONSP-OF-CAR-WHEN-ATOM-LISTP))
 (12 6 (:REWRITE GL::NFIX-NATP))
 (6 6 (:TYPE-PRESCRIPTION NATP))
 (2 2 (:REWRITE DEFAULT-SYMBOL-PACKAGE-NAME))
 )
