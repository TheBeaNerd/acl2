(C::BINOP-STRICTP)
(C::BOOLEANP-OF-BINOP-STRICTP)
(C::BINOP-STRICTP-OF-BINOP-FIX-OP
 (3 1 (:REWRITE C::BINOP-FIX-WHEN-BINOPP))
 (2 2 (:TYPE-PRESCRIPTION C::BINOPP))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-SUB))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-SHR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-SHL))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-REM))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-NE))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-MUL))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-LT))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-LOGOR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-LOGAND))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-LE))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-GT))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-GE))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-EQ))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-DIV))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-BITXOR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-BITIOR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-BITAND))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-XOR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-SUB))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-SHR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-SHL))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-REM))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-MUL))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-IOR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-DIV))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-AND))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-ADD))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ADD))
 )
(C::BINOP-STRICTP-BINOP-EQUIV-CONGRUENCE-ON-OP)
(C::BINOP-PUREP)
(C::BOOLEANP-OF-BINOP-PUREP)
(C::BINOP-PUREP-OF-BINOP-FIX-OP
 (3 1 (:REWRITE C::BINOP-FIX-WHEN-BINOPP))
 (2 2 (:TYPE-PRESCRIPTION C::BINOPP))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-SUB))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-SHR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-SHL))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-REM))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-NE))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-MUL))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-LT))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-LOGOR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-LOGAND))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-LE))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-GT))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-GE))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-EQ))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-DIV))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-BITXOR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-BITIOR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-BITAND))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-XOR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-SUB))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-SHR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-SHL))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-REM))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-MUL))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-IOR))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-DIV))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-AND))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG-ADD))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ASG))
 (2 1 (:REWRITE C::BINOP-FIX-WHEN-ADD))
 )
(C::BINOP-PUREP-BINOP-EQUIV-CONGRUENCE-ON-OP)
(C::OBJ-DECLOR-TO-IDENT+ADECLOR
 (6 2 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE DEFAULT-<-1))
 )
(C::IDENTP-OF-OBJ-DECLOR-TO-IDENT+ADECLOR.ID
 (14 14 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::OBJ-ADECLORP-OF-OBJ-DECLOR-TO-IDENT+ADECLOR.ADECLOR)
(C::OBJ-DECLOR-TO-IDENT+ADECLOR
 (5 1 (:DEFINITION C::OBJ-DECLOR-TO-IDENT+ADECLOR))
 )
(C::OBJ-DECLOR-TO-IDENT+ADECLOR-OF-OBJ-DECLOR-FIX-DECLOR)
(C::OBJ-DECLOR-TO-IDENT+ADECLOR-OBJ-DECLOR-EQUIV-CONGRUENCE-ON-DECLOR)
(C::IDENT+ADECLOR-TO-OBJ-DECLOR
 (6 2 (:REWRITE DEFAULT-<-2))
 (6 2 (:REWRITE DEFAULT-<-1))
 )
(C::OBJ-DECLORP-OF-IDENT+ADECLOR-TO-OBJ-DECLOR)
(C::IDENT+ADECLOR-TO-OBJ-DECLOR
 (4 4 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::IDENT+ADECLOR-TO-OBJ-DECLOR-OF-OBJ-DECLOR-TO-IDENT+ADECLOR
 (23 10 (:REWRITE DEFAULT-CDR))
 (23 10 (:REWRITE DEFAULT-CAR))
 (22 22 (:TYPE-PRESCRIPTION C::OBJ-ADECLOR-KIND$INLINE))
 (4 2 (:REWRITE C::OBJ-ADECLOR-FIX-WHEN-NONE))
 (2 1 (:REWRITE C::ICONST-OPTION-FIX-WHEN-NONE))
 (1 1 (:TYPE-PRESCRIPTION C::OBJ-DECLOR-ARRAY->SIZE$INLINE))
 )
(C::OBJ-DECLOR-TO-IDENT+ADECLOR-OF-IDENT+ADECLOR-TO-OBJ-DECLOR
 (96 96 (:TYPE-PRESCRIPTION C::OBJ-DECLOR-KIND$INLINE))
 (90 24 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (78 48 (:REWRITE DEFAULT-CDR))
 (78 48 (:REWRITE DEFAULT-CAR))
 (44 44 (:TYPE-PRESCRIPTION C::IDENTP))
 (22 22 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 (4 2 (:REWRITE C::ICONST-OPTION-FIX-WHEN-NONE))
 (2 2 (:TYPE-PRESCRIPTION C::OBJ-ADECLOR-ARRAY->SIZE$INLINE))
 )
(C::IDENT+ADECLOR-TO-OBJ-DECLOR-OF-IDENT-FIX-ID
 (20 5 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (10 10 (:TYPE-PRESCRIPTION C::IDENTP))
 (8 4 (:REWRITE DEFAULT-CDR))
 (8 4 (:REWRITE DEFAULT-CAR))
 (5 5 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::IDENT+ADECLOR-TO-OBJ-DECLOR-IDENT-EQUIV-CONGRUENCE-ON-ID)
(C::IDENT+ADECLOR-TO-OBJ-DECLOR-OF-OBJ-ADECLOR-FIX-ADECLOR)
(C::IDENT+ADECLOR-TO-OBJ-DECLOR-OBJ-ADECLOR-EQUIV-CONGRUENCE-ON-ADECLOR)
(C::FUN-DECLOR-TO-IDENT+ADECLOR
 (3 1 (:REWRITE DEFAULT-<-2))
 (3 1 (:REWRITE DEFAULT-<-1))
 )
(C::IDENTP-OF-FUN-DECLOR-TO-IDENT+ADECLOR.ID
 (8 8 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::FUN-ADECLORP-OF-FUN-DECLOR-TO-IDENT+ADECLOR.ADECLOR)
(C::FUN-DECLOR-TO-IDENT+ADECLOR)
(C::FUN-DECLOR-TO-IDENT+ADECLOR-OF-FUN-DECLOR-FIX-DECLOR)
(C::FUN-DECLOR-TO-IDENT+ADECLOR-FUN-DECLOR-EQUIV-CONGRUENCE-ON-DECLOR)
(C::IDENT+ADECLOR-TO-FUN-DECLOR
 (3 1 (:REWRITE DEFAULT-<-2))
 (3 1 (:REWRITE DEFAULT-<-1))
 )
(C::FUN-DECLORP-OF-IDENT+ADECLOR-TO-FUN-DECLOR)
(C::IDENT+ADECLOR-TO-FUN-DECLOR
 (3 3 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::IDENT+ADECLOR-TO-FUN-DECLOR-OF-FUN-DECLOR-TO-IDENT+ADECLOR
 (19 8 (:REWRITE DEFAULT-CDR))
 (19 8 (:REWRITE DEFAULT-CAR))
 (8 8 (:TYPE-PRESCRIPTION C::FUN-ADECLOR-KIND$INLINE))
 )
(C::FUN-DECLOR-TO-IDENT+ADECLOR-OF-IDENT+ADECLOR-TO-FUN-DECLOR
 (53 14 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (42 26 (:REWRITE DEFAULT-CDR))
 (42 26 (:REWRITE DEFAULT-CAR))
 (26 26 (:TYPE-PRESCRIPTION C::IDENTP))
 (26 26 (:TYPE-PRESCRIPTION C::FUN-DECLOR-KIND$INLINE))
 (13 13 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::IDENT+ADECLOR-TO-FUN-DECLOR-OF-IDENT-FIX-ID
 (12 3 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (6 6 (:TYPE-PRESCRIPTION C::IDENTP))
 (4 2 (:REWRITE DEFAULT-CDR))
 (4 2 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::IDENT+ADECLOR-TO-FUN-DECLOR-IDENT-EQUIV-CONGRUENCE-ON-ID)
(C::IDENT+ADECLOR-TO-FUN-DECLOR-OF-FUN-ADECLOR-FIX-ADECLOR)
(C::IDENT+ADECLOR-TO-FUN-DECLOR-FUN-ADECLOR-EQUIV-CONGRUENCE-ON-ADECLOR)
(C::FUN-ADECLOR-TO-PARAMS+DECLOR
 (3 1 (:REWRITE DEFAULT-<-2))
 (3 1 (:REWRITE DEFAULT-<-1))
 )
(C::PARAM-DECLON-LISTP-OF-FUN-ADECLOR-TO-PARAMS+DECLOR.PARAMS
 (8 8 (:REWRITE C::PARAM-DECLON-LISTP-WHEN-NOT-CONSP))
 )
(C::OBJ-ADECLORP-OF-FUN-ADECLOR-TO-PARAMS+DECLOR.DECLOR)
(C::FUN-ADECLOR-TO-PARAMS+DECLOR)
(C::FUN-ADECLOR-TO-PARAMS+DECLOR-OF-FUN-ADECLOR-FIX-DECLOR)
(C::FUN-ADECLOR-TO-PARAMS+DECLOR-FUN-ADECLOR-EQUIV-CONGRUENCE-ON-DECLOR)
(C::TYSPEC+DECLOR-TO-IDENT+TYNAME)
(C::IDENTP-OF-TYSPEC+DECLOR-TO-IDENT+TYNAME.ID)
(C::TYNAMEP-OF-TYSPEC+DECLOR-TO-IDENT+TYNAME.TYNAME)
(C::TYSPEC+DECLOR-TO-IDENT+TYNAME-OF-TYSPECSEQ-FIX-TYSPEC
 (8 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-TYSPECSEQP))
 (5 5 (:TYPE-PRESCRIPTION C::TYSPECSEQ-KIND$INLINE))
 (5 1 (:REWRITE C::TYSPECSEQP-WHEN-TYSPECSEQ-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::TYSPECSEQP))
 (2 2 (:TYPE-PRESCRIPTION C::TYSPECSEQ-OPTIONP))
 (2 1 (:REWRITE C::TYSPECSEQ-OPTIONP-WHEN-TYSPECSEQP))
 (2 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-VOID))
 (2 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-UCHAR))
 (2 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-SCHAR))
 (2 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-CHAR))
 (2 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-BOOL))
 )
(C::TYSPEC+DECLOR-TO-IDENT+TYNAME-TYSPECSEQ-EQUIV-CONGRUENCE-ON-TYSPEC)
(C::TYSPEC+DECLOR-TO-IDENT+TYNAME-OF-OBJ-DECLOR-FIX-DECLOR)
(C::TYSPEC+DECLOR-TO-IDENT+TYNAME-OBJ-DECLOR-EQUIV-CONGRUENCE-ON-DECLOR)
(C::IDENT+TYNAME-TO-TYSPEC+DECLOR)
(C::TYSPECSEQP-OF-IDENT+TYNAME-TO-TYSPEC+DECLOR.TYSPEC)
(C::OBJ-DECLORP-OF-IDENT+TYNAME-TO-TYSPEC+DECLOR.DECLOR)
(C::IDENT+TYNAME-TO-TYSPEC+DECLOR-OF-TYSPEC+DECLOR-TO-IDENT+TYNAME
 (10 10 (:TYPE-PRESCRIPTION C::TYSPECSEQ-KIND$INLINE))
 (9 2 (:REWRITE C::TYSPECSEQ-FIX-WHEN-TYSPECSEQP))
 (5 1 (:REWRITE C::TYSPECSEQP-WHEN-TYSPECSEQ-OPTIONP))
 (4 2 (:REWRITE C::TYSPECSEQ-FIX-WHEN-VOID))
 (4 2 (:REWRITE C::TYSPECSEQ-FIX-WHEN-UCHAR))
 (4 2 (:REWRITE C::TYSPECSEQ-FIX-WHEN-SCHAR))
 (4 2 (:REWRITE C::TYSPECSEQ-FIX-WHEN-CHAR))
 (4 2 (:REWRITE C::TYSPECSEQ-FIX-WHEN-BOOL))
 (4 2 (:REWRITE C::OBJ-DECLOR-FIX-WHEN-OBJ-DECLORP))
 (3 3 (:TYPE-PRESCRIPTION C::TYSPECSEQP))
 (2 2 (:TYPE-PRESCRIPTION C::TYSPECSEQ-OPTIONP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJ-DECLORP))
 (2 1 (:REWRITE C::TYSPECSEQ-OPTIONP-WHEN-TYSPECSEQP))
 (2 1 (:REWRITE C::OBJ-ADECLOR-FIX-WHEN-NONE))
 (1 1 (:TYPE-PRESCRIPTION C::OBJ-ADECLOR-KIND$INLINE))
 )
(C::TYSPEC+DECLOR-TO-IDENT+TYNAME-OF-IDENT+TYNAME-TO-TYSPEC+DECLOR
 (5 2 (:REWRITE C::IDENT-FIX-WHEN-IDENTP))
 (4 2 (:REWRITE C::TYNAME-FIX-WHEN-TYNAMEP))
 (2 2 (:TYPE-PRESCRIPTION C::TYNAMEP))
 (2 2 (:TYPE-PRESCRIPTION C::IDENTP))
 (2 1 (:REWRITE C::OBJ-ADECLOR-FIX-WHEN-NONE))
 (1 1 (:TYPE-PRESCRIPTION C::OBJ-ADECLOR-KIND$INLINE))
 (1 1 (:REWRITE C::IDENTP-WHEN-IN-IDENT-SETP-BINDS-FREE-X))
 )
(C::IDENT+TYNAME-TO-TYSPEC+DECLOR-OF-IDENT-FIX-ID)
(C::IDENT+TYNAME-TO-TYSPEC+DECLOR-IDENT-EQUIV-CONGRUENCE-ON-ID)
(C::IDENT+TYNAME-TO-TYSPEC+DECLOR-OF-TYNAME-FIX-TYNAME)
(C::IDENT+TYNAME-TO-TYSPEC+DECLOR-TYNAME-EQUIV-CONGRUENCE-ON-TYNAME)
(C::TYSPEC+DECLOR-TO-IDENT+PARAMS+TYNAME)
(C::IDENTP-OF-TYSPEC+DECLOR-TO-IDENT+PARAMS+TYNAME.ID)
(C::PARAM-DECLON-LISTP-OF-TYSPEC+DECLOR-TO-IDENT+PARAMS+TYNAME.PARAMS)
(C::TYNAMEP-OF-TYSPEC+DECLOR-TO-IDENT+PARAMS+TYNAME.TYNAME)
(C::TYSPEC+DECLOR-TO-IDENT+PARAMS+TYNAME-OF-TYSPECSEQ-FIX-TYSPEC
 (8 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-TYSPECSEQP))
 (5 5 (:TYPE-PRESCRIPTION C::TYSPECSEQ-KIND$INLINE))
 (5 1 (:REWRITE C::TYSPECSEQP-WHEN-TYSPECSEQ-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::TYSPECSEQP))
 (2 2 (:TYPE-PRESCRIPTION C::TYSPECSEQ-OPTIONP))
 (2 1 (:REWRITE C::TYSPECSEQ-OPTIONP-WHEN-TYSPECSEQP))
 (2 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-VOID))
 (2 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-UCHAR))
 (2 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-SCHAR))
 (2 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-CHAR))
 (2 1 (:REWRITE C::TYSPECSEQ-FIX-WHEN-BOOL))
 )
(C::TYSPEC+DECLOR-TO-IDENT+PARAMS+TYNAME-TYSPECSEQ-EQUIV-CONGRUENCE-ON-TYSPEC)
(C::TYSPEC+DECLOR-TO-IDENT+PARAMS+TYNAME-OF-FUN-DECLOR-FIX-DECLOR)
(C::TYSPEC+DECLOR-TO-IDENT+PARAMS+TYNAME-FUN-DECLOR-EQUIV-CONGRUENCE-ON-DECLOR)
(C::STRUCT-DECLON-TO-IDENT+TYNAME)
(C::IDENTP-OF-STRUCT-DECLON-TO-IDENT+TYNAME.ID)
(C::TYNAMEP-OF-STRUCT-DECLON-TO-IDENT+TYNAME.TYNAME)
(C::STRUCT-DECLON-TO-IDENT+TYNAME-OF-STRUCT-DECLON-FIX-DECLON)
(C::STRUCT-DECLON-TO-IDENT+TYNAME-STRUCT-DECLON-EQUIV-CONGRUENCE-ON-DECLON)
(C::PARAM-DECLON-TO-IDENT+TYNAME)
(C::IDENTP-OF-PARAM-DECLON-TO-IDENT+TYNAME.ID)
(C::TYNAMEP-OF-PARAM-DECLON-TO-IDENT+TYNAME.TYNAME)
(C::PARAM-DECLON-TO-IDENT+TYNAME-OF-PARAM-DECLON-FIX-DECLON)
(C::PARAM-DECLON-TO-IDENT+TYNAME-PARAM-DECLON-EQUIV-CONGRUENCE-ON-DECLON)
(C::PARAM-DECLON-LIST-TO-IDENT+TYNAME-LISTS
 (3 3 (:REWRITE C::PARAM-DECLON-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(C::IDENT-LISTP-OF-PARAM-DECLON-LIST-TO-IDENT+TYNAME-LISTS.IDS
 (9 9 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(C::TYNAME-LISTP-OF-PARAM-DECLON-LIST-TO-IDENT+TYNAME-LISTS.TYNAMES
 (9 9 (:REWRITE C::TYNAME-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(C::LEN-OF-PARAM-DECLON-LIST-TO-IDENT+TYNAME-LISTS.IDS
 (14 7 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(C::LEN-OF-PARAM-DECLON-LIST-TO-IDENT+TYNAME-LISTS.TYNAMES
 (14 7 (:REWRITE DEFAULT-+-2))
 (8 8 (:REWRITE DEFAULT-CDR))
 (7 7 (:REWRITE DEFAULT-+-1))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(C::PARAM-DECLON-LIST-TO-IDENT+TYNAME-LISTS-OF-PARAM-DECLON-LIST-FIX-DECLONS
 (200 114 (:REWRITE DEFAULT-CDR))
 (116 21 (:REWRITE C::PARAM-DECLON-LIST-FIX-WHEN-PARAM-DECLON-LISTP))
 (115 92 (:REWRITE DEFAULT-CAR))
 (32 8 (:REWRITE C::PARAM-DECLON-LISTP-OF-CDR-WHEN-PARAM-DECLON-LISTP))
 (30 29 (:REWRITE C::PARAM-DECLON-LISTP-WHEN-NOT-CONSP))
 )
(C::PARAM-DECLON-LIST-TO-IDENT+TYNAME-LISTS-PARAM-DECLON-LIST-EQUIV-CONGRUENCE-ON-DECLONS)
(C::OBJ-DECLON-TO-IDENT+TYNAME+INIT)
(C::IDENTP-OF-OBJ-DECLON-TO-IDENT+TYNAME+INIT.ID)
(C::TYNAMEP-OF-OBJ-DECLON-TO-IDENT+TYNAME+INIT.TYNAME)
(C::INITERP-OF-OBJ-DECLON-TO-IDENT+TYNAME+INIT.INIT)
(C::OBJ-DECLON-TO-IDENT+TYNAME+INIT-OF-OBJ-DECLON-FIX-DECLON
 (3 1 (:REWRITE C::OBJ-DECLON-FIX-WHEN-OBJ-DECLONP))
 (2 2 (:TYPE-PRESCRIPTION C::OBJ-DECLONP))
 )
(C::OBJ-DECLON-TO-IDENT+TYNAME+INIT-OBJ-DECLON-EQUIV-CONGRUENCE-ON-DECLON)
(C::EXT-DECLON-LIST->FUNDEF-LIST
 (7 7 (:REWRITE C::EXT-DECLON-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(C::FUNDEF-LISTP-OF-EXT-DECLON-LIST->FUNDEF-LIST
 (79 21 (:REWRITE C::FUNDEF-LISTP-WHEN-NOT-CONSP))
 (15 15 (:REWRITE DEFAULT-CAR))
 (3 3 (:REWRITE DEFAULT-CDR))
 )
(C::EXT-DECLON-LIST->FUNDEF-LIST-OF-EXT-DECLON-LIST-FIX-EXTS
 (807 418 (:REWRITE DEFAULT-CDR))
 (418 72 (:REWRITE C::EXT-DECLON-LIST-FIX-WHEN-EXT-DECLON-LISTP))
 (373 206 (:REWRITE DEFAULT-CAR))
 (128 32 (:REWRITE C::EXT-DECLON-LISTP-OF-CDR-WHEN-EXT-DECLON-LISTP))
 (111 104 (:REWRITE C::EXT-DECLON-LISTP-WHEN-NOT-CONSP))
 )
(C::EXT-DECLON-LIST->FUNDEF-LIST-EXT-DECLON-LIST-EQUIV-CONGRUENCE-ON-EXTS)
(C::FUNDEF->NAME)
(C::IDENTP-OF-FUNDEF->NAME)
(C::FUNDEF->NAME-OF-FUNDEF-FIX-FUNDEF)
(C::FUNDEF->NAME-FUNDEF-EQUIV-CONGRUENCE-ON-FUNDEF)
(C::FUNDEF-LIST->NAME-LIST-EXEC)
(C::FUNDEF-LIST->NAME-LIST-NREV)
(C::FUNDEF-LIST->NAME-LIST)
(C::IDENT-LISTP-OF-FUNDEF-LIST->NAME-LIST
 (33 9 (:REWRITE C::IDENT-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(C::FUNDEF-LIST->NAME-LIST-NIL-PRESERVINGP-LEMMA)
(C::FUNDEF-LIST->NAME-LIST-NREV-REMOVAL
 (170 5 (:REWRITE LIST-FIX-WHEN-TRUE-LISTP))
 (112 10 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (93 5 (:DEFINITION TRUE-LISTP))
 (64 5 (:REWRITE LIST-FIX-WHEN-LEN-ZERO))
 (36 36 (:TYPE-PRESCRIPTION RCONS))
 (29 5 (:DEFINITION LEN))
 (25 25 (:TYPE-PRESCRIPTION TRUE-LISTP))
 (24 20 (:REWRITE DEFAULT-CDR))
 (20 20 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (20 10 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (20 10 (:REWRITE C::SETP-WHEN-IDENT-SETP))
 (20 10 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (10 10 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (10 10 (:TYPE-PRESCRIPTION C::IDENT-SETP))
 (10 10 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (10 10 (:REWRITE SET::IN-SET))
 (10 10 (:REWRITE DEFAULT-CAR))
 (10 5 (:REWRITE DEFAULT-+-2))
 (7 5 (:REWRITE LIST-FIX-WHEN-NOT-CONSP))
 (5 5 (:REWRITE DEFAULT-+-1))
 )
(C::FUNDEF-LIST->NAME-LIST-EXEC-REMOVAL
 (5 5 (:REWRITE DEFAULT-CDR))
 (5 5 (:REWRITE DEFAULT-CAR))
 )
(C::FUNDEF-LIST->NAME-LIST-OF-REV)
(C::FUNDEF-LIST->NAME-LIST-OF-LIST-FIX)
(C::FUNDEF-LIST->NAME-LIST-OF-APPEND)
(C::CDR-OF-FUNDEF-LIST->NAME-LIST)
(C::CAR-OF-FUNDEF-LIST->NAME-LIST)
(C::FUNDEF-LIST->NAME-LIST-UNDER-IFF)
(C::CONSP-OF-FUNDEF-LIST->NAME-LIST)
(C::LEN-OF-FUNDEF-LIST->NAME-LIST)
(C::TRUE-LISTP-OF-FUNDEF-LIST->NAME-LIST)
(C::FUNDEF-LIST->NAME-LIST-WHEN-NOT-CONSP)
(C::FUNDEF-LIST->NAME-LIST-OF-CONS)
(C::FUNDEF-LIST->NAME-LIST-NREV
 (40 4 (:REWRITE SET::SETS-ARE-TRUE-LISTS-CHEAP))
 (24 2 (:DEFINITION TRUE-LISTP))
 (8 8 (:TYPE-PRESCRIPTION SET::SETP-TYPE))
 (8 4 (:REWRITE OMAP::SETP-WHEN-MAPP))
 (8 4 (:REWRITE C::SETP-WHEN-IDENT-SETP))
 (8 4 (:REWRITE SET::NONEMPTY-MEANS-SET))
 (4 4 (:TYPE-PRESCRIPTION OMAP::MAPP))
 (4 4 (:TYPE-PRESCRIPTION C::IDENT-SETP))
 (4 4 (:TYPE-PRESCRIPTION SET::EMPTY-TYPE))
 (4 4 (:REWRITE SET::IN-SET))
 (4 4 (:REWRITE C::FUNDEF-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(C::FUNDEF-LIST->NAME-LIST)
(C::FUNDEF-LIST->NAME-LIST-EXEC
 (4 4 (:REWRITE C::FUNDEF-LISTP-WHEN-NOT-CONSP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(C::FUNDEF-LIST->NAME-LIST-OF-FUNDEF-LIST-FIX-X
 (85 44 (:REWRITE DEFAULT-CDR))
 (76 13 (:REWRITE C::FUNDEF-LIST-FIX-WHEN-FUNDEF-LISTP))
 (32 30 (:REWRITE DEFAULT-CAR))
 (24 6 (:REWRITE C::FUNDEF-LISTP-OF-CDR-WHEN-FUNDEF-LISTP))
 (20 19 (:REWRITE C::FUNDEF-LISTP-WHEN-NOT-CONSP))
 )
(C::FUNDEF-LIST->NAME-LIST-FUNDEF-LIST-EQUIV-CONGRUENCE-ON-X)
