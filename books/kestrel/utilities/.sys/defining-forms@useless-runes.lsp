(DEFUN-OR-MUTUAL-RECURSION-FORMP)
(GET-DECLARES-FROM-EVENT
 (527 266 (:REWRITE DEFAULT-+-2))
 (341 266 (:REWRITE DEFAULT-+-1))
 (210 42 (:DEFINITION LEN))
 (195 195 (:REWRITE DEFAULT-CDR))
 (192 48 (:DEFINITION INTEGER-ABS))
 (192 24 (:DEFINITION LENGTH))
 (157 157 (:REWRITE DEFAULT-CAR))
 (120 90 (:REWRITE DEFAULT-<-2))
 (110 90 (:REWRITE DEFAULT-<-1))
 (60 5 (:DEFINITION TAKE))
 (52 4 (:REWRITE ALL-DECLAREP-OF-TAKE))
 (48 48 (:REWRITE DEFAULT-UNARY-MINUS))
 (24 24 (:REWRITE DEFAULT-REALPART))
 (24 24 (:REWRITE DEFAULT-NUMERATOR))
 (24 24 (:REWRITE DEFAULT-IMAGPART))
 (24 24 (:REWRITE DEFAULT-DENOMINATOR))
 (24 24 (:REWRITE DEFAULT-COERCE-2))
 (24 24 (:REWRITE DEFAULT-COERCE-1))
 (21 7 (:REWRITE ALL-DEFUN-FORMP-OF-CDR))
 (20 5 (:REWRITE ZP-OPEN))
 (9 9 (:TYPE-PRESCRIPTION DECLAREP))
 (4 2 (:DEFINITION TRUE-LISTP))
 )
(ALL-DECLAREP-OF-GET-DECLARES-FROM-EVENT
 (1126 1126 (:REWRITE DEFAULT-CDR))
 (943 943 (:REWRITE DEFAULT-CAR))
 (216 18 (:DEFINITION TAKE))
 (200 136 (:REWRITE DEFAULT-+-2))
 (136 136 (:REWRITE DEFAULT-+-1))
 (120 12 (:REWRITE ALL-DECLAREP-OF-TAKE))
 (74 56 (:REWRITE DEFAULT-<-2))
 (72 18 (:REWRITE ZP-OPEN))
 (60 56 (:REWRITE DEFAULT-<-1))
 (49 49 (:TYPE-PRESCRIPTION DECLAREP))
 (3 1 (:REWRITE ALL-DEFUN-FORMP-OF-CDR))
 )
(GET-XARGS-FROM-EVENT)
(GET-BODY-FROM-EVENT
 (527 266 (:REWRITE DEFAULT-+-2))
 (341 266 (:REWRITE DEFAULT-+-1))
 (210 42 (:DEFINITION LEN))
 (195 195 (:REWRITE DEFAULT-CDR))
 (192 48 (:DEFINITION INTEGER-ABS))
 (192 24 (:DEFINITION LENGTH))
 (157 157 (:REWRITE DEFAULT-CAR))
 (120 90 (:REWRITE DEFAULT-<-2))
 (110 90 (:REWRITE DEFAULT-<-1))
 (60 5 (:DEFINITION TAKE))
 (52 4 (:REWRITE ALL-DECLAREP-OF-TAKE))
 (48 48 (:REWRITE DEFAULT-UNARY-MINUS))
 (24 24 (:REWRITE DEFAULT-REALPART))
 (24 24 (:REWRITE DEFAULT-NUMERATOR))
 (24 24 (:REWRITE DEFAULT-IMAGPART))
 (24 24 (:REWRITE DEFAULT-DENOMINATOR))
 (24 24 (:REWRITE DEFAULT-COERCE-2))
 (24 24 (:REWRITE DEFAULT-COERCE-1))
 (21 7 (:REWRITE ALL-DEFUN-FORMP-OF-CDR))
 (20 5 (:REWRITE ZP-OPEN))
 (9 9 (:TYPE-PRESCRIPTION DECLAREP))
 (4 2 (:DEFINITION TRUE-LISTP))
 )
(EVENT-DEMANDS-GUARD-VERIFICATIONP
 (116 116 (:REWRITE DEFAULT-CDR))
 (100 20 (:DEFINITION LEN))
 (75 75 (:REWRITE DEFAULT-CAR))
 (72 6 (:DEFINITION TAKE))
 (64 44 (:REWRITE DEFAULT-+-2))
 (52 4 (:REWRITE ALL-DECLAREP-OF-TAKE))
 (44 44 (:REWRITE DEFAULT-+-1))
 (32 26 (:REWRITE DEFAULT-<-2))
 (28 26 (:REWRITE DEFAULT-<-1))
 (24 6 (:REWRITE ZP-OPEN))
 (18 6 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:TYPE-PRESCRIPTION DECLAREP))
 (9 3 (:REWRITE ALL-DEFUN-FORMP-OF-CDR))
 (8 4 (:DEFINITION TRUE-LISTP))
 )
(ENSURE-EVENT-DEMANDS-GUARD-VERIFICATION
 (116 116 (:REWRITE DEFAULT-CDR))
 (100 20 (:DEFINITION LEN))
 (75 75 (:REWRITE DEFAULT-CAR))
 (72 6 (:DEFINITION TAKE))
 (64 44 (:REWRITE DEFAULT-+-2))
 (52 4 (:REWRITE ALL-DECLAREP-OF-TAKE))
 (44 44 (:REWRITE DEFAULT-+-1))
 (32 26 (:REWRITE DEFAULT-<-2))
 (28 26 (:REWRITE DEFAULT-<-1))
 (24 6 (:REWRITE ZP-OPEN))
 (18 6 (:REWRITE FOLD-CONSTS-IN-+))
 (10 10 (:TYPE-PRESCRIPTION DECLAREP))
 (9 3 (:REWRITE ALL-DEFUN-FORMP-OF-CDR))
 (8 4 (:DEFINITION TRUE-LISTP))
 )
