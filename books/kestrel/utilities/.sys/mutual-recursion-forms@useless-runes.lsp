(ALL-DEFUN-FORMP)
(DEFUN-FORMP-OF-CAR
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(ALL-DEFUN-FORMP-OF-CDR
 (4 1 (:REWRITE DEFUN-FORMP-OF-CAR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(ALL-DEFUN-FORMP-OF-CONS
 (8 2 (:REWRITE DEFUN-FORMP-OF-CAR))
 (8 2 (:REWRITE ALL-DEFUN-FORMP-OF-CDR))
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(FIND-DEFUN-IN-MUT-REC
 (8 2 (:REWRITE DEFUN-FORMP-OF-CAR))
 (2 2 (:REWRITE DEFAULT-CAR))
 (1 1 (:REWRITE DEFAULT-CDR))
 )
(DEFUN-FORMP-OF-FIND-DEFUN-IN-MUT-REC
 (36 36 (:REWRITE DEFAULT-CAR))
 (21 21 (:REWRITE DEFAULT-CDR))
 )
(ANY-DEFUN-HAS-A-GUARDP
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(ANY-DEFUN-HAS-VERIFY-GUARDS-NILP
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(ANY-DEFUN-HAS-VERIFY-GUARDS-TP
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(REPLACE-XARG-IN-DEFUNS
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(ALL-DEFUN-FORMP-OF-REPLACE-XARG-IN-DEFUNS
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(REMOVE-XARG-IN-DEFUNS
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(REMOVE-HINTS-FROM-DEFUNS
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(ALL-DEFUN-FORMP-OF-REMOVE-XARG-IN-DEFUNS
 (3 3 (:REWRITE DEFAULT-CAR))
 (2 2 (:REWRITE DEFAULT-CDR))
 )
(CONSP-OF-REMOVE-XARG-IN-DEFUNS
 (3 3 (:REWRITE DEFAULT-CDR))
 (3 3 (:REWRITE DEFAULT-CAR))
 )
(ANY-DEFUN-DEMANDS-GUARD-VERIFICATIONP
 (2 1 (:DEFINITION TRUE-LISTP))
 (1 1 (:REWRITE DEFAULT-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
(GET-NAME-ARITY-LIST-FROM-DEFUNS
 (31 30 (:REWRITE DEFAULT-CDR))
 (17 16 (:REWRITE DEFAULT-CAR))
 )
(MUTUAL-RECURSION-FORMP)
(MUTUAL-RECURSION-FORMP-FORWARD-TO-EQUAL-OF-CAR)
(GET-NAME-ARITY-LIST-FROM-MUTUAL-RECURSION)
(REPLACE-XARG-IN-MUTUAL-RECURSION)
(MUTUAL-RECURSION-FORMP-FORWARD-TO-ALL-DEFUN-FORMP-OF-CDR)
(MUTUAL-RECURSION-FORMP-FORWARD-TO-TRUE-LISTP-OF-CDR)
(MUTUAL-RECURSION-DEMANDS-GUARD-VERIFICATIONP)
(ENSURE-MUTUAL-RECURSION-DEMANDS-GUARD-VERIFICATION
 (21 2 (:DEFINITION ANY-DEFUN-HAS-A-GUARDP))
 (14 8 (:REWRITE DEFAULT-CDR))
 (10 4 (:REWRITE DEFAULT-CAR))
 (6 2 (:REWRITE ALL-DEFUN-FORMP-OF-CDR))
 (2 2 (:TYPE-PRESCRIPTION DEFUN-HAS-A-GUARDP))
 )
(REMOVE-HINTS-FROM-MUTUAL-RECURSION
 (6 6 (:REWRITE DEFAULT-CDR))
 (6 2 (:REWRITE ALL-DEFUN-FORMP-OF-CDR))
 (1 1 (:REWRITE DEFAULT-CAR))
 )
