(SUB-DIFFERENCE)
(APPLY-SIGMA-TAU)
(COMPOSER)
(PARALLEL-TO-SERIAL-SUB)
(COLLECT-NODES)
(SET-SUB-NODE
 (5 5 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(SET-WP-NODE
 (5 5 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(SET-PREV-NODE)
(DECREMENT-MARK-NODE
 (5 5 (:TYPE-PRESCRIPTION BINARY-APPEND))
 (1 1 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(SET-NODE-GRAPH)
(UPDATE-NODE-WITH-BRANCH
 (26 5 (:TYPE-PRESCRIPTION SET-PREV-NODE))
 (8 8 (:TYPE-PRESCRIPTION BINARY-APPEND))
 )
(UPDATE-GRAPH-WITH-BRANCH)
(UPDATE-GRAPH-WITH-BRANCH-LIST)
(ADD-LINE-BRANCHES
 (6 6 (:TYPE-PRESCRIPTION UPDATE-GRAPH-WITH-BRANCH-LIST))
 )
(MAKE-GRAPH)
(FIND-MIN-MARK)
(UPDATE-WP-GRAPH)
(MAKE-WP-STRING)
(MAKE-OR)
(MAKE-AND)
(ACC-WP
 (5 5 (:TYPE-PRESCRIPTION MAKE-OR))
 )
(INIT-WP)
(ACC-WP-LIST)
(REMOVE-NODE)
(SET-NODE-GRAPH-CONSERVES-LENGTH
 (63 31 (:REWRITE DEFAULT-CAR))
 (42 21 (:REWRITE DEFAULT-+-2))
 (39 37 (:REWRITE DEFAULT-CDR))
 (32 8 (:REWRITE O-P-O-INFP-CAR))
 (21 21 (:REWRITE DEFAULT-+-1))
 (14 14 (:META CANCEL_TIMES-EQUAL-CORRECT))
 (14 14 (:META CANCEL_PLUS-EQUAL-CORRECT))
 (8 8 (:REWRITE O-P-DEF-O-FINP-1))
 (1 1 (:REWRITE EQUAL-CONSTANT-+))
 )
(WP-GEN-GRAPH
 (6 6 (:TYPE-PRESCRIPTION ACC-WP-LIST))
 (4 4 (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|))
 )
(ADD-COUNT-SUB-NODE)
(ADD-COUNT-SUB-GRAPH)
(COLLECT-VARS-SUB)
(COLLECT-VARS-BRANCH)
(COLLECT-VARS-NODE)
(COLLECT-VARS-GRAPH)
(CHK-VARS-PROG)
(WP-GEN)
(COLLECT-WP-NODE)
(COLLECT-WPS-MUTUAL)
(COLLECT-WPS)
(RUN-WP-LIST)
