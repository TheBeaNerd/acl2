(NUM-HANDLED-NODES-AUX
 (24 1 (:DEFINITION NUM-HANDLED-NODES-AUX))
 (18 15 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-+-1))
 (15 12 (:REWRITE DEFAULT-<-2))
 (12 12 (:REWRITE DEFAULT-<-1))
 (2 2 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (2 2 (:LINEAR ARRAY2P-LINEAR))
 (1 1 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 )
(NUM-HANDLED-NODES-AUX-OF-ASET1-IRREL
 (35 26 (:REWRITE DEFAULT-<-2))
 (32 26 (:REWRITE DEFAULT-<-1))
 (32 20 (:REWRITE DEFAULT-+-2))
 (20 20 (:REWRITE DEFAULT-+-1))
 (8 8 (:LINEAR ARRAY2P-LINEAR))
 (6 6 (:REWRITE RATIONALP-IMPLIES-ACL2-NUMBERP))
 (6 6 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 )
(NUM-HANDLED-NODES-AUX-OF-ASET1
 (100 66 (:REWRITE DEFAULT-+-2))
 (66 66 (:REWRITE DEFAULT-+-1))
 (30 24 (:REWRITE DEFAULT-<-2))
 (29 19 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (24 24 (:REWRITE DEFAULT-<-1))
 (16 16 (:LINEAR ARRAY2P-LINEAR))
 )
(NUM-HANDLED-NODES)
(NUM-HANDLED-NODES-OF-ASET1
 (56 2 (:DEFINITION NUM-HANDLED-NODES-AUX))
 (32 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (16 4 (:REWRITE FOLD-CONSTS-IN-+))
 (8 8 (:TYPE-PRESCRIPTION NUM-HANDLED-NODES-AUX))
 (7 3 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (6 2 (:REWRITE UNICITY-OF-0))
 (4 2 (:DEFINITION FIX))
 (3 2 (:REWRITE DEFAULT-<-2))
 (2 2 (:REWRITE DEFAULT-<-1))
 (2 2 (:LINEAR ARRAY2P-LINEAR))
 )
(NUM-HANDLED-NODES-AUX-BOUND
 (22 16 (:REWRITE DEFAULT-+-2))
 (16 16 (:REWRITE DEFAULT-+-1))
 (15 10 (:REWRITE DEFAULT-<-2))
 (10 10 (:REWRITE DEFAULT-<-1))
 (6 3 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (3 3 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 )
(NUM-HANDLED-NODES-BOUND
 (48 2 (:DEFINITION NUM-HANDLED-NODES-AUX))
 (38 38 (:TYPE-PRESCRIPTION POSP-OF-ALEN1))
 (19 15 (:REWRITE DEFAULT-+-2))
 (15 15 (:REWRITE DEFAULT-+-1))
 (5 4 (:REWRITE DEFAULT-<-2))
 (4 4 (:REWRITE DEFAULT-<-1))
 (3 1 (:REWRITE INTEGERP-OF-ALEN1))
 (2 2 (:REWRITE AREF1-WHEN-TOO-LARGE-CHEAP))
 (1 1 (:REWRITE INTEGERP-OF-ALEN1-GEN))
 )
