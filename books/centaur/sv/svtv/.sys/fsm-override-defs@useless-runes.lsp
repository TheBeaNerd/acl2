(SV::FSM-OVERRIDEKEY-TRANSPARENT-P)
(SV::SET-EQUIV-IMPLIES-EQUAL-FSM-OVERRIDEKEY-TRANSPARENT-P-2
 (10 4 (:REWRITE SV::SVEX-ALIST-OVERRIDEKEY-TRANSPARENT-P-BY-ALIST-VALS))
 (6 6 (:TYPE-PRESCRIPTION SV::SVEXLIST-OVERRIDEKEY-TRANSPARENT-P))
 )
(SV::FSM-OVERRIDEKEY-TRANSPARENT-P-OF-SVARLIST-CHANGE-OVERRIDE
 (18 6 (:REWRITE SV::SVEX-ALIST-OVERRIDEKEY-TRANSPARENT-P-BY-ALIST-VALS))
 (10 10 (:TYPE-PRESCRIPTION SV::SVEXLIST-OVERRIDEKEY-TRANSPARENT-P))
 (4 2 (:REWRITE SV::SVEXLIST-OVERRIDEKEY-TRANSPARENT-P-OF-SVARLIST-CHANGE-OVERRIDE))
 (3 1 (:REWRITE SV::SVARLIST-CHANGE-OVERRIDE-WHEN-OVERRIDE-P))
 (2 2 (:TYPE-PRESCRIPTION SV::SVARLIST-OVERRIDE-P))
 )
(SV::FSM-OVMONOTONIC)
(SV::FSM-OVCONGRUENT)
(SV::FSM-<<=)
(SV::OVERRIDEKEYS-ENVLISTS-OK
 (30 30 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE SV::SVEX-ENVLIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 )
(SV::OVERRIDEKEYS-ENVLISTS-AGREE*
 (27 27 (:REWRITE DEFAULT-CAR))
 (24 12 (:REWRITE DEFAULT-+-2))
 (18 18 (:REWRITE DEFAULT-CDR))
 (12 12 (:REWRITE DEFAULT-+-1))
 (9 9 (:REWRITE SV::SVEX-ENVLIST-P-WHEN-NOT-CONSP))
 (2 2 (:REWRITE SUBSETP-TRANS2))
 (2 2 (:REWRITE SUBSETP-TRANS))
 (2 1 (:REWRITE DEFAULT-<-2))
 (2 1 (:REWRITE DEFAULT-<-1))
 (1 1 (:REWRITE SV::SVARLIST-P-WHEN-NOT-CONSP))
 )
