(C::IRR-TYPE)
(C::TYPEP-OF-IRR-TYPE)
(C::TYPE-TO-MAKER
 (5 5 (:REWRITE C::TYPE-OPTIONP-WHEN-IN-TYPE-OPTION-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 )
(C::TYPE-TO-MAKER-OF-TYPE-FIX-TYPE
 (32 5 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (12 5 (:REWRITE C::TYPE-OPTIONP-WHEN-TYPEP))
 (10 10 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (5 5 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (5 5 (:REWRITE C::TYPE-OPTIONP-WHEN-IN-TYPE-OPTION-SETP-BINDS-FREE-X))
 )
(C::TYPE-TO-MAKER-TYPE-EQUIV-CONGRUENCE-ON-TYPE)
(C::POSITIVE-TO-ICONST)
(C::ICONSTP-OF-POSITIVE-TO-ICONST)
(C::TYPE-TO-TYNAME-AUX)
(C::TYSPECSEQP-OF-TYPE-TO-TYNAME-AUX.TYSPEC)
(C::OBJ-ADECLORP-OF-TYPE-TO-TYNAME-AUX.DECLOR)
(C::TYPE-TO-TYNAME-AUX
 (30 1 (:DEFINITION C::TYPE-TO-TYNAME-AUX))
 (16 2 (:REWRITE C::ICONST-OPTIONP-WHEN-ICONSTP))
 (7 7 (:REWRITE C::TYPE-OPTIONP-WHEN-IN-TYPE-OPTION-SETP-BINDS-FREE-X))
 (7 1 (:REWRITE C::ICONSTP-WHEN-ICONST-OPTIONP))
 (3 3 (:TYPE-PRESCRIPTION C::ICONSTP))
 (3 3 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 )
(C::TYPE-TO-TYNAME-AUX-OF-TYPE-FIX-TYPE
 (32 5 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (12 5 (:REWRITE C::TYPE-OPTIONP-WHEN-TYPEP))
 (10 10 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (5 5 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (5 5 (:REWRITE C::TYPE-OPTIONP-WHEN-IN-TYPE-OPTION-SETP-BINDS-FREE-X))
 )
(C::TYPE-TO-TYNAME-AUX-TYPE-EQUIV-CONGRUENCE-ON-TYPE)
(C::TYPE-TO-TYNAME)
(C::TYNAMEP-OF-TYPE-TO-TYNAME)
(C::TYPE-TO-TYNAME-OF-TYPE-FIX-TYPE)
(C::TYPE-TO-TYNAME-TYPE-EQUIV-CONGRUENCE-ON-TYPE)
(C::IDENT+TYPE-TO-TYSPEC+DECLOR)
(C::TYSPECSEQP-OF-IDENT+TYPE-TO-TYSPEC+DECLOR.TYSPEC)
(C::OBJ-DECLORP-OF-IDENT+TYPE-TO-TYSPEC+DECLOR.DECLOR)
(C::IDENT+TYPE-TO-TYSPEC+DECLOR-OF-IDENT-FIX-ID)
(C::IDENT+TYPE-TO-TYSPEC+DECLOR-IDENT-EQUIV-CONGRUENCE-ON-ID)
(C::IDENT+TYPE-TO-TYSPEC+DECLOR-OF-TYPE-FIX-TYPE)
(C::IDENT+TYPE-TO-TYSPEC+DECLOR-TYPE-EQUIV-CONGRUENCE-ON-TYPE)
