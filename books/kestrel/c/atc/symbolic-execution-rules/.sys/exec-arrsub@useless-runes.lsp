(C::ATC-EXEC-ARRSUB-RULES-GEN
 (18 18 (:REWRITE ATOM-LISTP-WHEN-SUBSETP-EQUAL))
 (9 9 (:REWRITE ATOM-LISTP-WHEN-NOT-CONSP))
 (3 3 (:REWRITE C::TYPE-OPTIONP-WHEN-IN-TYPE-OPTION-SETP-BINDS-FREE-X))
 (2 2 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 )
(C::SYMBOLP-OF-ATC-EXEC-ARRSUB-RULES-GEN.NAME)
(C::PSEUDO-EVENT-FORMP-OF-ATC-EXEC-ARRSUB-RULES-GEN.EVENT)
(C::ATC-EXEC-ARRSUB-RULES-GEN-LOOP
 (13 2 (:REWRITE C::TYPEP-WHEN-TYPE-OPTIONP))
 (10 10 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (7 3 (:REWRITE C::TYPE-NONCHAR-INTEGER-LISTP-WHEN-NOT-CONSP))
 (7 3 (:REWRITE C::TYPE-LISTP-WHEN-NOT-CONSP))
 (6 1 (:REWRITE C::TYPE-OPTIONP-WHEN-TYPEP))
 (4 1 (:REWRITE C::TYPE-OPTIONP-OF-CAR-WHEN-TYPE-OPTION-LISTP))
 (2 2 (:TYPE-PRESCRIPTION C::TYPE-OPTIONP))
 (2 2 (:REWRITE C::TYPEP-WHEN-IN-TYPE-SETP-BINDS-FREE-X))
 (1 1 (:TYPE-PRESCRIPTION C::TYPEP))
 (1 1 (:REWRITE C::TYPE-OPTIONP-WHEN-IN-TYPE-OPTION-SETP-BINDS-FREE-X))
 (1 1 (:REWRITE C::TYPE-OPTION-LISTP-WHEN-NOT-CONSP))
 )
(C::SYMBOL-LISTP-OF-ATC-EXEC-ARRSUB-RULES-GEN-LOOP.NAMES
 (38 22 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (22 8 (:REWRITE SYMBOL-LISTP-WHEN-NOT-CONSP))
 (14 2 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (14 2 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (9 9 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (9 1 (:REWRITE SUBSETP-OF-CONS))
 (5 5 (:REWRITE SUBSETP-TRANS2))
 (5 5 (:REWRITE SUBSETP-TRANS))
 (5 5 (:REWRITE SUBSETP-MEMBER . 2))
 (5 5 (:REWRITE SUBSETP-MEMBER . 1))
 (2 2 (:REWRITE MEMBER-SELF))
 )
(C::PSEUDO-EVENT-FORM-LISTP-OF-ATC-EXEC-ARRSUB-RULES-GEN-LOOP.EVENTS
 (259 7 (:DEFINITION PSEUDO-EVENT-FORM-LISTP))
 (62 62 (:REWRITE CONSP-WHEN-MEMBER-EQUAL-OF-ATOM-LISTP))
 (61 7 (:REWRITE PSEUDO-EVENT-FORMP-OF-CAR-WHEN-PSEUDO-EVENT-FORM-LISTP))
 (61 7 (:REWRITE PSEUDO-EVENT-FORM-LISTP-OF-CDR-WHEN-PSEUDO-EVENT-FORM-LISTP))
 (57 29 (:REWRITE PSEUDO-EVENT-FORM-LISTP-WHEN-NOT-CONSP))
 (40 14 (:REWRITE PSEUDO-EVENT-FORMP-WHEN-MEMBER-EQUAL-OF-PSEUDO-EVENT-FORM-LISTP))
 (24 12 (:REWRITE SUBSETP-WHEN-ATOM-RIGHT))
 (20 12 (:REWRITE SUBSETP-WHEN-ATOM-LEFT))
 (18 2 (:REWRITE SUBSETP-IMPLIES-SUBSETP-CDR))
 (18 2 (:REWRITE SUBSETP-CAR-MEMBER))
 (15 15 (:REWRITE SUBSETP-TRANS2))
 (15 15 (:REWRITE SUBSETP-TRANS))
 (9 1 (:REWRITE SUBSETP-OF-CONS))
 (7 7 (:TYPE-PRESCRIPTION PSEUDO-EVENT-FORMP))
 (7 7 (:TYPE-PRESCRIPTION MEMBER-EQUAL))
 (3 3 (:REWRITE SUBSETP-MEMBER . 2))
 (3 3 (:REWRITE SUBSETP-MEMBER . 1))
 )
(C::ATC-EXEC-ARRSUB-RULES-GEN-ALL)
(C::PSEUDO-EVENT-FORMP-OF-ATC-EXEC-ARRSUB-RULES-GEN-ALL)
(C::EXEC-ARRSUB-WHEN-SCHAR-ARRAYP
 (237 47 (:REWRITE C::CINTEGERP-WHEN-USHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UCHARP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SSHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::USHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::ULONGP))
 (92 92 (:TYPE-PRESCRIPTION C::ULLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::UINTP))
 (92 92 (:TYPE-PRESCRIPTION C::UCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::SSHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::SLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SLLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SINTP))
 (92 92 (:TYPE-PRESCRIPTION C::SCHARP))
 (92 92 (:REWRITE C::USHORTP-WHEN-MEMBER-EQUAL-OF-USHORT-LISTP))
 (92 92 (:REWRITE C::ULONGP-WHEN-MEMBER-EQUAL-OF-ULONG-LISTP))
 (92 92 (:REWRITE C::ULLONGP-WHEN-MEMBER-EQUAL-OF-ULLONG-LISTP))
 (92 92 (:REWRITE C::UINTP-WHEN-MEMBER-EQUAL-OF-UINT-LISTP))
 (92 92 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 (92 92 (:REWRITE C::SSHORTP-WHEN-MEMBER-EQUAL-OF-SSHORT-LISTP))
 (92 92 (:REWRITE C::SLONGP-WHEN-MEMBER-EQUAL-OF-SLONG-LISTP))
 (92 92 (:REWRITE C::SLLONGP-WHEN-MEMBER-EQUAL-OF-SLLONG-LISTP))
 (92 92 (:REWRITE C::SINTP-WHEN-MEMBER-EQUAL-OF-SINT-LISTP))
 (92 92 (:REWRITE C::SCHARP-WHEN-MEMBER-EQUAL-OF-SCHAR-LISTP))
 (32 4 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (24 2 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 4 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (11 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (8 4 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (5 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (1 1 (:REWRITE C::OBJDESIGN-OPTIONP-OF-EXPR-VALUE->OBJECT))
 )
(C::EXEC-ARRSUB-WHEN-UCHAR-ARRAYP
 (237 47 (:REWRITE C::CINTEGERP-WHEN-USHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UCHARP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SSHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::USHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::ULONGP))
 (92 92 (:TYPE-PRESCRIPTION C::ULLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::UINTP))
 (92 92 (:TYPE-PRESCRIPTION C::UCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::SSHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::SLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SLLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SINTP))
 (92 92 (:TYPE-PRESCRIPTION C::SCHARP))
 (92 92 (:REWRITE C::USHORTP-WHEN-MEMBER-EQUAL-OF-USHORT-LISTP))
 (92 92 (:REWRITE C::ULONGP-WHEN-MEMBER-EQUAL-OF-ULONG-LISTP))
 (92 92 (:REWRITE C::ULLONGP-WHEN-MEMBER-EQUAL-OF-ULLONG-LISTP))
 (92 92 (:REWRITE C::UINTP-WHEN-MEMBER-EQUAL-OF-UINT-LISTP))
 (92 92 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 (92 92 (:REWRITE C::SSHORTP-WHEN-MEMBER-EQUAL-OF-SSHORT-LISTP))
 (92 92 (:REWRITE C::SLONGP-WHEN-MEMBER-EQUAL-OF-SLONG-LISTP))
 (92 92 (:REWRITE C::SLLONGP-WHEN-MEMBER-EQUAL-OF-SLLONG-LISTP))
 (92 92 (:REWRITE C::SINTP-WHEN-MEMBER-EQUAL-OF-SINT-LISTP))
 (92 92 (:REWRITE C::SCHARP-WHEN-MEMBER-EQUAL-OF-SCHAR-LISTP))
 (32 4 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (24 2 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 4 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (11 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (8 4 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (5 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (1 1 (:REWRITE C::OBJDESIGN-OPTIONP-OF-EXPR-VALUE->OBJECT))
 )
(C::EXEC-ARRSUB-WHEN-SSHORT-ARRAYP
 (237 47 (:REWRITE C::CINTEGERP-WHEN-USHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UCHARP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SSHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::USHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::ULONGP))
 (92 92 (:TYPE-PRESCRIPTION C::ULLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::UINTP))
 (92 92 (:TYPE-PRESCRIPTION C::UCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::SSHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::SLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SLLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SINTP))
 (92 92 (:TYPE-PRESCRIPTION C::SCHARP))
 (92 92 (:REWRITE C::USHORTP-WHEN-MEMBER-EQUAL-OF-USHORT-LISTP))
 (92 92 (:REWRITE C::ULONGP-WHEN-MEMBER-EQUAL-OF-ULONG-LISTP))
 (92 92 (:REWRITE C::ULLONGP-WHEN-MEMBER-EQUAL-OF-ULLONG-LISTP))
 (92 92 (:REWRITE C::UINTP-WHEN-MEMBER-EQUAL-OF-UINT-LISTP))
 (92 92 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 (92 92 (:REWRITE C::SSHORTP-WHEN-MEMBER-EQUAL-OF-SSHORT-LISTP))
 (92 92 (:REWRITE C::SLONGP-WHEN-MEMBER-EQUAL-OF-SLONG-LISTP))
 (92 92 (:REWRITE C::SLLONGP-WHEN-MEMBER-EQUAL-OF-SLLONG-LISTP))
 (92 92 (:REWRITE C::SINTP-WHEN-MEMBER-EQUAL-OF-SINT-LISTP))
 (92 92 (:REWRITE C::SCHARP-WHEN-MEMBER-EQUAL-OF-SCHAR-LISTP))
 (32 4 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (24 2 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 4 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (11 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (8 4 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (5 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (1 1 (:REWRITE C::OBJDESIGN-OPTIONP-OF-EXPR-VALUE->OBJECT))
 )
(C::EXEC-ARRSUB-WHEN-USHORT-ARRAYP
 (237 47 (:REWRITE C::CINTEGERP-WHEN-USHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UCHARP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SSHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::USHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::ULONGP))
 (92 92 (:TYPE-PRESCRIPTION C::ULLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::UINTP))
 (92 92 (:TYPE-PRESCRIPTION C::UCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::SSHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::SLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SLLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SINTP))
 (92 92 (:TYPE-PRESCRIPTION C::SCHARP))
 (92 92 (:REWRITE C::USHORTP-WHEN-MEMBER-EQUAL-OF-USHORT-LISTP))
 (92 92 (:REWRITE C::ULONGP-WHEN-MEMBER-EQUAL-OF-ULONG-LISTP))
 (92 92 (:REWRITE C::ULLONGP-WHEN-MEMBER-EQUAL-OF-ULLONG-LISTP))
 (92 92 (:REWRITE C::UINTP-WHEN-MEMBER-EQUAL-OF-UINT-LISTP))
 (92 92 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 (92 92 (:REWRITE C::SSHORTP-WHEN-MEMBER-EQUAL-OF-SSHORT-LISTP))
 (92 92 (:REWRITE C::SLONGP-WHEN-MEMBER-EQUAL-OF-SLONG-LISTP))
 (92 92 (:REWRITE C::SLLONGP-WHEN-MEMBER-EQUAL-OF-SLLONG-LISTP))
 (92 92 (:REWRITE C::SINTP-WHEN-MEMBER-EQUAL-OF-SINT-LISTP))
 (92 92 (:REWRITE C::SCHARP-WHEN-MEMBER-EQUAL-OF-SCHAR-LISTP))
 (32 4 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (24 2 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 4 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (11 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (8 4 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (5 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (1 1 (:REWRITE C::OBJDESIGN-OPTIONP-OF-EXPR-VALUE->OBJECT))
 )
(C::EXEC-ARRSUB-WHEN-SINT-ARRAYP
 (237 47 (:REWRITE C::CINTEGERP-WHEN-USHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UCHARP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SSHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::USHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::ULONGP))
 (92 92 (:TYPE-PRESCRIPTION C::ULLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::UINTP))
 (92 92 (:TYPE-PRESCRIPTION C::UCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::SSHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::SLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SLLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SINTP))
 (92 92 (:TYPE-PRESCRIPTION C::SCHARP))
 (92 92 (:REWRITE C::USHORTP-WHEN-MEMBER-EQUAL-OF-USHORT-LISTP))
 (92 92 (:REWRITE C::ULONGP-WHEN-MEMBER-EQUAL-OF-ULONG-LISTP))
 (92 92 (:REWRITE C::ULLONGP-WHEN-MEMBER-EQUAL-OF-ULLONG-LISTP))
 (92 92 (:REWRITE C::UINTP-WHEN-MEMBER-EQUAL-OF-UINT-LISTP))
 (92 92 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 (92 92 (:REWRITE C::SSHORTP-WHEN-MEMBER-EQUAL-OF-SSHORT-LISTP))
 (92 92 (:REWRITE C::SLONGP-WHEN-MEMBER-EQUAL-OF-SLONG-LISTP))
 (92 92 (:REWRITE C::SLLONGP-WHEN-MEMBER-EQUAL-OF-SLLONG-LISTP))
 (92 92 (:REWRITE C::SINTP-WHEN-MEMBER-EQUAL-OF-SINT-LISTP))
 (92 92 (:REWRITE C::SCHARP-WHEN-MEMBER-EQUAL-OF-SCHAR-LISTP))
 (32 4 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (24 2 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 4 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (11 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (8 4 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (5 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (1 1 (:REWRITE C::OBJDESIGN-OPTIONP-OF-EXPR-VALUE->OBJECT))
 )
(C::EXEC-ARRSUB-WHEN-UINT-ARRAYP
 (237 47 (:REWRITE C::CINTEGERP-WHEN-USHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UCHARP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SSHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::USHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::ULONGP))
 (92 92 (:TYPE-PRESCRIPTION C::ULLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::UINTP))
 (92 92 (:TYPE-PRESCRIPTION C::UCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::SSHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::SLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SLLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SINTP))
 (92 92 (:TYPE-PRESCRIPTION C::SCHARP))
 (92 92 (:REWRITE C::USHORTP-WHEN-MEMBER-EQUAL-OF-USHORT-LISTP))
 (92 92 (:REWRITE C::ULONGP-WHEN-MEMBER-EQUAL-OF-ULONG-LISTP))
 (92 92 (:REWRITE C::ULLONGP-WHEN-MEMBER-EQUAL-OF-ULLONG-LISTP))
 (92 92 (:REWRITE C::UINTP-WHEN-MEMBER-EQUAL-OF-UINT-LISTP))
 (92 92 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 (92 92 (:REWRITE C::SSHORTP-WHEN-MEMBER-EQUAL-OF-SSHORT-LISTP))
 (92 92 (:REWRITE C::SLONGP-WHEN-MEMBER-EQUAL-OF-SLONG-LISTP))
 (92 92 (:REWRITE C::SLLONGP-WHEN-MEMBER-EQUAL-OF-SLLONG-LISTP))
 (92 92 (:REWRITE C::SINTP-WHEN-MEMBER-EQUAL-OF-SINT-LISTP))
 (92 92 (:REWRITE C::SCHARP-WHEN-MEMBER-EQUAL-OF-SCHAR-LISTP))
 (32 4 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (24 2 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 4 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (11 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (8 4 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (5 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (1 1 (:REWRITE C::OBJDESIGN-OPTIONP-OF-EXPR-VALUE->OBJECT))
 )
(C::EXEC-ARRSUB-WHEN-SLONG-ARRAYP
 (237 47 (:REWRITE C::CINTEGERP-WHEN-USHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UCHARP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SSHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::USHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::ULONGP))
 (92 92 (:TYPE-PRESCRIPTION C::ULLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::UINTP))
 (92 92 (:TYPE-PRESCRIPTION C::UCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::SSHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::SLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SLLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SINTP))
 (92 92 (:TYPE-PRESCRIPTION C::SCHARP))
 (92 92 (:REWRITE C::USHORTP-WHEN-MEMBER-EQUAL-OF-USHORT-LISTP))
 (92 92 (:REWRITE C::ULONGP-WHEN-MEMBER-EQUAL-OF-ULONG-LISTP))
 (92 92 (:REWRITE C::ULLONGP-WHEN-MEMBER-EQUAL-OF-ULLONG-LISTP))
 (92 92 (:REWRITE C::UINTP-WHEN-MEMBER-EQUAL-OF-UINT-LISTP))
 (92 92 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 (92 92 (:REWRITE C::SSHORTP-WHEN-MEMBER-EQUAL-OF-SSHORT-LISTP))
 (92 92 (:REWRITE C::SLONGP-WHEN-MEMBER-EQUAL-OF-SLONG-LISTP))
 (92 92 (:REWRITE C::SLLONGP-WHEN-MEMBER-EQUAL-OF-SLLONG-LISTP))
 (92 92 (:REWRITE C::SINTP-WHEN-MEMBER-EQUAL-OF-SINT-LISTP))
 (92 92 (:REWRITE C::SCHARP-WHEN-MEMBER-EQUAL-OF-SCHAR-LISTP))
 (32 4 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (24 2 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 4 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (11 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (8 4 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (5 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (1 1 (:REWRITE C::OBJDESIGN-OPTIONP-OF-EXPR-VALUE->OBJECT))
 )
(C::EXEC-ARRSUB-WHEN-ULONG-ARRAYP
 (237 47 (:REWRITE C::CINTEGERP-WHEN-USHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UCHARP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SSHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::USHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::ULONGP))
 (92 92 (:TYPE-PRESCRIPTION C::ULLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::UINTP))
 (92 92 (:TYPE-PRESCRIPTION C::UCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::SSHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::SLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SLLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SINTP))
 (92 92 (:TYPE-PRESCRIPTION C::SCHARP))
 (92 92 (:REWRITE C::USHORTP-WHEN-MEMBER-EQUAL-OF-USHORT-LISTP))
 (92 92 (:REWRITE C::ULONGP-WHEN-MEMBER-EQUAL-OF-ULONG-LISTP))
 (92 92 (:REWRITE C::ULLONGP-WHEN-MEMBER-EQUAL-OF-ULLONG-LISTP))
 (92 92 (:REWRITE C::UINTP-WHEN-MEMBER-EQUAL-OF-UINT-LISTP))
 (92 92 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 (92 92 (:REWRITE C::SSHORTP-WHEN-MEMBER-EQUAL-OF-SSHORT-LISTP))
 (92 92 (:REWRITE C::SLONGP-WHEN-MEMBER-EQUAL-OF-SLONG-LISTP))
 (92 92 (:REWRITE C::SLLONGP-WHEN-MEMBER-EQUAL-OF-SLLONG-LISTP))
 (92 92 (:REWRITE C::SINTP-WHEN-MEMBER-EQUAL-OF-SINT-LISTP))
 (92 92 (:REWRITE C::SCHARP-WHEN-MEMBER-EQUAL-OF-SCHAR-LISTP))
 (32 4 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (24 2 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 4 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (11 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (8 4 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (5 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (1 1 (:REWRITE C::OBJDESIGN-OPTIONP-OF-EXPR-VALUE->OBJECT))
 )
(C::EXEC-ARRSUB-WHEN-SLLONG-ARRAYP
 (237 47 (:REWRITE C::CINTEGERP-WHEN-USHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UCHARP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SSHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::USHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::ULONGP))
 (92 92 (:TYPE-PRESCRIPTION C::ULLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::UINTP))
 (92 92 (:TYPE-PRESCRIPTION C::UCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::SSHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::SLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SLLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SINTP))
 (92 92 (:TYPE-PRESCRIPTION C::SCHARP))
 (92 92 (:REWRITE C::USHORTP-WHEN-MEMBER-EQUAL-OF-USHORT-LISTP))
 (92 92 (:REWRITE C::ULONGP-WHEN-MEMBER-EQUAL-OF-ULONG-LISTP))
 (92 92 (:REWRITE C::ULLONGP-WHEN-MEMBER-EQUAL-OF-ULLONG-LISTP))
 (92 92 (:REWRITE C::UINTP-WHEN-MEMBER-EQUAL-OF-UINT-LISTP))
 (92 92 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 (92 92 (:REWRITE C::SSHORTP-WHEN-MEMBER-EQUAL-OF-SSHORT-LISTP))
 (92 92 (:REWRITE C::SLONGP-WHEN-MEMBER-EQUAL-OF-SLONG-LISTP))
 (92 92 (:REWRITE C::SLLONGP-WHEN-MEMBER-EQUAL-OF-SLLONG-LISTP))
 (92 92 (:REWRITE C::SINTP-WHEN-MEMBER-EQUAL-OF-SINT-LISTP))
 (92 92 (:REWRITE C::SCHARP-WHEN-MEMBER-EQUAL-OF-SCHAR-LISTP))
 (32 4 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (24 2 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 4 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (11 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (8 4 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (5 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (1 1 (:REWRITE C::OBJDESIGN-OPTIONP-OF-EXPR-VALUE->OBJECT))
 )
(C::EXEC-ARRSUB-WHEN-ULLONG-ARRAYP
 (237 47 (:REWRITE C::CINTEGERP-WHEN-USHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-ULLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-UCHARP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SSHORTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SLLONGP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SINTP))
 (237 47 (:REWRITE C::CINTEGERP-WHEN-SCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::USHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::ULONGP))
 (92 92 (:TYPE-PRESCRIPTION C::ULLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::UINTP))
 (92 92 (:TYPE-PRESCRIPTION C::UCHARP))
 (92 92 (:TYPE-PRESCRIPTION C::SSHORTP))
 (92 92 (:TYPE-PRESCRIPTION C::SLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SLLONGP))
 (92 92 (:TYPE-PRESCRIPTION C::SINTP))
 (92 92 (:TYPE-PRESCRIPTION C::SCHARP))
 (92 92 (:REWRITE C::USHORTP-WHEN-MEMBER-EQUAL-OF-USHORT-LISTP))
 (92 92 (:REWRITE C::ULONGP-WHEN-MEMBER-EQUAL-OF-ULONG-LISTP))
 (92 92 (:REWRITE C::ULLONGP-WHEN-MEMBER-EQUAL-OF-ULLONG-LISTP))
 (92 92 (:REWRITE C::UINTP-WHEN-MEMBER-EQUAL-OF-UINT-LISTP))
 (92 92 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 (92 92 (:REWRITE C::SSHORTP-WHEN-MEMBER-EQUAL-OF-SSHORT-LISTP))
 (92 92 (:REWRITE C::SLONGP-WHEN-MEMBER-EQUAL-OF-SLONG-LISTP))
 (92 92 (:REWRITE C::SLLONGP-WHEN-MEMBER-EQUAL-OF-SLLONG-LISTP))
 (92 92 (:REWRITE C::SINTP-WHEN-MEMBER-EQUAL-OF-SINT-LISTP))
 (92 92 (:REWRITE C::SCHARP-WHEN-MEMBER-EQUAL-OF-SCHAR-LISTP))
 (32 4 (:REWRITE C::COMPUSTATE-FIX-WHEN-COMPUSTATEP))
 (24 2 (:REWRITE C::VALUE-FIX-WHEN-VALUEP))
 (20 4 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-OPTIONP))
 (12 12 (:TYPE-PRESCRIPTION C::COMPUSTATEP))
 (11 2 (:REWRITE C::VALUEP-WHEN-VALUE-OPTIONP))
 (8 8 (:TYPE-PRESCRIPTION C::COMPUSTATE-OPTIONP))
 (8 4 (:REWRITE C::COMPUSTATE-OPTIONP-WHEN-COMPUSTATEP))
 (6 6 (:TYPE-PRESCRIPTION C::VALUEP))
 (5 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (4 4 (:TYPE-PRESCRIPTION C::VALUE-OPTIONP))
 (4 4 (:REWRITE C::VALUEP-WHEN-MEMBER-EQUAL-OF-VALUE-LISTP))
 (4 2 (:REWRITE C::OBJDESIGN-OPTION-FIX-WHEN-NONE))
 (1 1 (:REWRITE C::OBJDESIGN-OPTIONP-OF-EXPR-VALUE->OBJECT))
 )
