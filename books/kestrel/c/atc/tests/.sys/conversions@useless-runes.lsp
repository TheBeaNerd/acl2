(|f|
 (10 4 (:REWRITE DEFAULT-<-2))
 (10 4 (:REWRITE DEFAULT-<-1))
 (8 8 (:REWRITE C::UCHARP-WHEN-MEMBER-EQUAL-OF-UCHAR-LISTP))
 )
(|g|)
(C::*PROGRAM*-WELL-FORMED)
(C::*PROGRAM*-FUN-ENV)
(|f-FUN-ENV|)
(|f-RESULT|)
(C::|*PROGRAM*-f-CORRECT|
 (20 17 (:REWRITE C::VALUEP-WHEN-ULONGP))
 (20 17 (:REWRITE C::VALUEP-WHEN-ULLONGP))
 (20 17 (:REWRITE C::VALUEP-WHEN-SLONGP))
 (20 17 (:REWRITE C::VALUEP-WHEN-SLLONGP))
 (17 17 (:REWRITE C::VALUEP-WHEN-POINTERP))
 (13 13 (:REWRITE C::VALUEP-WHEN-USHORTP))
 (13 13 (:REWRITE C::VALUEP-WHEN-UINTP))
 (13 13 (:REWRITE C::VALUEP-WHEN-SSHORTP))
 (13 13 (:REWRITE C::VALUEP-WHEN-SCHARP))
 (12 9 (:REWRITE C::NOT-UCHARP-WHEN-ULONGP))
 (12 9 (:REWRITE C::NOT-UCHARP-WHEN-ULLONGP))
 (12 9 (:REWRITE C::NOT-UCHARP-WHEN-SLONGP))
 (12 9 (:REWRITE C::NOT-UCHARP-WHEN-SLLONGP))
 (9 9 (:REWRITE C::NOT-UCHARP-WHEN-POINTERP))
 (8 8 (:REWRITE C::NOT-UCHARP-WHEN-USHORTP))
 (8 8 (:REWRITE C::NOT-UCHARP-WHEN-UINTP))
 (8 8 (:REWRITE C::NOT-UCHARP-WHEN-SSHORTP))
 (8 8 (:REWRITE C::NOT-UCHARP-WHEN-SCHARP))
 (5 5 (:REWRITE C::EXEC-EXPR-PURE-WHEN-COND))
 (5 5 (:REWRITE C::EXEC-EXPR-PURE-WHEN-BINARY-LOGOR))
 (5 5 (:REWRITE C::EXEC-EXPR-PURE-WHEN-BINARY-LOGAND))
 (4 1 (:REWRITE C::NOT-USHORTP-WHEN-ULONGP))
 (4 1 (:REWRITE C::NOT-USHORTP-WHEN-ULLONGP))
 (4 1 (:REWRITE C::NOT-USHORTP-WHEN-SLONGP))
 (4 1 (:REWRITE C::NOT-USHORTP-WHEN-SLLONGP))
 (4 1 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
 (4 1 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
 (4 1 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
 (4 1 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
 (4 1 (:REWRITE C::NOT-SSHORTP-WHEN-ULONGP))
 (4 1 (:REWRITE C::NOT-SSHORTP-WHEN-ULLONGP))
 (4 1 (:REWRITE C::NOT-SSHORTP-WHEN-SLONGP))
 (4 1 (:REWRITE C::NOT-SSHORTP-WHEN-SLLONGP))
 (4 1 (:REWRITE C::NOT-SINTP-WHEN-USHORTP))
 (4 1 (:REWRITE C::NOT-SINTP-WHEN-ULONGP))
 (4 1 (:REWRITE C::NOT-SINTP-WHEN-ULLONGP))
 (4 1 (:REWRITE C::NOT-SINTP-WHEN-UINTP))
 (4 1 (:REWRITE C::NOT-SINTP-WHEN-UCHARP))
 (4 1 (:REWRITE C::NOT-SINTP-WHEN-SSHORTP))
 (4 1 (:REWRITE C::NOT-SINTP-WHEN-SLONGP))
 (4 1 (:REWRITE C::NOT-SINTP-WHEN-SLLONGP))
 (4 1 (:REWRITE C::NOT-SINTP-WHEN-SCHARP))
 (4 1 (:REWRITE C::NOT-SCHARP-WHEN-ULONGP))
 (4 1 (:REWRITE C::NOT-SCHARP-WHEN-ULLONGP))
 (4 1 (:REWRITE C::NOT-SCHARP-WHEN-SLONGP))
 (4 1 (:REWRITE C::NOT-SCHARP-WHEN-SLLONGP))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-BITXOR-WHEN-ULONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-BITXOR-WHEN-ULLONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-BITXOR-WHEN-UINT))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-BITXOR-WHEN-SLONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-BITXOR-WHEN-SLLONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-BITXOR-AND-SINT-WHEN-ULONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-BITXOR-AND-SINT-WHEN-ULLONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-BITXOR-AND-SINT-WHEN-UINT))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-BITXOR-AND-SINT-WHEN-SLONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-BITXOR-AND-SINT-WHEN-SLLONG))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-UNARY))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-CONST))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-ARRSUB))
 (2 2 (:REWRITE C::EXEC-CAST-OF-SINT-WHEN-USHORTP))
 (2 2 (:REWRITE C::EXEC-CAST-OF-SINT-WHEN-ULONGP))
 (2 2 (:REWRITE C::EXEC-CAST-OF-SINT-WHEN-ULLONGP))
 (2 2 (:REWRITE C::EXEC-CAST-OF-SINT-WHEN-UINTP))
 (2 2 (:REWRITE C::EXEC-CAST-OF-SINT-WHEN-SSHORTP))
 (2 2 (:REWRITE C::EXEC-CAST-OF-SINT-WHEN-SLONGP))
 (2 2 (:REWRITE C::EXEC-CAST-OF-SINT-WHEN-SLLONGP))
 (2 2 (:REWRITE C::EXEC-CAST-OF-SINT-WHEN-SINTP))
 (1 1 (:REWRITE C::NOT-USHORTP-WHEN-POINTERP))
 (1 1 (:REWRITE C::NOT-UINTP-WHEN-POINTERP))
 (1 1 (:REWRITE C::NOT-SSHORTP-WHEN-POINTERP))
 (1 1 (:REWRITE C::NOT-SINTP-WHEN-POINTERP))
 (1 1 (:REWRITE C::NOT-SCHARP-WHEN-POINTERP))
 (1 1 (:REWRITE C::EXEC-FUN-OF-CONST-IDENTIFIER))
 (1 1 (:REWRITE C::EXEC-EXPR-CALL-OF-PURE-WHEN-CALL))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-BITIOR))
 (1 1 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-RESULTP-AND-NOT-ERRORP))
 )
(|g-FUN-ENV|)
(|g-RESULT|)
(C::|*PROGRAM*-g-CORRECT|
 (12 9 (:REWRITE C::VALUEP-WHEN-ULONGP))
 (12 9 (:REWRITE C::VALUEP-WHEN-ULLONGP))
 (12 9 (:REWRITE C::VALUEP-WHEN-SLONGP))
 (12 9 (:REWRITE C::VALUEP-WHEN-SLLONGP))
 (9 9 (:REWRITE C::VALUEP-WHEN-POINTERP))
 (7 4 (:REWRITE C::VALUEP-WHEN-USHORTP))
 (7 4 (:REWRITE C::VALUEP-WHEN-UINTP))
 (7 4 (:REWRITE C::VALUEP-WHEN-SSHORTP))
 (7 4 (:REWRITE C::VALUEP-WHEN-SCHARP))
 (5 2 (:REWRITE C::NOT-UCHARP-WHEN-ULONGP))
 (5 2 (:REWRITE C::NOT-UCHARP-WHEN-ULLONGP))
 (5 2 (:REWRITE C::NOT-UCHARP-WHEN-SLONGP))
 (5 2 (:REWRITE C::NOT-UCHARP-WHEN-SLLONGP))
 (4 1 (:REWRITE C::NOT-UCHARP-WHEN-USHORTP))
 (4 1 (:REWRITE C::NOT-UCHARP-WHEN-UINTP))
 (4 1 (:REWRITE C::NOT-UCHARP-WHEN-SSHORTP))
 (4 1 (:REWRITE C::NOT-UCHARP-WHEN-SCHARP))
 (4 1 (:REWRITE C::EXEC-CAST-OF-UCHAR-WHEN-ULONGP))
 (4 1 (:REWRITE C::EXEC-CAST-OF-UCHAR-WHEN-ULLONGP))
 (4 1 (:REWRITE C::EXEC-CAST-OF-UCHAR-WHEN-UINTP))
 (4 1 (:REWRITE C::EXEC-CAST-OF-UCHAR-WHEN-SLONGP))
 (4 1 (:REWRITE C::EXEC-CAST-OF-UCHAR-WHEN-SLLONGP))
 (3 3 (:REWRITE C::EXEC-EXPR-PURE-WHEN-STRICT-PURE-BINARY))
 (3 3 (:REWRITE C::EXEC-EXPR-PURE-WHEN-COND))
 (3 3 (:REWRITE C::EXEC-EXPR-PURE-WHEN-BINARY-LOGOR))
 (3 3 (:REWRITE C::EXEC-EXPR-PURE-WHEN-BINARY-LOGAND))
 (2 2 (:REWRITE C::NOT-UCHARP-WHEN-POINTERP))
 (2 2 (:REWRITE C::NOT-SINTP-WHEN-USHORTP))
 (2 2 (:REWRITE C::NOT-SINTP-WHEN-ULONGP))
 (2 2 (:REWRITE C::NOT-SINTP-WHEN-ULLONGP))
 (2 2 (:REWRITE C::NOT-SINTP-WHEN-UINTP))
 (2 2 (:REWRITE C::NOT-SINTP-WHEN-UCHARP))
 (2 2 (:REWRITE C::NOT-SINTP-WHEN-SSHORTP))
 (2 2 (:REWRITE C::NOT-SINTP-WHEN-SLONGP))
 (2 2 (:REWRITE C::NOT-SINTP-WHEN-SLLONGP))
 (2 2 (:REWRITE C::NOT-SINTP-WHEN-SCHARP))
 (2 2 (:REWRITE C::NOT-SINTP-WHEN-POINTERP))
 (1 1 (:REWRITE C::NOT-USHORTP-WHEN-ULONGP))
 (1 1 (:REWRITE C::NOT-USHORTP-WHEN-ULLONGP))
 (1 1 (:REWRITE C::NOT-USHORTP-WHEN-SLONGP))
 (1 1 (:REWRITE C::NOT-USHORTP-WHEN-SLLONGP))
 (1 1 (:REWRITE C::NOT-USHORTP-WHEN-POINTERP))
 (1 1 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
 (1 1 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
 (1 1 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
 (1 1 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
 (1 1 (:REWRITE C::NOT-UINTP-WHEN-POINTERP))
 (1 1 (:REWRITE C::NOT-SSHORTP-WHEN-ULONGP))
 (1 1 (:REWRITE C::NOT-SSHORTP-WHEN-ULLONGP))
 (1 1 (:REWRITE C::NOT-SSHORTP-WHEN-SLONGP))
 (1 1 (:REWRITE C::NOT-SSHORTP-WHEN-SLLONGP))
 (1 1 (:REWRITE C::NOT-SSHORTP-WHEN-POINTERP))
 (1 1 (:REWRITE C::NOT-SCHARP-WHEN-ULONGP))
 (1 1 (:REWRITE C::NOT-SCHARP-WHEN-ULLONGP))
 (1 1 (:REWRITE C::NOT-SCHARP-WHEN-SLONGP))
 (1 1 (:REWRITE C::NOT-SCHARP-WHEN-SLLONGP))
 (1 1 (:REWRITE C::NOT-SCHARP-WHEN-POINTERP))
 (1 1 (:REWRITE C::EXEC-LOGNOT-WHEN-USHORTP))
 (1 1 (:REWRITE C::EXEC-LOGNOT-WHEN-ULONGP))
 (1 1 (:REWRITE C::EXEC-LOGNOT-WHEN-ULLONGP))
 (1 1 (:REWRITE C::EXEC-LOGNOT-WHEN-UINTP))
 (1 1 (:REWRITE C::EXEC-LOGNOT-WHEN-UCHARP))
 (1 1 (:REWRITE C::EXEC-LOGNOT-WHEN-SSHORTP))
 (1 1 (:REWRITE C::EXEC-LOGNOT-WHEN-SLONGP))
 (1 1 (:REWRITE C::EXEC-LOGNOT-WHEN-SLLONGP))
 (1 1 (:REWRITE C::EXEC-LOGNOT-WHEN-SINTP))
 (1 1 (:REWRITE C::EXEC-LOGNOT-WHEN-SCHARP))
 (1 1 (:REWRITE C::EXEC-FUN-OF-CONST-IDENTIFIER))
 (1 1 (:REWRITE C::EXEC-EXPR-PURE-WHEN-CONST))
 (1 1 (:REWRITE C::EXEC-EXPR-PURE-WHEN-ARRSUB))
 (1 1 (:REWRITE C::EXEC-EXPR-CALL-OF-PURE-WHEN-CALL))
 (1 1 (:REWRITE C::EXEC-BITNOT-WHEN-ULONGP))
 (1 1 (:REWRITE C::EXEC-BITNOT-WHEN-ULLONGP))
 (1 1 (:REWRITE C::EXEC-BITNOT-WHEN-UINTP))
 (1 1 (:REWRITE C::EXEC-BITNOT-WHEN-SLONGP))
 (1 1 (:REWRITE C::EXEC-BITNOT-WHEN-SLLONGP))
 (1 1 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-RESULTP-AND-NOT-ERRORP))
 )
