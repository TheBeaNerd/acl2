(|f$loop|
 (564 2 (:REWRITE MOD-X-Y-=-X . 4))
 (284 2 (:REWRITE |(< d (+ c x))|))
 (122 3 (:REWRITE CANCEL-MOD-+))
 (36 4 (:LINEAR C::UCHAR-MAX-VS-USHORT-MAX))
 (28 4 (:LINEAR C::USHORT-MAX-VS-SINT-MAX))
 (28 4 (:LINEAR C::ULONG-MAX-VS-ULLONG-MAX))
 (28 4 (:LINEAR C::SINT-MAX-VS-SLONG-MAX))
 (26 26 (:TYPE-PRESCRIPTION C::UCHAR-MAX))
 (26 26 (:TYPE-PRESCRIPTION C::SINT-MAX))
 (26 26 (:TYPE-PRESCRIPTION C::INTEGERP-OF-UCHAR-MAX))
 (26 26 (:TYPE-PRESCRIPTION C::INTEGERP-OF-SINT-MAX))
 (25 5 (:REWRITE DEFAULT-UNARY-/))
 (24 4 (:LINEAR C::USHORT-MAX-VS-SLONG-MAX))
 (24 4 (:LINEAR C::USHORT-MAX-VS-SLLONG-MAX))
 (24 4 (:LINEAR C::ULONG-MAX-VS-SLLONG-MAX))
 (24 4 (:LINEAR C::UCHAR-MAX-VS-SLONG-MAX))
 (24 4 (:LINEAR C::UCHAR-MAX-VS-SLLONG-MAX))
 (24 4 (:LINEAR C::SSHORT-MAX-VS-SINT-MAX))
 (24 4 (:LINEAR C::SLONG-MAX-VS-SLLONG-MAX))
 (24 2 (:REWRITE C::UINT-INTEGER-FIX-WHEN-UINT-INTEGERP))
 (23 9 (:REWRITE DEFAULT-+-2))
 (20 4 (:LINEAR C::UCHAR-MAX-VS-SINT-MAX))
 (18 2 (:LINEAR C::USHORT-MAX-BOUND))
 (18 2 (:LINEAR C::UINT-MAX-BOUND))
 (18 2 (:LINEAR C::SCHAR-MAX-VS-SSHORT-MAX))
 (14 14 (:TYPE-PRESCRIPTION C::SSHORT-MAX))
 (14 14 (:TYPE-PRESCRIPTION C::INTEGERP-OF-SSHORT-MAX))
 (14 2 (:LINEAR C::ULONG-MAX-BOUND))
 (12 12 (:TYPE-PRESCRIPTION C::ULLONG-MAX))
 (12 12 (:TYPE-PRESCRIPTION C::INTEGERP-OF-ULLONG-MAX))
 (11 5 (:REWRITE DEFAULT-UNARY-MINUS))
 (10 2 (:LINEAR C::ULLONG-MAX-BOUND))
 (10 2 (:LINEAR C::UCHAR-MAX-BOUND))
 (10 2 (:LINEAR C::SSHORT-MAX-BOUND))
 (10 2 (:LINEAR C::SLONG-MAX-BOUND))
 (10 2 (:LINEAR C::SLLONG-MAX-BOUND))
 (9 9 (:REWRITE NORMALIZE-TERMS-SUCH-AS-A/A+B-+-B/A+B))
 (9 9 (:REWRITE DEFAULT-+-1))
 (9 3 (:REWRITE SIMPLIFY-MOD-+-MOD-WEAK))
 (9 3 (:REWRITE SIMPLIFY-MOD-+-MINUS-MOD))
 (9 3 (:REWRITE MOD-CANCEL-*))
 (8 8 (:REWRITE C::UINT-INTEGERP-WHEN-MEMBER-EQUAL-OF-UINT-INTEGER-LISTP))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES-TWO))
 (7 7 (:REWRITE REMOVE-WEAK-INEQUALITIES-ONE))
 (7 7 (:META META-INTEGERP-CORRECT))
 (7 3 (:REWRITE MOD-MINUS-2))
 (6 5 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-<))
 (6 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-4A))
 (6 2 (:LINEAR C::SINT-MAX-BOUND))
 (6 1 (:REWRITE |(* y x)|))
 (5 5 (:REWRITE NORMALIZE-TERMS-SUCH-AS-1/AX+BX))
 (5 5 (:REWRITE |(< (- x) (- y))|))
 (4 4 (:TYPE-PRESCRIPTION C::UINT-INTEGERP))
 (4 4 (:REWRITE REDUCE-INTEGERP-+))
 (4 3 (:REWRITE DEFAULT-<-1))
 (3 3 (:REWRITE DEFAULT-<-2))
 (3 3 (:REWRITE |(* (- x) y)|))
 (3 1 (:REWRITE DEFAULT-*-1))
 (2 2 (:TYPE-PRESCRIPTION C::SCHAR-MAX))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-3A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-2A))
 (2 2 (:TYPE-PRESCRIPTION NOT-INTEGERP-1A))
 (2 2 (:TYPE-PRESCRIPTION C::INTEGERP-OF-SCHAR-MAX))
 (2 2 (:REWRITE-QUOTED-CONSTANT C::SINT-INTEGER-FIX-UNDER-SINT-INTEGER-EQUIV))
 (2 1 (:REWRITE SIMPLIFY-SUMS-EQUAL))
 (2 1 (:REWRITE SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL))
 (2 1 (:REWRITE PREFER-POSITIVE-ADDENDS-EQUAL))
 (1 1 (:REWRITE-QUOTED-CONSTANT C::UINT-INTEGER-FIX-UNDER-UINT-INTEGER-EQUIV))
 (1 1 (:REWRITE-QUOTED-CONSTANT C::UINT-FIX-UNDER-UINT-EQUIV))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-=-0))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-A+AB-<-0))
 (1 1 (:REWRITE SIMPLIFY-TERMS-SUCH-AS-0-<-A+AB))
 (1 1 (:REWRITE NORMALIZE-FACTORS-GATHER-EXPONENTS))
 (1 1 (:REWRITE DEFAULT-*-2))
 (1 1 (:REWRITE |(integerp (* c x))|))
 (1 1 (:REWRITE |(equal (- x) 0)|))
 (1 1 (:REWRITE |(equal (- x) (- y))|))
 (1 1 (:REWRITE |(< 0 (- x))|))
 (1 1 (:REWRITE |(< (- x) 0)|))
 (1 1 (:REWRITE |(< (+ c x) d)|))
 (1 1 (:REWRITE |(* 1 x)|))
 )
(|f|)
(|NATP-OF-MEASURE-OF-f$loop|)
(C::*PROGRAM*-WELL-FORMED)
(C::*PROGRAM*-FUN-ENV)
(|MEASURE-OF-f$loop|)
(|f$loop-RESULTS|)
(|EXEC-STMT-WHILE-FOR-f$loop|)
(|EXEC-STMT-WHILE-FOR-f$loop-TO-EXEC-STMT-WHILE|)
(|NATP-OF-MEASURE-OF-f$loop$|)
(|TERMINATION-OF-f$loop|)
(C::|*PROGRAM*-f$loop-CORRECT-TEST|
 (13 7 (:REWRITE C::NOT-UINTP-WHEN-USHORTP))
 (13 7 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
 (13 7 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
 (13 7 (:REWRITE C::NOT-UINTP-WHEN-UCHARP))
 (13 7 (:REWRITE C::NOT-UINTP-WHEN-SSHORTP))
 (13 7 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
 (13 7 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
 (13 7 (:REWRITE C::NOT-UINTP-WHEN-SINTP))
 (13 7 (:REWRITE C::NOT-UINTP-WHEN-SCHARP))
 (7 7 (:REWRITE C::NOT-UINTP-WHEN-POINTERP))
 (4 1 (:REWRITE C::EXEC-TEST-WHEN-ULONGP))
 (4 1 (:REWRITE C::EXEC-TEST-WHEN-ULLONGP))
 (4 1 (:REWRITE C::EXEC-TEST-WHEN-UINTP))
 (4 1 (:REWRITE C::EXEC-TEST-WHEN-SLONGP))
 (4 1 (:REWRITE C::EXEC-TEST-WHEN-SLLONGP))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-NE-AND-UINT-WHEN-ULONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-NE-AND-UINT-WHEN-ULLONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-NE-AND-UINT-WHEN-SLONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-NE-AND-UINT-WHEN-SLLONG))
 (3 3 (:REWRITE C::EXEC-EXPR-PURE-WHEN-COND))
 (3 3 (:REWRITE C::EXEC-EXPR-PURE-WHEN-BINARY-LOGOR))
 (3 3 (:REWRITE C::EXEC-EXPR-PURE-WHEN-BINARY-LOGAND))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-UNARY))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-CAST))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-ARRSUB))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-BITXOR))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-BITIOR))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-BITAND))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-NE-WHEN-ULONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-NE-WHEN-ULLONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-NE-WHEN-SLONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-NE-WHEN-SLLONG))
 (1 1 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-RESULTP-AND-NOT-ERRORP))
 )
(C::|*PROGRAM*-f$loop-CORRECT-BODY|
 (35 17 (:REWRITE C::NOT-UINTP-WHEN-USHORTP))
 (35 17 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
 (35 17 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
 (35 17 (:REWRITE C::NOT-UINTP-WHEN-UCHARP))
 (35 17 (:REWRITE C::NOT-UINTP-WHEN-SSHORTP))
 (35 17 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
 (35 17 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
 (35 17 (:REWRITE C::NOT-UINTP-WHEN-SINTP))
 (35 17 (:REWRITE C::NOT-UINTP-WHEN-SCHARP))
 (28 16 (:REWRITE C::VALUEP-WHEN-ULONGP))
 (28 16 (:REWRITE C::VALUEP-WHEN-ULLONGP))
 (28 16 (:REWRITE C::VALUEP-WHEN-SLONGP))
 (28 16 (:REWRITE C::VALUEP-WHEN-SLLONGP))
 (28 16 (:REWRITE C::VALUEP-WHEN-SINTP))
 (24 2 (:REWRITE C::VALUE-OPTIONP-WHEN-VALUEP))
 (20 8 (:REWRITE C::NOT-USHORTP-WHEN-ULONGP))
 (20 8 (:REWRITE C::NOT-USHORTP-WHEN-ULLONGP))
 (20 8 (:REWRITE C::NOT-USHORTP-WHEN-SLONGP))
 (20 8 (:REWRITE C::NOT-USHORTP-WHEN-SLLONGP))
 (20 8 (:REWRITE C::NOT-USHORTP-WHEN-SINTP))
 (20 8 (:REWRITE C::NOT-UCHARP-WHEN-ULONGP))
 (20 8 (:REWRITE C::NOT-UCHARP-WHEN-ULLONGP))
 (20 8 (:REWRITE C::NOT-UCHARP-WHEN-SLONGP))
 (20 8 (:REWRITE C::NOT-UCHARP-WHEN-SLLONGP))
 (20 8 (:REWRITE C::NOT-UCHARP-WHEN-SINTP))
 (20 8 (:REWRITE C::NOT-SSHORTP-WHEN-ULONGP))
 (20 8 (:REWRITE C::NOT-SSHORTP-WHEN-ULLONGP))
 (20 8 (:REWRITE C::NOT-SSHORTP-WHEN-SLONGP))
 (20 8 (:REWRITE C::NOT-SSHORTP-WHEN-SLLONGP))
 (20 8 (:REWRITE C::NOT-SSHORTP-WHEN-SINTP))
 (20 8 (:REWRITE C::NOT-SCHARP-WHEN-ULONGP))
 (20 8 (:REWRITE C::NOT-SCHARP-WHEN-ULLONGP))
 (20 8 (:REWRITE C::NOT-SCHARP-WHEN-SLONGP))
 (20 8 (:REWRITE C::NOT-SCHARP-WHEN-SLLONGP))
 (20 8 (:REWRITE C::NOT-SCHARP-WHEN-SINTP))
 (17 17 (:REWRITE C::NOT-UINTP-WHEN-POINTERP))
 (16 16 (:REWRITE C::VALUEP-WHEN-POINTERP))
 (13 3 (:REWRITE C::UPDATE-VAR-OF-UPDATE-VAR-LESS))
 (8 8 (:REWRITE C::NOT-USHORTP-WHEN-POINTERP))
 (8 8 (:REWRITE C::NOT-UCHARP-WHEN-POINTERP))
 (8 8 (:REWRITE C::NOT-SSHORTP-WHEN-POINTERP))
 (8 8 (:REWRITE C::NOT-SCHARP-WHEN-POINTERP))
 (6 6 (:REWRITE C::EXEC-EXPR-PURE-WHEN-COND))
 (6 6 (:REWRITE C::EXEC-EXPR-PURE-WHEN-BINARY-LOGOR))
 (6 6 (:REWRITE C::EXEC-EXPR-PURE-WHEN-BINARY-LOGAND))
 (4 4 (:REWRITE C::EXEC-STMT-WHEN-WHILE))
 (4 4 (:REWRITE C::EXEC-STMT-WHEN-RETURN))
 (4 4 (:REWRITE C::EXEC-STMT-WHEN-IFELSE))
 (4 4 (:REWRITE C::EXEC-STMT-WHEN-IF))
 (4 4 (:REWRITE C::EXEC-EXPR-PURE-WHEN-UNARY))
 (4 4 (:REWRITE C::EXEC-EXPR-PURE-WHEN-CAST))
 (4 4 (:REWRITE C::EXEC-EXPR-PURE-WHEN-ARRSUB))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-SUB-AND-UINT-WHEN-ULONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-SUB-AND-UINT-WHEN-ULLONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-SUB-AND-UINT-WHEN-SLONG))
 (4 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-SUB-AND-UINT-WHEN-SLLONG))
 (2 2 (:REWRITE C::VALUEP-WHEN-USHORTP))
 (2 2 (:REWRITE C::VALUEP-WHEN-UCHARP))
 (2 2 (:REWRITE C::VALUEP-WHEN-SSHORTP))
 (2 2 (:REWRITE C::VALUEP-WHEN-SCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-CALL-OF-PURE-WHEN-CALL))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-USHORT-ARRAYP-AND-USHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-USHORT-ARRAYP-AND-ULONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-USHORT-ARRAYP-AND-ULLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-USHORT-ARRAYP-AND-UINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-USHORT-ARRAYP-AND-UCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-USHORT-ARRAYP-AND-SSHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-USHORT-ARRAYP-AND-SLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-USHORT-ARRAYP-AND-SLLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-USHORT-ARRAYP-AND-SINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-USHORT-ARRAYP-AND-SCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULONG-ARRAYP-AND-USHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULONG-ARRAYP-AND-ULONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULONG-ARRAYP-AND-ULLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULONG-ARRAYP-AND-UINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULONG-ARRAYP-AND-UCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULONG-ARRAYP-AND-SSHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULONG-ARRAYP-AND-SLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULONG-ARRAYP-AND-SLLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULONG-ARRAYP-AND-SINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULONG-ARRAYP-AND-SCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULLONG-ARRAYP-AND-USHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULLONG-ARRAYP-AND-ULONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULLONG-ARRAYP-AND-ULLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULLONG-ARRAYP-AND-UINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULLONG-ARRAYP-AND-UCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULLONG-ARRAYP-AND-SSHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULLONG-ARRAYP-AND-SLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULLONG-ARRAYP-AND-SLLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULLONG-ARRAYP-AND-SINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-ULLONG-ARRAYP-AND-SCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UINT-ARRAYP-AND-USHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UINT-ARRAYP-AND-ULONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UINT-ARRAYP-AND-ULLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UINT-ARRAYP-AND-UINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UINT-ARRAYP-AND-UCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UINT-ARRAYP-AND-SSHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UINT-ARRAYP-AND-SLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UINT-ARRAYP-AND-SLLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UINT-ARRAYP-AND-SINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UINT-ARRAYP-AND-SCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UCHAR-ARRAYP-AND-USHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UCHAR-ARRAYP-AND-ULONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UCHAR-ARRAYP-AND-ULLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UCHAR-ARRAYP-AND-UINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UCHAR-ARRAYP-AND-UCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UCHAR-ARRAYP-AND-SSHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UCHAR-ARRAYP-AND-SLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UCHAR-ARRAYP-AND-SLLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UCHAR-ARRAYP-AND-SINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-UCHAR-ARRAYP-AND-SCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SSHORT-ARRAYP-AND-USHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SSHORT-ARRAYP-AND-ULONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SSHORT-ARRAYP-AND-ULLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SSHORT-ARRAYP-AND-UINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SSHORT-ARRAYP-AND-UCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SSHORT-ARRAYP-AND-SSHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SSHORT-ARRAYP-AND-SLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SSHORT-ARRAYP-AND-SLLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SSHORT-ARRAYP-AND-SINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SSHORT-ARRAYP-AND-SCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLONG-ARRAYP-AND-USHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLONG-ARRAYP-AND-ULONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLONG-ARRAYP-AND-ULLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLONG-ARRAYP-AND-UINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLONG-ARRAYP-AND-UCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLONG-ARRAYP-AND-SSHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLONG-ARRAYP-AND-SLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLONG-ARRAYP-AND-SLLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLONG-ARRAYP-AND-SINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLONG-ARRAYP-AND-SCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLLONG-ARRAYP-AND-USHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLLONG-ARRAYP-AND-ULONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLLONG-ARRAYP-AND-ULLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLLONG-ARRAYP-AND-UINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLLONG-ARRAYP-AND-UCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLLONG-ARRAYP-AND-SSHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLLONG-ARRAYP-AND-SLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLLONG-ARRAYP-AND-SLLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLLONG-ARRAYP-AND-SINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SLLONG-ARRAYP-AND-SCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SINT-ARRAYP-AND-USHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SINT-ARRAYP-AND-ULONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SINT-ARRAYP-AND-ULLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SINT-ARRAYP-AND-UINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SINT-ARRAYP-AND-UCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SINT-ARRAYP-AND-SSHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SINT-ARRAYP-AND-SLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SINT-ARRAYP-AND-SLLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SINT-ARRAYP-AND-SINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SINT-ARRAYP-AND-SCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SCHAR-ARRAYP-AND-USHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SCHAR-ARRAYP-AND-ULONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SCHAR-ARRAYP-AND-ULLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SCHAR-ARRAYP-AND-UINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SCHAR-ARRAYP-AND-UCHARP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SCHAR-ARRAYP-AND-SSHORTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SCHAR-ARRAYP-AND-SLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SCHAR-ARRAYP-AND-SLLONGP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SCHAR-ARRAYP-AND-SINTP))
 (2 2 (:REWRITE C::EXEC-EXPR-ASG-ARRSUB-WHEN-SCHAR-ARRAYP-AND-SCHARP))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-SHR))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-SHL))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-NE))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-LT))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-LE))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-GT))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-GE))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-EQ))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-BITXOR))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-BITIOR))
 (2 2 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-BITAND))
 (2 2 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-RESULTP-AND-NOT-ERRORP))
 (2 2 (:REWRITE C::<<-OF-IDENT-AND-IDENT))
 (1 1 (:REWRITE C::EXEC-BLOCK-ITEM-WHEN-DECLON))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-REM))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-DIV))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-WHEN-ADD))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-SUB-WHEN-ULONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-SUB-WHEN-ULLONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-SUB-WHEN-SLONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-SUB-WHEN-SLLONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-MUL-WHEN-ULONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-MUL-WHEN-ULLONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-MUL-WHEN-SLONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-MUL-WHEN-SLLONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-MUL-AND-UINT-WHEN-ULONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-MUL-AND-UINT-WHEN-ULLONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-MUL-AND-UINT-WHEN-SLONG))
 (1 1 (:REWRITE C::EXEC-BINARY-STRICT-PURE-OF-MUL-AND-UINT-WHEN-SLLONG))
 )
(C::|*PROGRAM*-f$loop-CORRECT-LEMMA|
 (955 955 (:REWRITE C::READ-VAR-OF-CONST-IDENTIFIER))
 (740 590 (:REWRITE C::VALUEP-WHEN-ULONGP))
 (740 590 (:REWRITE C::VALUEP-WHEN-ULLONGP))
 (740 590 (:REWRITE C::VALUEP-WHEN-SLONGP))
 (740 590 (:REWRITE C::VALUEP-WHEN-SLLONGP))
 (740 590 (:REWRITE C::VALUEP-WHEN-SINTP))
 (718 532 (:REWRITE C::NOT-UINTP-WHEN-USHORTP))
 (718 532 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
 (718 532 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
 (718 532 (:REWRITE C::NOT-UINTP-WHEN-UCHARP))
 (718 532 (:REWRITE C::NOT-UINTP-WHEN-SSHORTP))
 (718 532 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
 (718 532 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
 (718 532 (:REWRITE C::NOT-UINTP-WHEN-SINTP))
 (718 532 (:REWRITE C::NOT-UINTP-WHEN-SCHARP))
 (590 590 (:REWRITE C::VALUEP-WHEN-POINTERP))
 (532 532 (:REWRITE C::NOT-UINTP-WHEN-POINTERP))
 (434 434 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-RESULTP-AND-NOT-ERRORP))
 (420 270 (:REWRITE C::NOT-USHORTP-WHEN-ULONGP))
 (420 270 (:REWRITE C::NOT-USHORTP-WHEN-ULLONGP))
 (420 270 (:REWRITE C::NOT-USHORTP-WHEN-SLONGP))
 (420 270 (:REWRITE C::NOT-USHORTP-WHEN-SLLONGP))
 (420 270 (:REWRITE C::NOT-USHORTP-WHEN-SINTP))
 (420 270 (:REWRITE C::NOT-UCHARP-WHEN-ULONGP))
 (420 270 (:REWRITE C::NOT-UCHARP-WHEN-ULLONGP))
 (420 270 (:REWRITE C::NOT-UCHARP-WHEN-SLONGP))
 (420 270 (:REWRITE C::NOT-UCHARP-WHEN-SLLONGP))
 (420 270 (:REWRITE C::NOT-UCHARP-WHEN-SINTP))
 (420 270 (:REWRITE C::NOT-SSHORTP-WHEN-ULONGP))
 (420 270 (:REWRITE C::NOT-SSHORTP-WHEN-ULLONGP))
 (420 270 (:REWRITE C::NOT-SSHORTP-WHEN-SLONGP))
 (420 270 (:REWRITE C::NOT-SSHORTP-WHEN-SLLONGP))
 (420 270 (:REWRITE C::NOT-SSHORTP-WHEN-SINTP))
 (420 270 (:REWRITE C::NOT-SCHARP-WHEN-ULONGP))
 (420 270 (:REWRITE C::NOT-SCHARP-WHEN-ULLONGP))
 (420 270 (:REWRITE C::NOT-SCHARP-WHEN-SLONGP))
 (420 270 (:REWRITE C::NOT-SCHARP-WHEN-SLLONGP))
 (420 270 (:REWRITE C::NOT-SCHARP-WHEN-SINTP))
 (270 270 (:REWRITE C::NOT-USHORTP-WHEN-POINTERP))
 (270 270 (:REWRITE C::NOT-UCHARP-WHEN-POINTERP))
 (270 270 (:REWRITE C::NOT-SSHORTP-WHEN-POINTERP))
 (270 270 (:REWRITE C::NOT-SCHARP-WHEN-POINTERP))
 (198 99 (:REWRITE C::NOT-ERRORP-WHEN-COMPUSTATEP))
 (146 146 (:REWRITE C::WRITE-VAR-OF-CONST-IDENTIFIER))
 (131 131 (:REWRITE C::VALUEP-WHEN-USHORTP))
 (131 131 (:REWRITE C::VALUEP-WHEN-UCHARP))
 (131 131 (:REWRITE C::VALUEP-WHEN-SSHORTP))
 (131 131 (:REWRITE C::VALUEP-WHEN-SCHARP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-VALUE-LISTP-REWRITE))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-USHORT-ARRAYP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-ULONG-ARRAYP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-ULLONG-ARRAYP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-UINT-ARRAYP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-UCHAR-ARRAYP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-SSHORT-ARRAYP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-SLONG-ARRAYP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-SLLONG-ARRAYP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-SINT-ARRAYP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-SCOPE-LISTP))
 (111 111 (:REWRITE C::NOT-ERRORP-WHEN-SCHAR-ARRAYP))
 (99 99 (:REWRITE C::NOT-ERRORP-WHEN-SCOPEP))
 (19 19 (:REWRITE C::NOT-ZP-OF-LIMIT-MINUS-CONST))
 )
(C::|*PROGRAM*-f$loop-CORRECT|)
(|f-FUN-ENV|)
(|f-RESULT|)
(C::|*PROGRAM*-f-CORRECT|
 (23 20 (:REWRITE C::VALUEP-WHEN-ULONGP))
 (23 20 (:REWRITE C::VALUEP-WHEN-ULLONGP))
 (23 20 (:REWRITE C::VALUEP-WHEN-SLONGP))
 (23 20 (:REWRITE C::VALUEP-WHEN-SLLONGP))
 (23 20 (:REWRITE C::VALUEP-WHEN-SINTP))
 (20 20 (:REWRITE C::VALUEP-WHEN-POINTERP))
 (14 8 (:REWRITE C::NOT-UINTP-WHEN-USHORTP))
 (14 8 (:REWRITE C::NOT-UINTP-WHEN-ULONGP))
 (14 8 (:REWRITE C::NOT-UINTP-WHEN-ULLONGP))
 (14 8 (:REWRITE C::NOT-UINTP-WHEN-UCHARP))
 (14 8 (:REWRITE C::NOT-UINTP-WHEN-SSHORTP))
 (14 8 (:REWRITE C::NOT-UINTP-WHEN-SLONGP))
 (14 8 (:REWRITE C::NOT-UINTP-WHEN-SLLONGP))
 (14 8 (:REWRITE C::NOT-UINTP-WHEN-SINTP))
 (14 8 (:REWRITE C::NOT-UINTP-WHEN-SCHARP))
 (10 7 (:REWRITE C::NOT-USHORTP-WHEN-ULONGP))
 (10 7 (:REWRITE C::NOT-USHORTP-WHEN-ULLONGP))
 (10 7 (:REWRITE C::NOT-USHORTP-WHEN-SLONGP))
 (10 7 (:REWRITE C::NOT-USHORTP-WHEN-SLLONGP))
 (10 7 (:REWRITE C::NOT-USHORTP-WHEN-SINTP))
 (10 7 (:REWRITE C::NOT-UCHARP-WHEN-ULONGP))
 (10 7 (:REWRITE C::NOT-UCHARP-WHEN-ULLONGP))
 (10 7 (:REWRITE C::NOT-UCHARP-WHEN-SLONGP))
 (10 7 (:REWRITE C::NOT-UCHARP-WHEN-SLLONGP))
 (10 7 (:REWRITE C::NOT-UCHARP-WHEN-SINTP))
 (10 7 (:REWRITE C::NOT-SSHORTP-WHEN-ULONGP))
 (10 7 (:REWRITE C::NOT-SSHORTP-WHEN-ULLONGP))
 (10 7 (:REWRITE C::NOT-SSHORTP-WHEN-SLONGP))
 (10 7 (:REWRITE C::NOT-SSHORTP-WHEN-SLLONGP))
 (10 7 (:REWRITE C::NOT-SSHORTP-WHEN-SINTP))
 (10 7 (:REWRITE C::NOT-SCHARP-WHEN-ULONGP))
 (10 7 (:REWRITE C::NOT-SCHARP-WHEN-ULLONGP))
 (10 7 (:REWRITE C::NOT-SCHARP-WHEN-SLONGP))
 (10 7 (:REWRITE C::NOT-SCHARP-WHEN-SLLONGP))
 (10 7 (:REWRITE C::NOT-SCHARP-WHEN-SINTP))
 (8 8 (:REWRITE C::NOT-UINTP-WHEN-POINTERP))
 (7 7 (:REWRITE C::NOT-USHORTP-WHEN-POINTERP))
 (7 7 (:REWRITE C::NOT-UCHARP-WHEN-POINTERP))
 (7 7 (:REWRITE C::NOT-SSHORTP-WHEN-POINTERP))
 (7 7 (:REWRITE C::NOT-SCHARP-WHEN-POINTERP))
 (3 3 (:REWRITE C::WRITE-VAR-OKP-WHEN-VALUEP-OF-READ-VAR))
 (2 2 (:REWRITE C::WRITE-VAR-OF-CONST-IDENTIFIER))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-UNARY))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-STRICT-PURE-BINARY))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-COND))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-CAST))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-BINARY-LOGOR))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-BINARY-LOGAND))
 (2 2 (:REWRITE C::EXEC-EXPR-PURE-WHEN-ARRSUB))
 (2 2 (:REWRITE C::EXEC-EXPR-CALL-OF-PURE-WHEN-CALL))
 (1 1 (:REWRITE C::EXEC-FUN-OF-CONST-IDENTIFIER))
 (1 1 (:REWRITE C::COMPUSTATEP-WHEN-COMPUSTATE-RESULTP-AND-NOT-ERRORP))
 )
