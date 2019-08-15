; Cryptocurrency Hierarchical Deterministic Wallet Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Main Author: Alessandro Coglio (coglio@kestrel.edu)
; Contributing Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "HDWALLET")

(include-book "wallet")

; temporarily exclude the following from the manual
; until some conflicts between libraries
; (indirectly included by the following file)
; are resolved:
;; (include-book "wallet-executable")
