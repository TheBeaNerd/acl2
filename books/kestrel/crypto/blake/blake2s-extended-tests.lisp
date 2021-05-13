; Tests of blake2s-extended
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "BLAKE")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "kestrel/utilities/integers-from-to" :dir :system)

(include-book "blake2s-extended")
(include-book "blake2s-tests") ;todo: reduce, for hex-string-to-bytes

;; TODO: Add more tests (e.g., one with a key)

;; Suppresses any errors.
(defund hex-string-to-bytes! (s)
  (declare (xargs :guard (stringp s)))
  (mv-let (erp val)
    (hex-string-to-bytes s)
    (declare (ignore erp))
    val))

;; A test with no salt or personalization
(acl2::assert-equal (blake2s-extended '(0 1 2)
                                      nil ;key
                                      nil ;salt
                                      nil ;personalization
                                      32)
                    (hex-string-to-bytes! "e8f91c6ef232a041452ab0e149070cdd7dd1769e75b3a5921be37876c45c9900"))


;; A test with a salt
(acl2::assert-equal (blake2s-extended '(0 1 2)
                                      nil ;key
                                      '(78 97 67 108 56 56 56 56) ;salt
                                      nil ;personalization
                                      32)
                    (hex-string-to-bytes! "500b8ddc2ab792780fe152de2d99f1e97f39fafb6691ae4126168b48acf91a87"))

;;;
;;; Tests with personalization:
;;;

(acl2::assert-equal (blake2s-extended '(0 1 2)
                                      nil ;key
                                      nil ;salt
                                      '(90 99 97 115 104 95 80 72) ;personalization "Zcash_PH"
                                      32)
                    (hex-string-to-bytes! "79e9fa3e5f9eb03e114b97a81b0104c19724726d1f23f9ec1810239195be01ca"))

;; This test is from github.com/zkcrypto/bellman/blob/main/src/gadgets/blake2s.rs
(acl2::assert-equal (blake2s-extended '()
                                      nil ;key
                                      nil ;salt
                                      '(49 50 51 52 53 54 55 56) ;personalization "12345678"
                                      32)
                    (hex-string-to-bytes! "c59f682376d137f3f255e671e207d1f2374ebe504e9314208a52d9f88d69e8c8"))

;; Test with personalization and 64 bytes of input.
;; Result checked against both Python and Rust implementations.
(acl2::assert-equal (blake2s-extended (acl2::integers-from-to 0 63)
                                      nil ;key
                                      nil ;salt
                                      '(90 99 97 115 104 95 80 72) ; personalization "Zcash_PH"
                                      32)
                    (hex-string-to-bytes! "80EAC167076FC215A0AE83EF83F9E04C59F2AE3D14C0C9AFAA9D76A41791D902"))
