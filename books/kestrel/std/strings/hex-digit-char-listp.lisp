; Standard Strings Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "STR")

(include-book "std/strings/hex" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(std::deflist hex-digit-char-listp (x)
  :parents (hex)
  :short "Recognize lists of hexadecimal digit characters."
  :long
  (xdoc::topstring
   (xdoc::p
    "Unlike @(tsee hex-digit-char-list*p),
     this requires true list (i.e. @('nil')-terminated.")
   (xdoc::p
    "Since there are functions in @(see std/strings)
     that operate on @(tsee hex-digit-char-list*p),
     we provide a bridge theorem between the two recognizers."))
  (hex-digit-char-p x)
  :true-listp t
  :elementp-of-nil nil
  ///

  (defthm hex-digit-char-list*p-when-hex-digit-char-listp
    (implies (hex-digit-char-listp x)
             (hex-digit-char-list*p x))
    :hints (("Goal"
             :induct t
             :in-theory (enable str::hex-digit-char-list*p)))))
