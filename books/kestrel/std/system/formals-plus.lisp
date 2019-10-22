; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "pseudo-termfnp")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define formals+ ((fn pseudo-termfnp) (wrld plist-worldp))
  :returns (formals symbol-listp)
  :parents (std/system/function-queries)
  :short (xdoc::topstring
          (xdoc::seetopic "std/system/logic-friendly" "Logic-friendly")
          " variant of @(tsee formals).")
  :long
  (xdoc::topstring
   (xdoc::p
    "This returns the same result as @(tsee formals) on named functions,
     but it includes a run-time check (which should always succeed)
     on the result
     that allows us to prove the return type theorem
     without strengthening the guard on @('wrld').")
   (xdoc::p
    "Note that @(tsee formals), which is called by this function,
     causes an error on a symbol that does not name a function.")
   (xdoc::p
    "This utility also operates on lambda expressions,
     unlike @(tsee formals)."))
  (b* ((result (cond ((symbolp fn) (formals fn wrld))
                     (t (lambda-formals fn)))))
    (if (symbol-listp result)
        result
      (raise "Internal error: ~
              the formals ~x0 of ~x1 are not a true list of symbols."
             result fn)))
  :guard-hints (("Goal" :in-theory (enable pseudo-termfnp pseudo-lambdap))))
