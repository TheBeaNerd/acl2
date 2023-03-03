; A utility to gather the let-bound vars in a term
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We use the term "let var" to mean a variable bound in a lambda that is not
;; trivially bound (that is, that is not bound to itself).  Trivial bindings
;; often arise because lambdas in ACL2 must be closed.

(include-book "non-trivial-formals")
(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))

(mutual-recursion
 ;; Gather all the vars that are bound in lambdas in TERM, except don't include
 ;; variable that ar simply bound to themselves.  Vars may appear only once in
 ;; the result.  Does not include vars that are free (unless they are also
 ;; bound by a lambda).
 (defun let-vars-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       nil ;; not a lambda-bound var
     (let ((fn (ffn-symb term)))
       (if (eq fn 'quote)
           nil
         (if (consp fn)
             ;; a lambda application:
             (union-eq (non-trivial-formals (lambda-formals fn) (fargs term))
                       (union-eq (let-vars-in-term (lambda-body fn))
                                 (let-vars-in-terms (fargs term))))
           ;; not a lambda application:
           (let-vars-in-terms (fargs term)))))))

 (defun let-vars-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (union-eq (let-vars-in-term (first terms))
               (let-vars-in-terms (rest terms))))))

(make-flag let-vars-in-term)

(defthm-flag-let-vars-in-term
  (defthm symbol-listp-of-let-vars-in-term
    (implies (pseudo-termp term)
             (symbol-listp (let-vars-in-term term)))
    :flag let-vars-in-term)
  (defthm symbol-listp-of-let-vars-in-terms
    (implies (pseudo-term-listp terms)
             (symbol-listp (let-vars-in-terms terms)))
    :flag let-vars-in-terms)
  :hints (("Goal" :expand (pseudo-term-listp term)
           :in-theory (enable pseudo-term-listp))))

(defthm-flag-let-vars-in-term
  (defthm true-listp-of-let-vars-in-term
    (true-listp (let-vars-in-term term))
    :flag let-vars-in-term)
  (defthm true-listp-of-let-vars-in-terms
    (true-listp (let-vars-in-terms terms))
    :flag let-vars-in-terms)
  :hints (("Goal" :expand (pseudo-term-listp term)
           :in-theory (enable pseudo-term-listp))))

(verify-guards let-vars-in-term)
