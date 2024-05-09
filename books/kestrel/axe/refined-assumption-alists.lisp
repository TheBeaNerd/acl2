; An alist that stores assumptions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;(include-book "kestrel/alists-light/uniquify-alist-eq" :dir :system)
(include-book "renaming-array")
(include-book "axe-trees")
(include-book "refine-assumptions")
(include-book "darg-listp")
;(include-book "kestrel/utilities/forms" :dir :system)
;(include-book "kestrel/utilities/erp" :dir :system)
;(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))

;;; Usage (see refine-assumptions-and-add-to-dag-array):
;;;
;;; 1. Call refine-assumptions-for-matching to produce a list of terms.
;;;
;;; 2. Call add-refined-assumptions-to-dag-array to add the args of the refined
;;;    assumptions to the dag-array, yielding a list of function call exprs.
;;;
;;; 3. Call make-refined-assumption-alist on the resulting exprs.

;; See also the comment "How we use the refined-assumption-alist" in make-rewriter-simple.lisp

(local (in-theory (disable symbol-listp ; prevent inductions
                           wf-dagp wf-dagp-expander)))

;; (defthm darg-listp-when-all-dargp ; eventually remove this
;;   (implies (all-dargp items)
;;            (equal (darg-listp items)
;;                   (true-listp items)))
;;   :hints (("Goal" :in-theory (enable darg-listp))))

;; (defthmd all-dargp-when-darg-listp ; eventually remove
;;   (implies (darg-listp x)
;;            (all-dargp x))
;;   :hints (("Goal" :in-theory (enable darg-listp))))

;move
(defthm darg-listp-of-dargs-when-dag-exprp
  (implies (and (dag-exprp expr)
                (not (eq 'quote (car expr))))
           (darg-listp (dargs expr)))
  :hints (("Goal" :in-theory (enable dag-exprp))))

(defun darg-list-listp (items)
  (declare (xargs :guard t))
  (if (atom items)
      (null items)
    (and (darg-listp (first items))
         (darg-list-listp (rest items)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A "refined-assumption-alist" is an efficient way to store a list of
;; axe-trees, all of which are function calls applied to dargs (args that are nodenums
;; / quoteps).  We use "term indexing": the alist maps each topmost function to
;; a list of darg-lists (one for each call of fn in the list).
;; TODO: Consider using a propery list world instead of an alist.

;could add more checks to this
(defun refined-assumption-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let ((entry (car alist)))
      (and (consp entry)
           (symbolp (car entry)) ;; should lambdas be allowed?
           ;; (not (eq 'quote (car entry))) ;; TODO: Uncomment
           (darg-list-listp (cdr entry)) ; checks that each member of (cdr entry) is a list of nodenum/quoteps
           (refined-assumption-alistp (cdr alist))))))

(defthm symbol-alistp-when-refined-assumption-alistp-cheap
  (implies (refined-assumption-alistp acc)
           (symbol-alistp acc))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;; todo: ensure we always use lookup-in-refined-assumption-alist and then remove these
(defthm true-listp-of-lookup-equal-when-refined-assumption-alistp-cheap
  (implies (refined-assumption-alistp alist)
           (true-listp (lookup-equal sym alist)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

(defthm darg-list-listp-of-lookup-equal-when-refined-assumption-alistp
  (implies (refined-assumption-alistp alist)
           (darg-list-listp (lookup-equal fn alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Just lookup-eq (currently) but kept separate to make a nice abstraction for refined-assumption-alists.
;; Returns a list of dargs
(defund-inline lookup-in-refined-assumption-alist (fn refined-assumption-alist)
  (declare (xargs :guard (and (symbolp fn)
                              (refined-assumption-alistp refined-assumption-alist))))
  (lookup-eq fn refined-assumption-alist))

(defthm darg-list-listp-of-lookup-in-refined-assumption-alist
  (implies (refined-assumption-alistp refined-assumption-alist)
           (darg-list-listp (lookup-in-refined-assumption-alist fn refined-assumption-alist)))
  :hints (("Goal" :in-theory (enable lookup-in-refined-assumption-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;;;
;;; bounded refined-assumption-alists
;;;

;; Recognizes a true-list of bounded darg lists.
(defund bounded-darg-list-listp (items dag-len)
  (declare (xargs :guard (natp dag-len)))
  (if (atom items)
      (null items)
    (and (bounded-darg-listp (first items) dag-len)
         (bounded-darg-list-listp (rest items) dag-len))))

(defthm bounded-darg-list-listp-forward-to-true-listp
  (implies (bounded-darg-list-listp items dag-len)
           (true-listp items))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm bounded-darg-list-listp-of-nil
  (bounded-darg-list-listp nil dag-len)
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm bounded-darg-list-listp-of-cons
  (equal (bounded-darg-list-listp (cons a x) dag-len)
         (and (bounded-darg-listp a dag-len)
              (bounded-darg-list-listp x dag-len)))
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm bounded-darg-list-listp-monotone
  (implies (and (bounded-darg-list-listp alist bound2)
                (<= bound2 bound))
           (bounded-darg-list-listp alist bound))
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm bounded-darg-listp-of-car
  (implies (bounded-darg-list-listp items dag-len)
           (bounded-darg-listp (car items) dag-len))
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm bounded-darg-list-listp-of-cdr
  (implies (bounded-darg-list-listp items dag-len)
           (bounded-darg-list-listp (cdr items) dag-len))
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthm darg-list-listp-when-bounded-darg-list-listp
  (implies (bounded-darg-list-listp items bound)
           (darg-list-listp items))
  :hints (("Goal" :in-theory (enable bounded-darg-list-listp))))

(defthmd true-list-of-car-when-bounded-darg-list-listp
  (implies (and (bounded-darg-list-listp assumption-arg-lists dag-len)
                (consp assumption-arg-lists))
           (true-listp (car assumption-arg-lists))))

(defthmd darg-listp-of-car-when-bounded-darg-list-listp
  (implies (and (bounded-darg-list-listp assumption-arg-lists dag-len)
                (consp assumption-arg-lists))
           (darg-listp (car assumption-arg-lists))))

;;;
;;; bounded-refined-assumption-alistp
;;;

(defund bounded-refined-assumption-alistp (alist bound)
  (declare (xargs :guard (natp bound)))
  (if (atom alist)
      (null alist)
    (let ((entry (car alist)))
      (and (consp entry)
           (symbolp (car entry)) ;; should lambdas be allowed?
           ;; (not (eq 'quote (car entry))) ;; TODO: Uncomment
           (bounded-darg-list-listp (cdr entry) bound)
           (bounded-refined-assumption-alistp (cdr alist) bound)))))

(defthm refined-assumption-alistp-when-bounded-refined-assumption-alistp
  (implies (bounded-refined-assumption-alistp alist bound)
           (refined-assumption-alistp alist))
  :hints (("Goal" :in-theory (e/d (bounded-refined-assumption-alistp)
                                  (darg-list-listp)))))

(local
  (defthm bounded-darg-list-listp-of-lookup-equal-when-bounded-refined-assumption-alistp
    (implies (bounded-refined-assumption-alistp refined-assumption-alist bound)
             (bounded-darg-list-listp (lookup-equal fn refined-assumption-alist) bound))
    :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp lookup-equal assoc-equal)))))

(defthm bounded-darg-list-listp-of-lookup-in-refined-assumption-alist
  (implies (bounded-refined-assumption-alistp refined-assumption-alist bound)
           (bounded-darg-list-listp (lookup-in-refined-assumption-alist fn refined-assumption-alist) bound))
  :hints (("Goal" :in-theory (enable lookup-in-refined-assumption-alist))))

(defthm bounded-refined-assumption-alistp-monotone
  (implies (and (bounded-refined-assumption-alistp alist bound2)
                (<= bound2 bound))
           (bounded-refined-assumption-alistp alist bound))
  :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp))))

(local
  (defthm bounded-refined-assumption-alistp-of-uniquify-alist-eq-aux
    (implies (and (bounded-refined-assumption-alistp alist bound)
                  (bounded-refined-assumption-alistp acc bound))
             (bounded-refined-assumption-alistp (uniquify-alist-eq-aux alist acc) bound))
    :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp uniquify-alist-eq-aux)))))



(defthm bounded-refined-assumption-alistp-forward-to-symbol-alistp
  (implies (bounded-refined-assumption-alistp refined-assumption-alist bound)
           (symbol-alistp refined-assumption-alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp))))

;; ;does not check that the nodenums are not too big
;; ;todo: replace?  just use DAG-FUNCTION-CALL-EXPRP?
;; ;a kind of axe-tree
;; (defund weak-dag-fun-call-exprp (expr)
;;   (declare (xargs :guard t))
;;   (and (consp expr)
;;        (symbolp (ffn-symb expr)) ;disallows lambdas
;;        (not (eq 'quote (ffn-symb expr)))
;;        (darg-listp (fargs expr))))

;; (defthm weak-dag-fun-call-exprp-forward-to-true-listp
;;   (implies (weak-dag-fun-call-exprp expr)
;;            (true-listp expr))
;;   :rule-classes :forward-chaining
;;   :hints (("Goal" :in-theory (enable weak-dag-fun-call-exprp))))

;; (defthm weak-dag-fun-call-exprp-of-cons
;;   (equal (weak-dag-fun-call-exprp (cons fn args))
;;          (and (symbolp fn)
;;               (not (eq 'quote fn))
;;               (darg-listp args)))
;;   :hints (("Goal" :in-theory (enable weak-dag-fun-call-exprp))))

(local
  (defthm refined-assumption-alistp-of-uniquify-alist-eq-aux
    (implies (and (refined-assumption-alistp acc)
                  (refined-assumption-alistp alist))
             (refined-assumption-alistp (uniquify-alist-eq-aux alist acc)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Adds the EXPRS to the REFINED-ASSUMPTION-ALIST.
;the exprs are fn calls applied to dargs (nodenums / quoteps)
;; We could optimize this using fast alists or property list worlds.
(defund extend-refined-assumption-alist (exprs refined-assumption-alist)
  (declare (xargs :guard (and (true-listp exprs)
                              (all-dag-function-call-exprp exprs)
                              (refined-assumption-alistp refined-assumption-alist))))
  (if (endp exprs)
      (uniquify-alist-eq refined-assumption-alist)
    (b* ((expr (first exprs))
         (fn (ffn-symb expr))
         (args (dargs expr))
         (arg-lists-for-fn (lookup-eq fn refined-assumption-alist))
         (new-arg-lists-for-fn (cons args arg-lists-for-fn)))
        (extend-refined-assumption-alist (rest exprs)
                                         (acons-fast fn new-arg-lists-for-fn refined-assumption-alist)))))

(defthm refined-assumption-alistp-of-extend-refined-assumption-alist
  (implies (and (refined-assumption-alistp refined-assumption-alist)
                (all-dag-function-call-exprp exprs))
           (refined-assumption-alistp (extend-refined-assumption-alist exprs refined-assumption-alist)))
  :hints (("Goal" :in-theory (enable extend-refined-assumption-alist))))

(defthm bounded-refined-assumption-alistp-of-extend-refined-assumption-alist
  (implies (and (bounded-refined-assumption-alistp refined-assumption-alist bound)
                (all-dag-function-call-exprp exprs)
                (bounded-dag-expr-listp bound exprs))
           (bounded-refined-assumption-alistp (extend-refined-assumption-alist exprs refined-assumption-alist) bound))
  :hints (("Goal" :in-theory (enable bounded-refined-assumption-alistp extend-refined-assumption-alist
                                     dag-function-call-exprp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Makes a refined-assumption-alist representing the EXPRS.
(defund make-refined-assumption-alist (exprs)
  (declare (xargs :guard (and (true-listp exprs)
                              (all-dag-function-call-exprp exprs))))
  (extend-refined-assumption-alist exprs nil))

(defthm refined-assumption-alistp-of-make-refined-assumption-alist
  (implies (all-dag-function-call-exprp exprs)
           (refined-assumption-alistp (make-refined-assumption-alist exprs)))
  :hints (("Goal" :in-theory (enable make-refined-assumption-alist))))

(defthm bounded-refined-assumption-alistp-of-make-refined-assumption-alist
  (implies (and (all-dag-function-call-exprp exprs)
                (bounded-dag-expr-listp bound exprs))
           (bounded-refined-assumption-alistp (make-refined-assumption-alist exprs) bound))
  :hints (("Goal" :in-theory (enable make-refined-assumption-alist
                                     bounded-refined-assumption-alistp))))

;;;
;;; refine-assumptions-and-add-to-dag-array
;;;

;; Returns (mv erp refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist).
;; First, refine the assumptions for matching.  Then, add each one's args to the DAG.  Finally, build the refined-assumption-alist.
(defund refine-assumptions-and-add-to-dag-array (assumptions
                                                 dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist
                                                 known-boolean-fns)
  (declare (xargs :guard (and (pseudo-term-listp assumptions)
                              (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                              (symbol-listp known-boolean-fns))))
  (b* ((refined-terms (refine-assumptions-for-matching assumptions known-boolean-fns nil))
       ((mv erp refined-assumption-exprs dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
        (add-refined-assumptions-to-dag-array refined-terms
                                              dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist
                                              dag-array-name
                                              dag-parent-array-name
                                              nil))
       ((when erp) (mv erp nil dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist))
       (refined-assumption-alist (make-refined-assumption-alist refined-assumption-exprs)))
    (mv (erp-nil) refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)))

(defthm refine-assumptions-and-add-to-dag-array-return-type
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-listp known-boolean-fns)
                ;; no errors:
                (not (mv-nth 0 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
           (mv-let (erp refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns)
             (declare (ignore erp ))
             (and (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                  (refined-assumption-alistp refined-assumption-alist)
                  (bounded-refined-assumption-alistp refined-assumption-alist dag-len)
                  (natp dag-len))))
  :hints (("Goal" :in-theory (e/d (refine-assumptions-and-add-to-dag-array) (natp)))))

(defthm refine-assumptions-and-add-to-dag-array-return-type-gen
  (implies (and (pseudo-term-listp assumptions)
                (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
                (symbol-listp known-boolean-fns)
                ;; no errors:
                (not (mv-nth 0 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
           (mv-let (erp refined-assumption-alist dag-array dag-len dag-parent-array dag-constant-alist dag-variable-alist)
             (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns)
             (declare (ignore erp DAG-ARRAY DAG-PARENT-ARRAY DAG-CONSTANT-ALIST DAG-VARIABLE-ALIST))
             (implies (<= dag-len bound)
                      (bounded-refined-assumption-alistp refined-assumption-alist bound))))
  :hints (("Goal" :use (:instance refine-assumptions-and-add-to-dag-array-return-type)
           :in-theory (disable refine-assumptions-and-add-to-dag-array-return-type))))

;; (defthm dargp-of-mv-nth-3-of-refine-assumptions-and-add-to-dag-array-return-type
;;   (implies (and (pseudo-term-listp assumptions)
;;                 (wf-dagp dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist)
;;                 (symbol-listp known-boolean-fns)
;;                 ;; no errors:
;;                 (not (mv-nth 0 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
;;            (dargp (mv-nth 3 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
;;   :hints (("Goal" :use (:instance refine-assumptions-and-add-to-dag-array-return-type)
;;            :in-theory (disable refine-assumptions-and-add-to-dag-array-return-type))))

(defthm natp-of-mv-nth-3-of-refine-assumptions-and-add-to-dag-array-return-type
  (implies (natp dag-len)
           (natp (mv-nth 3 (refine-assumptions-and-add-to-dag-array assumptions dag-array-name dag-array dag-len dag-parent-array-name dag-parent-array dag-constant-alist dag-variable-alist known-boolean-fns))))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable refine-assumptions-and-add-to-dag-array))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; nodenum-equal-to-refined-assumptionp
;;;

;; TODO: Just call member-equal and remove the p from this name?
;; Only called by the legacy rewriter?
(defund nodenum-equal-to-refined-assumptionp (nodenum refined-assumption-alist dag-array)
  (declare (xargs :guard (and (natp nodenum)
                              (pseudo-dag-arrayp 'dag-array dag-array (+ 1 nodenum))
                              (refined-assumption-alistp refined-assumption-alist))))
  (let* ((expr (aref1 'dag-array dag-array nodenum)))
    (and (consp expr) ;refined assumptions must be function calls
         (let ((fn (ffn-symb expr)))
           (and (not (eq 'quote fn))
                (let ((arglists-for-fn (lookup-eq fn refined-assumption-alist)))
                  (memberp (dargs expr) arglists-for-fn)))))))

;; ;the assumptions are fn calls applied to nodenums/quoteps
;; (defun fixup-refined-assumptions (refined-assumptions renaming-array-name renaming-array acc)
;;   (if (endp refined-assumptions)
;;       acc
;;     (let* ((assumption (first refined-assumptions))
;;            (fn (ffn-symb assumption))
;;            (args (fargs assumption))
;;            (fixed-up-args (rename-dargs args renaming-array-name renaming-array))
;;            (fixed-up-assumption (cons fn fixed-up-args))
;;            )
;;       (fixup-refined-assumptions (rest refined-assumptions)
;;                                  renaming-array-name
;;                                  renaming-array
;;                                  (cons fixed-up-assumption
;;                                        acc)))))

(defun largest-non-quotep-in-darg-lists (darg-lists)
  (declare (xargs :guard (darg-list-listp darg-lists)))
  (if (endp darg-lists)
      -1 ;think about this as the default
    (max (largest-non-quotep (first darg-lists))
         (largest-non-quotep-in-darg-lists (rest darg-lists)))))

;; also reverses.
(defund fixup-refined-assumption-arg-lists (darg-lists renaming-array-name renaming-array acc)
  (declare (xargs :guard (and (darg-list-listp darg-lists)
                              (renaming-arrayp renaming-array-name renaming-array (+ 1 (largest-non-quotep-in-darg-lists darg-lists))))))
  (if (endp darg-lists)
      acc ; could reverse here
    (fixup-refined-assumption-arg-lists (rest darg-lists)
                                        renaming-array-name
                                        renaming-array
                                        (cons (rename-dargs (first darg-lists) renaming-array-name renaming-array)
                                              acc))))

;; todo: guard is awkward.  pass in the nume-valid-nodes of the renaming-array and use as the bound
(defund fixup-refined-assumption-alist (refined-assumption-alist renaming-array-name renaming-array acc)
  ;; (declare (xargs :guard (and (bounded-refined-assumption-alistp refined-assumption-alist num-valid-nodes)
  ;;                             (renaming-arrayp renaming-array-name renaming-array num-valid-nodes))))
  (if (endp refined-assumption-alist)
      acc
    (let* ((entry (first refined-assumption-alist))
           (fn (car entry))
           (arg-lists (cdr entry))
           (fixed-up-arg-lists (fixup-refined-assumption-arg-lists arg-lists renaming-array-name renaming-array nil)))
      (fixup-refined-assumption-alist (rest refined-assumption-alist)
                                      renaming-array-name
                                      renaming-array
                                      (acons-fast fn fixed-up-arg-lists acc)))))

;;;
;;; decoding refined-assumption-alists (only used to implement WORK-HARD)
;;;

;see cons-onto-all
(defund add-fn-calls (fn arg-lists acc)
  (declare (xargs :guard (true-listp arg-lists)))
  (if (endp arg-lists)
      acc
    (add-fn-calls fn
                  (rest arg-lists)
                  (cons (cons fn (first arg-lists)) acc))))

(defund decode-refined-assumption-alist-aux (refined-assumption-alist acc)
  (declare (xargs :guard (refined-assumption-alistp refined-assumption-alist)))
  (if (endp refined-assumption-alist)
      acc
    (let* ((entry (car refined-assumption-alist))
           (fn (car entry))
           (arg-lists (cdr entry)))
      (decode-refined-assumption-alist-aux (cdr refined-assumption-alist)
                                           (add-fn-calls fn arg-lists acc)))))

;turns refined-assumption-alist back into the equivalent list of axe-trees
;; todo: prove return type
(defund decode-refined-assumption-alist (refined-assumption-alist)
  (declare (xargs :guard (refined-assumption-alistp refined-assumption-alist)))
  (decode-refined-assumption-alist-aux refined-assumption-alist nil))
