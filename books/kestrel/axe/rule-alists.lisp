; Rule-alists: databases of rules used by Axe
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2023 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "make-axe-rules")
(include-book "stored-rules")
(include-book "kestrel/alists-light/uniquify-alist-eq" :dir :system)
(local (include-book "kestrel/lists-light/union-equal" :dir :system))

(in-theory (disable fgetprop)) ;move

;; Rule-alists are structures that index rules by the top function symbol of their LHSes.
;; TODO: Consider using a property list world to make the lookups faster.

;; A rule-alist is a database of rules used by Axe.  It maps function symbols
;; to lists of stored rules.
(defund rule-alistp (alist)
  (declare (xargs :guard t))
  (if (atom alist)
      (null alist)
    (let* ((entry (car alist)))
      (and (consp entry)
           (let ((fn (car entry))
                 (stored-rules (cdr entry)))
             (and (symbolp fn)
                  (stored-axe-rule-listp stored-rules)))
           (rule-alistp (cdr alist))))))

;disable outside of axe?
(defthm true-listp-of-lookup-equal-when-rule-alistp
  (implies (rule-alistp alist)
           (true-listp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable lookup-equal assoc-equal rule-alistp))))

(defthm stored-axe-rule-listp-of-lookup-equal-when-rule-alistp
  (implies (rule-alistp alist)
           (stored-axe-rule-listp (lookup-equal key alist)))
  :hints (("Goal" :in-theory (enable lookup-equal assoc-equal rule-alistp))))

;really of acons?
(defthm rule-alistp-of-cons-of-cons
  (equal (rule-alistp (cons (cons key val) alist))
         (and (rule-alistp alist)
              (true-listp val)
              (symbolp key)
              (stored-axe-rule-listp val)))
  :hints (("Goal" :in-theory (enable lookup-equal assoc-equal rule-alistp))))

(defthm rule-alistp-of-acons
  (implies (and (symbolp fn)
                (stored-axe-rule-listp stored-rules)
                (rule-alistp rule-alist))
           (rule-alistp (acons fn stored-rules rule-alist)))
  :hints (("Goal" :in-theory (enable rule-alistp acons))))

;rename
;disable outside of axe, or make a :forward-chaining rule
(defthm rule-alistp-means-alistp
  (implies (rule-alistp alist)
           (alistp alist))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints (("Goal" :in-theory (enable rule-alistp))))

;rename
;disable outside of axe, or make a :forward-chaining rule
(defthm rule-alistp-means-symbol-alistp
  (implies (rule-alistp alist)
           (symbol-alistp alist))
  :rule-classes ((:rewrite :backchain-limit-lst 1))
  :hints (("Goal" :in-theory (enable rule-alistp))))

;; todo: why is this about the -aux function?
(defthm rule-alistp-of-uniquify-alist-eq-aux
  (implies (and (rule-alistp alist)
                (rule-alistp acc))
           (rule-alistp (uniquify-alist-eq-aux alist acc)))
  :hints (("Goal" :in-theory (enable rule-alistp acons))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun empty-rule-alist () (declare (xargs :guard t)) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: use defun-inline?  do we use this consistently?
(defmacro get-rules-for-fn (fn rule-alist)
  `(lookup-eq ,fn ,rule-alist))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund count-rules-in-rule-alist-aux (rule-alist acc)
  (declare (xargs :guard (and (rule-alistp rule-alist)
                              (natp acc))
                  :guard-hints (("Goal" :in-theory (enable rule-alistp)))))
  (if (endp rule-alist)
      acc
    (let* ((entry (first rule-alist))
           (stored-rules (cdr entry)))
      (count-rules-in-rule-alist-aux (rest rule-alist) (+ (len stored-rules) acc)))))

(defund count-rules-in-rule-alist (rule-alist)
  (declare (xargs :guard (rule-alistp rule-alist)))
  (count-rules-in-rule-alist-aux rule-alist 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;todo: deprecate (use count-rules-in-rule-alist)
(defund rule-count-in-rule-alist (rule-alist)
  (declare (xargs :guard (rule-alistp rule-alist)
                  :verify-guards nil ;done below
                  ))
  (if (endp rule-alist)
      0
    (let* ((entry (car rule-alist))
           (stored-rules (cdr entry)))
      (+ (len stored-rules)
         (rule-count-in-rule-alist (cdr rule-alist))))))

;drop?
(defthm natp-of-rule-count-in-rule-alist
  (natp (rule-count-in-rule-alist rule-alist))
  :rule-classes (:rewrite :type-prescription))

(verify-guards rule-count-in-rule-alist
  :hints (("Goal" :in-theory (enable rule-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Check whether RULE-ALIST contains a rule named RULE-SYMBOL.
(defund rule-alist-containsp (rule-alist rule-symbol)
  (declare (xargs :guard (and (rule-alistp rule-alist)
                              (symbolp rule-symbol))
                  :guard-hints (("Goal" :in-theory (enable rule-alistp)))))
  (if (endp rule-alist)
      nil
    (let* ((entry (first rule-alist))
           (stored-rules (cdr entry)))
      (or (rule-is-presentp rule-symbol stored-rules)
          (rule-alist-containsp (rest rule-alist) rule-symbol)))))

;; test: (equal (rule-alist-containsp (make-rule-alist '(car-cons cdr-cons) state) 'car-cons) t)
;; test: (equal (rule-alist-containsp (make-rule-alist '(car-cons cdr-cons) state) 'blah) nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Prints a message for all of the RULES not in the RULE-ALIST.
(defund print-missing-rules (rules rule-alist)
  (declare (xargs :guard (and (rule-alistp rule-alist)
                              (symbol-listp rules))
                  :guard-hints (("Goal" :in-theory (enable rule-alistp)))))
  (if (endp rules)
      t
    (b* ((rule (first rules))
         (presentp (rule-alist-containsp rule-alist rule))
         (- (and (not presentp)
                 (cw "(NOTE: Rule ~x0 is not (yet) in the rule-alist.)~%" rule))))
      (print-missing-rules (rest rules) rule-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;rename
;; Returns a list of rule-names.
(defund rules-from-rule-alist (alist)
  (declare (xargs :guard (rule-alistp alist)
                  :verify-guards nil ;done below
                  ))
  (if (endp alist)
      nil
    (let* ((entry (first alist))
;           (fn (car entry))
           (stored-rules (cdr entry)))
      (union-eq (rules-from-stored-axe-rules stored-rules)
                (rules-from-rule-alist (rest alist))))))

(defthm symbol-listp-of-rules-from-rule-alist
  (implies (rule-alistp alist)
           (symbol-listp (rules-from-rule-alist alist)))
  :hints (("Goal" :in-theory (enable rules-from-rule-alist
                                     rule-alistp))))

(verify-guards rules-from-rule-alist
  :hints (("Goal" :in-theory (enable rule-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;makes an alist where each entry pairs a function symbol with a list of axe-rules that apply to that function.
;(All rules must have a topmost function symbol; the LHS of a rule can't be a constant or variable).
;the alist returned may have many entries for each function symbol, but we remove the shadowed entries in the caller
;if remove-duplicate-rulesp is non-nil we ensure that two rules with the same name are never added (we don't check for rules that are the same except for the name)
;;ffixme might be faster to do duplicate checking at the end (or while sorting!)...
;; todo: optimize by using a property-list world?
(defund extend-unprioritized-rule-alist (axe-rules remove-duplicate-rulesp rule-alist)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              (rule-alistp rule-alist))
                  :guard-hints (("Goal" :expand ((axe-rule-listp axe-rules)
                                                 (axe-rulep (car axe-rules)))))))
  (if (endp axe-rules)
      rule-alist
    (let* ((rule (first axe-rules))
           (lhs (rule-lhs rule))
           (fn (ffn-symb lhs))
           (stored-rules-for-fn (get-rules-for-fn fn rule-alist)) ;may be slow?
           (new-stored-rules-for-fn (if (and remove-duplicate-rulesp
                                             (rule-is-presentp (rule-symbol rule) stored-rules-for-fn))
                                        ;;already there:
                                        stored-rules-for-fn
                                      ;;not already there (or we are not checking):
                                      ;;ffixme, could use priorities and insert the rule in sorted order (faster to merge sort at the end?)
                                      (cons (make-stored-rule (fargs lhs) (rule-hyps rule) (rule-symbol rule) (rule-rhs rule))
                                            stored-rules-for-fn))))
      (extend-unprioritized-rule-alist (rest axe-rules)
                                     remove-duplicate-rulesp
                                     (acons-fast ;-unique       ;;now we uniquify the alist at the end
                                      fn new-stored-rules-for-fn rule-alist)))))

(defthm symbol-alistp-of-extend-unprioritized-rule-alist
  (implies (and (symbol-alistp acc)
                (axe-rule-listp axe-rules))
           (symbol-alistp (extend-unprioritized-rule-alist axe-rules remove-duplicate-rulesp acc)))
  :hints (("Goal" :in-theory (enable extend-unprioritized-rule-alist axe-rulep ;yuck
                                     ))))

(defthm rule-alistp-of-extend-unprioritized-rule-alist
  (implies (and (rule-alistp acc)
                (axe-rule-listp axe-rules))
           (rule-alistp (extend-unprioritized-rule-alist axe-rules remove-duplicate-rulesp acc)))
  :hints (("Goal"
           :expand ((axe-rulep (car axe-rules))
                    (axe-rule-listp axe-rules))
           :in-theory (enable rule-alistp extend-unprioritized-rule-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Would it make sense to sort the fns also (e.g., by frequency of occurrence)?
(defund sort-rules-for-each-function-symbol-by-priority (rule-alist priorities)
  (declare (xargs :guard (and (alistp priorities)
                              (rule-alistp rule-alist))
                  :verify-guards nil ;done below
                  ))
  (if (endp rule-alist)
      nil
    (let* ((entry (first rule-alist))
           (fn (car entry))
           (stored-rules (cdr entry)))
      (acons fn
             ;; TODO: Perhaps optimize if none of the rules have priorities (but that might change existing orderings)?:
             (merge-sort-by-rule-priority stored-rules priorities)
             (sort-rules-for-each-function-symbol-by-priority (rest rule-alist) priorities)))))

(defthm alistp-of-sort-rules-for-each-function-symbol-by-priority
  (implies (alistp rule-alist)
           (alistp (sort-rules-for-each-function-symbol-by-priority rule-alist priorities)))
  :hints (("Goal" :in-theory (enable  sort-rules-for-each-function-symbol-by-priority))))

(verify-guards sort-rules-for-each-function-symbol-by-priority
  :hints (("Goal" :in-theory (enable rule-alistp  rule-alistp-means-alistp))))

(defthm rule-alistp-of-sort-rules-for-each-function-symbol-by-priority
  (implies (rule-alistp rule-alist)
           (rule-alistp (sort-rules-for-each-function-symbol-by-priority rule-alist priorities)))
  :hints (("Goal" :in-theory (enable sort-rules-for-each-function-symbol-by-priority
                                     rule-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;speed this up when just adding a few rules?
(defund extend-rule-alist (axe-rules remove-duplicate-rulesp priorities rule-alist)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              ; (booleanp remove-duplicate-rulesp)
                              (alistp priorities)
                              (rule-alistp rule-alist))))
  (let* ((rule-alist (extend-unprioritized-rule-alist axe-rules remove-duplicate-rulesp rule-alist))
         (rule-alist (uniquify-alist-eq rule-alist))
         (rule-alist (if priorities
                         (sort-rules-for-each-function-symbol-by-priority rule-alist priorities)
                       rule-alist)))
    rule-alist))

(defthm rule-alistp-of-extend-rule-alist
  (implies (and (rule-alistp rule-alist)
                (alistp priorities)
                (axe-rule-listp axe-rules))
           (rule-alistp (extend-rule-alist axe-rules remove-duplicate-rulesp priorities rule-alist)))
  :hints (("Goal" :in-theory (enable extend-rule-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Makes a rule-alist from the given axe-rules (not that these are full axe-rules,
;; not rule-names).  TODO: Might be faster to first sort the rules by head
;; symbol, then remove dups, then use the fact that rules for the same symbol
;; are grouped together.
(defund make-rule-alist-simple (axe-rules remove-duplicate-rulesp priorities)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              (alistp priorities))))
  (extend-rule-alist axe-rules remove-duplicate-rulesp priorities (empty-rule-alist)))

(defthm rule-alistp-of-make-rule-alist-simple
  (implies (and (axe-rule-listp axe-rules)
                (alistp priorities))
           (rule-alistp (make-rule-alist-simple axe-rules remove-duplicate-rulesp priorities)))
  :hints (("Goal" :in-theory (enable make-rule-alist-simple))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Makes a rule-alist from the given RULE-NAMES, using priority information from WRLD.
;; Returns (mv erp rule-alist).
;todo: optimize this routine to not make the rules first
(defund make-rule-alist (rule-names wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (ilks-plist-worldp wrld))))
  (b* (((mv erp axe-rules) (make-axe-rules rule-names wrld))
       ((when erp) (mv erp nil))
       (priorities (table-alist 'axe-rule-priorities-table wrld))
       )
    (if (not (alistp priorities))
        (prog2$ (er hard? 'make-rule-alist "Ill-formed priorities table.")
                (mv :bad-priorities-table nil))
      (mv (erp-nil)
          (make-rule-alist-simple axe-rules t priorities)))))

(defthm rule-alistp-of-mv-nth-1-of-make-rule-alist
  (implies (symbol-listp rule-names)
           (rule-alistp (mv-nth 1 (make-rule-alist rule-names wrld))))
  :hints (("Goal" :in-theory (enable make-rule-alist
                                     axe-rule-listp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a rule-alist.  Can throw an error but doesn't return erp.
(defund make-rule-alist! (rule-names wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (ilks-plist-worldp wrld))))
  (mv-let (erp rule-alist)
    (make-rule-alist rule-names wrld)
    (if erp
        (er hard? 'make-rule-alist! "Error making rule alist.")
      rule-alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rule-alist).
(defund add-to-rule-alist (rule-names rule-alist wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (rule-alistp rule-alist)
                              (ilks-plist-worldp wrld))))
  (b* (((mv erp axe-rules) (make-axe-rules rule-names wrld))
       ((when erp) (mv erp nil))
       (priorities (table-alist 'axe-rule-priorities-table wrld)))
    (if (not (alistp priorities))
        (prog2$ (er hard? 'add-to-rule-alist "Ill-formed priorities table.")
                (mv :bad-priorities-table nil))
      (mv (erp-nil)
          (extend-rule-alist axe-rules t priorities rule-alist)))))

(defthm rule-alistp-of-mv-nth-1-of-add-to-rule-alist
  (implies (and (symbol-listp rule-names)
                (rule-alistp rule-alist)
                (ilks-plist-worldp wrld))
           (rule-alistp (mv-nth 1 (add-to-rule-alist rule-names rule-alist wrld))))
  :hints (("Goal" :in-theory (enable add-to-rule-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns the rule-alist.  Does not return erp.
(defund add-to-rule-alist! (rule-names rule-alist wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (rule-alistp rule-alist)
                              (ilks-plist-worldp wrld))))
  (mv-let (erp rule-alist)
    (add-to-rule-alist rule-names rule-alist wrld)
    (if erp
        (er hard? 'add-to-rule-alist! "Error adding to rule alist.")
      rule-alist)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; This is for the special case when the AXE-RULES do not correspond to theorems in the world.
;todo: would prefer to just pass in named formulas here
(defund extend-rule-alist2 (axe-rules rule-alist wrld)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              (rule-alistp rule-alist)
                              (plist-worldp wrld))))
  (let ((priorities (table-alist 'axe-rule-priorities-table wrld)))
    (if (not (alistp priorities))
        (er hard? 'extend-rule-alist2 "Ill-formed priorities table.")
      (extend-rule-alist axe-rules t priorities rule-alist))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; TODO: Optimize to not re-cons if not needed.
(defund remove-from-rule-alist (rule-names rule-alist)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (rule-alistp rule-alist))
                  :verify-guards nil ;done below
                  ))
  (if (endp rule-alist)
      nil
    (let* ((entry (car rule-alist))
           (fn (car entry))
           (stored-rules (cdr entry)))
      (acons fn
             (remove-from-stored-rules rule-names stored-rules)
             (remove-from-rule-alist rule-names (rest rule-alist))))))

(defthm rule-alistp-of-remove-from-rule-alist
  (implies (rule-alistp rule-alist)
           (rule-alistp (remove-from-rule-alist rule-names rule-alist)))
  :hints (("Goal" :in-theory (enable remove-from-rule-alist rule-alistp))))

(verify-guards remove-from-rule-alist
  :hints (("Goal" :in-theory (enable stored-axe-rule-listp
                                     stored-axe-rulep
                                     rule-alistp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;
;;; all-rule-alistp
;;;

(defforall-simple rule-alistp) ; todo: simplify?
(verify-guards all-rule-alistp)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of rule-names.
;; Warning: If any of these rules have :rule-classes nil, ACL2 won't allow us to use them.
(defund rules-from-rule-alists (alists)
  (declare (xargs :guard (and (all-rule-alistp alists)
                              (true-listp alists))))
  (if (endp alists)
      nil
    (union-eq (rules-from-rule-alist (first alists))
              (rules-from-rule-alists (rest alists)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Only used in once, in equivalence checker.
(defund make-rule-alists-simple (rule-sets remove-duplicate-rulesp priorities)
  (declare (xargs :guard (and (axe-rule-setsp rule-sets)
                              (alistp priorities)
                              (booleanp remove-duplicate-rulesp))))
  (if (endp rule-sets)
      nil
    (cons (make-rule-alist-simple (first rule-sets) remove-duplicate-rulesp priorities)
          (make-rule-alists-simple (rest rule-sets) remove-duplicate-rulesp priorities))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rule-alists).
(defund make-rule-alists (rule-name-lists wrld)
  (declare (xargs :guard (and (symbol-list-listp rule-name-lists)
                              (ilks-plist-worldp wrld))))
  (if (endp rule-name-lists)
      (mv (erp-nil) nil)
    (b* (((mv erp rule-alist)
          (make-rule-alist (first rule-name-lists) wrld))
         ((when erp) (mv erp nil))
         ((mv erp rule-alists)
          (make-rule-alists (rest rule-name-lists) wrld))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (cons rule-alist rule-alists)))))

(defthm true-listp-of-mv-nth-1-of-make-rule-alists
  (true-listp (mv-nth 1 (make-rule-alists rule-name-lists wrld)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable make-rule-alists))))

(defthm all-rule-alistp-of-mv-nth-1-of-make-rule-alists
  (implies (symbol-list-listp rule-name-lists)
           (all-rule-alistp (mv-nth 1 (make-rule-alists rule-name-lists wrld))))
  :hints (("Goal" :in-theory (enable make-rule-alists))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: would prefer to just pass in named formulas here
(defund extend-rule-alists2 (axe-rules rule-alists wrld)
  (declare (xargs :guard (and (axe-rule-listp axe-rules)
                              (all-rule-alistp rule-alists)
                              (true-listp rule-alists)
                              (plist-worldp wrld))))
  (if (endp rule-alists)
      nil
    (cons (extend-rule-alist2 axe-rules (first rule-alists) wrld)
          (extend-rule-alists2 axe-rules (rest rule-alists) wrld))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv erp rule-alists).
(defund add-to-rule-alists (rule-names rule-alists wrld)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (all-rule-alistp rule-alists)
                              (true-listp rule-alists)
                              (ilks-plist-worldp wrld))))
  (if (endp rule-alists)
      (mv (erp-nil) nil)
    (b* (((mv erp rule-alist)
          (add-to-rule-alist rule-names (first rule-alists) wrld))
         ((when erp) (mv erp nil))
         ((mv erp rule-alists)
          (add-to-rule-alists rule-names (rest rule-alists) wrld))
         ((when erp) (mv erp nil)))
      (mv (erp-nil)
          (cons rule-alist rule-alists)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund remove-from-rule-alists (rule-names rule-alists)
  (declare (xargs :guard (and (symbol-listp rule-names)
                              (all-rule-alistp rule-alists)
                              (true-listp rule-alists))))
  (if (endp rule-alists)
      nil
    (cons (remove-from-rule-alist rule-names (first rule-alists))
          (remove-from-rule-alists rule-names (rest rule-alists)))))

(defthm symbol-listp-of-rules-from-rule-alists
  (implies (all-rule-alistp alists)
           (symbol-listp (rules-from-rule-alists alists)))
  :hints (("Goal" :in-theory (enable rules-from-rule-alists))))
