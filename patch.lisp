(in-package "ACL2")

#|
; dag - LP support
(verify-termination arith-term-order)

; dag
(defrec zeros (originals . zvectors) t)

; dag
(defrec pstat (sln zeros plist) t)

(defun dag-self-dot-alist (alist1 dot)
  (if (not (consp alist1)) dot
    (dag-self-dot-alist (cdr alist1) (+ (* (cdar alist1) (cdar alist1)) dot))))

(defun dag-self-dot (vector)
  (dag-self-dot-alist (access poly vector :alist) 0))

(defun dag-dot-alist (alist1 alist2 dot)
  (declare (xargs :measure (+ (len alist1) (len alist2))))
  (cond
   ((not (consp alist1))
    dot)
   ((not (consp alist2)) 
    dot)
   ((not (arith-term-order (caar alist1) (caar alist2)))
    (dag-dot-alist (cdr alist1) alist2 dot))
   ((equal (caar alist1) (caar alist2))
    (let ((dot (+ dot (* (cdar alist1) (cdar alist2)))))
      (dag-dot-alist (cdr alist1) (cdr alist2) dot)))
   (t
    (dag-dot-alist alist1 (cdr alist2) dot))))

(defun dag-scale-alist (alist coeff)
  (if (not (consp alist)) nil
    (cons (cons (caar alist) (* coeff (cdar alist)))
          (dag-scale-alist (cdr alist) coeff))))

(defun dag-scale-and-add-alists (alist1 alist2 coeff)
  (declare (xargs :measure (+ (len alist1) (len alist2))))
  (cond
   ((not (consp alist1))
    (dag-scale-alist alist2 coeff))
   ((not (consp alist2)) 
    alist1)
   ((not (arith-term-order (caar alist1) (caar alist2)))
    (cons (car alist1) (dag-scale-and-add-alists (cdr alist1) alist2 coeff)))
   ((equal (caar alist1) (caar alist2))
    (let ((value (+ (cdar alist1) (* coeff (cdar alist2)))))
      (if (= value 0) 
          (dag-scale-and-add-alists (cdr alist1) (cdr alist2) coeff)
        (cons (cons (caar alist1) value)
              (dag-scale-and-add-alists (cdr alist1) (cdr alist2) coeff)))))
   (t
    (cons (car alist2) (dag-scale-and-add-alists alist1 (cdr alist2) coeff)))))

(defun dag-dot-vectors (v1 v2)
  (dag-dot-alist (access poly v1 :alist) (access poly v2 :alist) 0))

(defun dag-scale-and-add-vector-to-sln (alist vector coeff)
  (dag-scale-and-add-alists alist (access poly vector :alist) coeff))

(defun dag-scale-and-add-vectors (v1 v2 coeff)
  (let* ((alist1  (access poly v1 :alist))
         (alist2  (access poly v2 :alist)))
    (make poly
          :constant 0
          :alist (dag-scale-and-add-alists alist1 alist2 coeff)
          :relation  (if (or (eq (access poly v1 :relation) '<)
                             (eq (access poly v2 :relation) '<))
                         '<
                       '<=)
          :ttree (cons-tag-trees (access poly v1 :ttree)
                                 (access poly v2 :ttree))
          :rational-poly-p (and (access poly v1 :rational-poly-p)
                                (access poly v2 :rational-poly-p))
          :parents (marry-parents (access poly v1 :parents)
                                  (access poly v2 :parents))
          :derived-from-not-equalityp nil)))

(defun dag-score-poly (poly pstat)
  (dag-dot-alist (access poly poly :alist) (access pstat pstat :sln) (access poly poly :constant)))

(defun dag-score-list1 (kind list ref plist zlist nlist)
  (if (not (consp list)) (mv plist zlist nlist)
    (let ((poly (car list)))
      (let ((score (dag-dot-alist (access poly poly :alist) ref (if (eq kind :polys) (access poly poly :constant) 0))))
        (cond
         ((< 0 score) (dag-score-list1 kind (cdr list) ref (cons poly plist) zlist nlist))
         ((= 0 score) (dag-score-list1 kind (cdr list) ref plist (cons poly zlist) nlist))
         (t           (dag-score-list1 kind (cdr list) ref plist zlist (cons poly nlist))))))))

(defun dag-score-list (kind list ref plist zlist nlist)
  (dag-score-list1 kind list ref plist zlist nlist))

(defun dag-poly-to-vector (poly)
  (change poly poly :constant 0))

(defun dag-remove-negative-zvectors-from-vector1 (zvectors vector)
  (if (not (consp zvectors)) vector
    (let ((zref (car zvectors)))
      (let ((dot (dag-dot-vectors zref vector)))
        (if (<= 0 dot) (dag-remove-negative-zvectors-from-vector1 (cdr zvectors) vector)
          (let ((coeff (/ (- dot) (dag-self-dot zref))))
            ;; zref * (vector + coeff*zref) = 0
            ;; zref*vector + coeff*zref^2 = 0
            ;; coeff= (- (vector*zref))/(zref^2)
            ;; coeff = (- dot)/(zref^2)
            (let ((vector (dag-scale-and-add-vectors vector zref coeff)))
              (dag-remove-negative-zvectors-from-vector1 (cdr zvectors) vector))))))))

(defun dag-remove-negative-zvectors-from-vector (zvectors vector)
  (dag-remove-negative-zvectors-from-vector1 zvectors vector))

(defun dag-remove-zvectors-from-vector1 (zvectors vector)
  (if (not (consp zvectors)) vector
    (let ((zref (car zvectors)))
      (let ((dot (dag-dot-vectors zref vector)))
        (if (= 0 dot) (dag-remove-zvectors-from-vector1 (cdr zvectors) vector)
          (let ((coeff (/ (- dot) (dag-self-dot zref))))
            ;; zref * (vector + coeff*zref) = 0
            ;; zref*vector + coeff*zref^2 = 0
            ;; coeff= (- (vector*zref))/(zref^2)
            ;; coeff = (- dot)/1.0
            (let ((vector (dag-scale-and-add-vectors vector zref coeff)))
              (dag-remove-zvectors-from-vector1 (cdr zvectors) vector))))))))

(defun dag-remove-zvectors-from-vector (zvectors vector)
  (dag-remove-zvectors-from-vector1 zvectors vector))

(defun dag-zero-vectorp (vector)
  (= (len (access poly vector :alist)) 0))

(defun dag-insert-positive-poly (score poly plist)
  (declare (ignore score))
  (cons poly plist))

(defun dag-insert-zero-poly (poly zeros)
  (let ((originals (access zeros zeros :originals))
        (zvectors    (access zeros zeros :zvectors)))
    (let ((vector (dag-poly-to-vector poly)))
      (let ((vector (dag-remove-zvectors-from-vector zvectors vector)))
        ;; Yeah .. so this would happen if any motion on the
        ;; vector would violate the existing zvectors.
        (if (dag-zero-vectorp vector) (change zeros zeros :originals (cons poly originals))
          (make zeros 
                :originals (cons poly originals)
                :zvectors    (cons vector zvectors)))))))

(defun dag-insert-zero-poly-list (list zeros)
  (if (not (consp list)) zeros
    (dag-insert-zero-poly-list (cdr list) (dag-insert-zero-poly (car list) zeros))))

(defun dag-unexpected (term)
  (declare (ignorable term))
  nil)

(defun dag-insert-negative-poly (score poly pstat)
  (let ((zeros (access pstat pstat :zeros))
        (plist (access pstat pstat :plist))
        (sln   (access pstat pstat :sln)))
    (let ((originals (access zeros zeros :originals))
          (zvectors  (access zeros zeros :zvectors)))
      (let ((vector (dag-poly-to-vector poly)))
        ;; poly's score is currently negative.  We need to move the solution vector
        ;; in the direction of poly's vector to try to make it positive.  When we
        ;; do so, however, we are going to disrupt the current zero vector set.
        ;; If we score the zvectors w/to poly's vector we see 3 results:
        ;; - pzvectors: after the move, these will be positive.
        ;; - zzvectors: these will remain unchanged
        ;; - nzvectors: these would become negative .. but we cannot allow that
        ;;              to happen .. so we remove these vectors from poly's vector.
        ;; Note: the zvectors are orthoganal.
        (mv-let (pzvectors zzvectors nzvectors) (dag-score-list :vectors zvectors (access poly vector :alist) nil nil nil)
          ;; Remove from vector all the negative components
          (let ((vector (dag-remove-negative-zvectors-from-vector nzvectors vector)))
            ;; After the move, this will be our new set of zero vectors
            (let ((zvectors (revappend zzvectors nzvectors)))
              ;; Oops .. this is a contradiction .. we need to change
              ;; the solution but our nzvectors will not allow it ..
              ;; so we are done.
              (if (dag-zero-vectorp vector) (mv vector nil pstat)
                (mv-let (new-plist originals empty) (dag-score-list :vectors originals (access poly vector :alist) pzvectors nil nil)
                  ;; This test should never succeed ..
                  (if (consp empty) 
                      (let ((irrelevant (dag-log-form (list "unexpected" score poly pstat))))
                        (declare (ignore irrelevant))
                        (mv nil nil pstat))
                    ;; (poly * (sln + coeff*vector)) = poly*sln + coeff*poly*vector = 0 
                    ;; coeff = (- poly*sln)/(poly*vector) 
                    ;;       = (- score)/vector^2
                    (let ((coeff (/ (- score) (dag-self-dot vector))))
                      (let ((sln (dag-scale-and-add-vector-to-sln sln vector coeff)))
                        (mv-let (plist zlist0 nlist) (dag-score-list :vectors plist (access poly vector :alist) new-plist nil nil)
                          (mv-let (plist zlist nlist) (dag-score-list :polys nlist sln plist nil nil)
                            (let ((plist (revappend zlist0 plist))) 
                              (let ((zeros (make zeros 
                                                 :originals (cons poly originals)
                                                 :zvectors    (cons vector zvectors))))
                                (let ((zeros (dag-insert-zero-poly-list zlist zeros)))
                                  (let ((pstat (make pstat
                                                     :sln   sln
                                                     :zeros zeros
                                                     :plist plist)))
                                    (mv nil nlist pstat)))))))))))))))))))

(defun dag-add-poly (poly pstat)
  (let ((score (dag-score-poly poly pstat)))
    (if (< 0 score) (mv nil nil (change pstat pstat :plist (dag-insert-positive-poly score poly (access pstat pstat :plist))))
      (if (= 0 score) (mv nil nil (change pstat pstat :zeros (dag-insert-zero-poly poly (access pstat pstat :zeros))))
        (dag-insert-negative-poly score poly pstat)))))

(defun dag-add-poly-list (polys pstat)
  (declare (xargs :mode :program))
  (if (not (consp polys)) (mv nil pstat)
    (mv-let (unsat new-polys pstat) (dag-add-poly (car polys) pstat)
      (if (not unsat) (dag-add-poly-list (revappend new-polys (cdr polys)) pstat)
        (mv unsat pstat)))))

(defun dag-new-zeros ()
  (make zeros
        :originals nil
        :zvectors nil))

(defun dag-new-pstat ()
  (make pstat
        :sln nil
        :zeros (dag-new-zeros)
        :plist nil))

(defun dag-add-linear-pot (pot-lst pstat)
  (declare (xargs :mode :program))
  (if (not (consp pot-lst)) (mv nil pstat)
    (let ((pot (car pot-lst)))
      (mv-let (unsat pstat) (dag-add-poly-list (access linear-pot pot :negatives) pstat)
        (if unsat (mv unsat pstat)
          (mv-let (unsat pstat) (dag-add-poly-list (access linear-pot pot :positives) pstat)
            (if unsat (mv unsat pstat)
              (dag-add-linear-pot (cdr pot-lst) pstat))))))))

(defun dag-add-strict-vectors (vectors vres)
  (if (not (consp vectors)) vres
    (let ((vector (car vectors)))
      (let ((vres (if (eq (access poly vector :relation) '<)
                      (dag-scale-and-add-vectors vres vector 1)
                    vres)))
        (dag-add-strict-vectors (cdr vectors) vres)))))

(defun dag-epsilon-unsat (pstat)
  ;;
  ;; We scan the list of zero vectors and find the ones that are strict
  ;; inequalities.  We add them up (all of the vectors are orthoganal)
  ;; and then compoare (dot) them to the original poly .. if any are
  ;; negative ther is no "epsilon" coefficient that would allow us to
  ;; satisfy the strict inequalities.
  ;;
  ;; Note that disequalities (ie: (not (equal x y))), were they to be
  ;; made avaiable, could also be checked at this point:
  ;;
  ;; For each disequality that evaluates to false (zero) at the solution,
  ;; - Consider the inequalities (< 0 (+ x (- y))) and (< 0 (+ (- x) y))
  ;; - Reduce them by the zvector set
  ;; - If both are unsat, no epsilon coefficient exits.
  ;;
  (let ((zeros (access pstat pstat :zeros)))
    (let ((zvectors (access zeros zeros :zvectors)))
      (let ((strict-vector (dag-add-strict-vectors zvectors nil)))
        (let ((originals (access zeros zeros :originals)))
          (mv-let (plist zlist nlist) (dag-score-list :vectors originals (access poly strict-vector :alist) nil nil nil)
            (declare (ignore plist zlist))
            (if (not (consp nlist)) nil
              (dag-scale-and-add-vectors (car nlist) strict-vector 1))))))))

(defun dag-add-polys1 (lst pot-lst)
  (mv-let (unsat pstat) (dag-add-linear-pot pot-lst (dag-new-pstat))
          (or unsat
              (mv-let (unsat pstat) (dag-add-poly-list lst pstat)
                      (or unsat
                          (dag-epsilon-unsat pstat))))))

|#

(defttag :lp)
:redef!

(defun add-polys0 (lst pot-lst pt nonlinearp max-rounds)
  (declare (xargs :mode :program))
; Lst is a list of polys.  We filter out the true ones (and detect any
; impossible ones) and then normalize and add the rest to pot-lst.
; Any new polys thereby produced are also added until there's nothing
; left to do.  We return the standard contradictionp and a new pot-lst.
  (mv-let (contradictionp lst) (filter-polys lst nil)
    (cond 
     (contradictionp (mv contradictionp nil))
     (t
      (let ((unsat (dag-add-polys1 lst pot-lst)))
        (mv-let (contradictionp lst) (add-polys1 lst pot-lst nil pt nonlinearp max-rounds 0)
          (let ((zed (cond
                      ((and unsat (not contradictionp))
                       (dag-log-form (list "unsound" lst pot-lst)))
                      ((and (not unsat) contradictionp)
                       (dag-log-form (list "incomplete" lst pot-lst)))
                      (t nil))))
            (declare (ignore zed))
            (mv contradictionp lst))))))))
  
#+joe
(defun log-event (form)
  (declare (ignorable form))
  #+acl2-loop-only
  (with-open-file (logfile "/home/dagreve/git/acl2/dag.log" :direction :output :if-does-not-exist :create :if-exists :append)
    (pprint form logfile))
  nil)


;;(include-book "finite-set-theory/total-ordering" :dir :system)
;;(include-book "coi/util/mv-nth" :dir :system)
(ld "tracing.lisp")

;; This is a linear routine built on top of the ACL2 poly
;; representation.

;; pstat holds the status of the current polys.
;; It consists of a rational valued solution vector and
;; sets of polys sorted by their satisfaction score.
;; 
;; Conceptually, polys represent formula of the form:
;;
;; (<= 0 poly)
;;
;; The satisfaction score is simply the result of evaluating
;; the poly relative to the solution vector.  If this result
;; (the score) is positive, the poly is true at the solution.  
;; If the score is negative, the poly is false at the solution.
;;
;; NOTE: If the score is zero, we say that the solution "satisfies"
;; the poly -- but once the pot is stable we check for 'epsilon
;; satisfiability' in which we verfify that there exists a rational
;; assignment some non-zero distance (epsilon) from the current
;; solution that would satisfy the strict inequality.

(set-state-ok t)

(defun show-vector (vector state)
  (declare (xargs :mode :program))
  (untranslate (poly-to-expr vector) nil (w state)))

(defun show-vector-list (list state)
  (declare (xargs :mode :program))
  (untranslate `(list ,@(poly-term-lst list)) nil (w state)))

(defun show-zeros (zeros state)
  (declare (xargs :mode :program))
  (let ((originals (access zeros zeros :originals))
        (zvectors  (access zeros zeros :zvectors)))
    `(zeros
      ,(untranslate `(:originals
                      ,@(poly-term-lst originals)
                      ) nil (w state))
      ,(untranslate `(:zvectors
                      ,@(poly-term-lst zvectors)
                      ) nil (w state))
      )))
    
(defun show-plist (plist state)
  (declare (xargs :mode :program))
  (untranslate `(:plist ,@(poly-term-lst plist)) nil (w state)))

(defun show-pstat (pstat state)
  (declare (xargs :mode :program))
  (let ((zeros (access pstat pstat :zeros))
        (plist (access pstat pstat :plist))
        (sln   (access pstat pstat :sln)))
      `(pstat
        (:sln ,sln)
        ,(show-zeros zeros state)
        ,(show-plist plist state)
        )))

#+joe
(trace$ dot-alist)

#+joe
(trace$ (dot-vectors
         :entry `(dot-vectors ,(show-vector v1 state)
                              ,(show-vector v2 state))
         :exit  `(dot-vectors ,(nth 0 values))))

#+joe
(trace$ (score-list 
         :entry `(score-list ,kind 
                             ,(show-vector-list list state) 
                             ,ref 
                             :plist ,(show-vector-list plist state) 
                             :zlist ,(show-vector-list zlist state)
                             :nlist ,(show-vector-list nlist state))
         :exit `(score-list :plist ,(show-vector-list (nth 0 values) state)
                            :zlist ,(show-vector-list (nth 1 values) state)
                            :nlist ,(show-vector-list (nth 2 values) state))))

#+joe
(trace$ (remove-negative-zvectors-from-vector1
         :entry `(remove-negative-zvectors-from-vector1 ,(show-vector-list zvectors state) ,(show-vector vector state))
         :exit  `(remove-negative-zvectors-from-vector1 ,(show-vector (nth 0 values) state))
         ))

#+joe
(trace$ (remove-negative-zvectors-from-vector 
         :entry `(remove-negative-zvectors-from-vector ,(show-vector-list zvectors state) ,(show-vector vector state))
         :exit  `(remove-negative-zvectors-from-vector ,(show-vector (nth 0 values) state))
         ))

#+joe
(trace$ (remove-zvectors-from-vector 
         :entry `(remove-zvectors-from-vector ,(show-vector-list zvectors state) ,(show-vector vector state))
         :exit  `(remove-zvectors-from-vector ,(show-vector (nth 0 values) state))
         ))

#+joe
(trace$ (zero-vectorp
         :entry `(zero-vectorp ,(show-vector vector state))
         :exit  `(zero-vectorp ,(nth 0 values))))

#+joe
(trace$ (dag-insert-positive-poly
         :entry `(dag-insert-positive-poly ,score ,(show-vector poly state) ,(show-pstat pstat state))
         :exit  `(dag-insert-positive-poly ,(show-pstat (nth 0 values) state))
         ))

#+joe
(trace$ (dag-insert-zero-poly
         :entry `(dag-insert-zero-poly ,score ,(show-vector poly state) ,(show-pstat pstat state))
         :exit  `(dag-insert-zero-poly ,(show-pstat (nth 0 values) state))
         ))

#+joe
(trace$ (dag-insert-negative-poly
         :entry `(dag-insert-negative-poly ,score ,(show-vector poly state) ,(show-pstat pstat state))
         :exit  `(dag-insert-negative-poly ,(nth 0 values) 
                                           ,(show-vector-list (nth 1 values) state)
                                           ,(show-pstat (nth 2 values) state))
         ))

;; zeros contains two lists:
;; - original polys
;; - basis polys (derived)

#+joe
(trace$ (add-strict-vectors
         :entry `(add-strict-vectors ,(show-vector-list vectors state))
         :exit  `(add-strict-vectors ,(show-vector (nth 0 values) state))))

#+joe
(trace$ (epsilon-unsat
         :entry `(epsilon-unsat ,(show-pstat pstat state))
         :exit  (if (nth 0 values) `(epsilon-unsat ,(show-vector (nth 0 values) state))
                  `(epsilon-unsat ,(nth 0 values)))))

#+joe
(trace$ (scale-and-add-vectors
         :entry `(scale-and-add-vectors ,(show-vector v1 state) ,(show-vector v2 state) ,coeff)
         :exit  `(scale-and-add-vectors ,(show-vector (nth 0 values)))
         ))


#+joe
(thm
   (implies
    (and
     (acl2-numberp x)
     (acl2-numberp y)
     (< 0 (+ x y     -2))
     (< 0 (+ (- x) y -4))
     )
    nil)
   )

#+joe
(defthm test-zero-poly
   (implies
    (and
     (acl2-numberp x)
     (acl2-numberp y)
     (< 0 (+ x y))
     (< 0 (+ (- x) y))
     (< 0 (+ (- y) -2))
     )
    nil)
  :rule-classes nil)

#+joe
(defthm test-epsilon-unsat
  (implies
   (and
    (acl2-numberp x)
    (acl2-numberp y)
    (< 0 (+ x y))
    (< 0 (+ (- x) y))
    (< 0 (- y))
    )
   nil)
  :rule-classes nil)

#+joe
(trace$ (DAG-ADD-POLYS1
         :entry `(DAG-ADD-POLYS1 ,(show-vector-list lst state) ,(untranslate `(poly-pot ,@(poly-pot-list pot-lst)) nil (w state)))
         :exit  `(DAG-ADD-POLYS1 ,(show-pstat (nth 0 values) state))
         ))

#+joe
(trace$ (DAG-ADD-POLY-LIST
         :entry `(DAG-ADD-POLY-LIST ,(show-vector-list polys state) ,(show-pstat pstat state))
         :exit  `(DAG-ADD-POLY-LIST ,(nth 0 values) ,(show-pstat (nth 1 values) state))
         ))

#+joe
(trace$ (DAG-ADD-POLY
         :entry `(DAG-ADD-POLY ,(show-vector poly state) ,(show-pstat pstat state))
         :exit  `(DAG-ADD-POLY ,(nth 0 values) 
                               ,(show-vector-list (nth 1 values) state)
                               ,(show-pstat (nth 2 values) state)
                               )
         ))

#+joe
(thm
 (IMPLIES (AND (< 0 J)
               (INTEGERP J)
               (<= 0 I)
               (INTEGERP I)
               (NOT (OR (EQUAL (NFIX J) 0) (< (IFIX I) J))))
          (<= 0 (+ I (- J))))
 )
