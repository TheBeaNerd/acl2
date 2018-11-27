(in-package "ACL2")

;; (defttag :lp)
;; :redef!

;; (defun add-polys0 (lst pot-lst pt nonlinearp max-rounds)
;;   (declare (xargs :mode :program))
;;   (dag-add-polys0 lst pot-lst pt nonlinearp max-rounds))

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

(defun show-zlist (zlist state)
  (declare (xargs :mode :program))
  (untranslate `(:zlist ,@(poly-term-lst zlist)) nil (w state)))
 
(defun show-plist (plist state)
  (declare (xargs :mode :program))
  (untranslate `(:plist ,@(poly-term-lst plist)) nil (w state)))

(defun show-pstat (pstat state)
  (declare (xargs :mode :program))
  (let ((zlist (access pstat pstat :zlist))
        (plist (access pstat pstat :plist))
        (sln   (access pstat pstat :sln)))
      `(pstat
        (:sln ,sln)
        ,(show-zlist zlist state)
        ,(show-plist plist state)
        )))

#+joe
(trace$ dot-alist)

;;#+joe
(trace$ (dag-dot-vectors
         :entry `(dag-dot-vectors ,(show-vector v1 state)
                                  ,(show-vector v2 state))
         :exit  `(dag-dot-vectors ,(nth 0 values))))

#+joe
(trace$ (dag-score-list 
         :entry `(dag-score-list ,kind 
                                 ,(show-vector-list list state) 
                                 ,ref 
                                 :plist ,(show-vector-list plist state) 
                                 :zlist ,(show-vector-list zlist state)
                                 :nlist ,(show-vector-list nlist state))
         :exit `(dag-score-list :plist ,(show-vector-list (nth 0 values) state)
                                :zlist ,(show-vector-list (nth 1 values) state)
                                :nlist ,(show-vector-list (nth 2 values) state))))

#+joe
(trace$ (remove-negative-zvectors-from-vector1
         :entry `(remove-negative-zvectors-from-vector1 ,(show-vector-list zvectors state) ,(show-vector vector state))
         :exit  `(remove-negative-zvectors-from-vector1 ,(show-vector (nth 0 values) state))
         ))

;;#+joe
(trace$ (dag-remove-opposing-zvectors-from-vector 
         :entry `(dag-remove-opposing-zvectors-from-vector ,(show-vector-list zvectors state) ,(show-vector vector state))
         :exit  `(dag-remove-opposing-zvectors-from-vector ,(show-vector (nth 0 values) state))
         ))

;;#+joe
(trace$ (dag-zero-vectorp
         :entry `(dag-zero-vectorp ,(show-vector vector state))
         :exit  `(dag-zero-vectorp ,(nth 0 values))))

;;#+joe
(trace$ (dag-insert-positive-poly
         :entry `(dag-insert-positive-poly ,score ,(show-vector poly state) ,(show-pstat pstat state))
         :exit  `(dag-insert-positive-poly ,(show-pstat (nth 0 values) state))
         ))

;;#+joe
(trace$ (dag-insert-zero-poly
         :entry `(dag-insert-zero-poly ,(show-vector poly state) ,(show-pstat pstat state))
         :exit  `(dag-insert-zero-poly ,(show-pstat (nth 0 values) state))
         ))

;;#+joe
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

;;#+joe
(trace$ (dag-scale-and-add-vectors
         :entry `(dag-scale-and-add-vectors ,(show-vector v1 state) ,(show-vector v2 state) ,coeff)
         :exit  `(dag-scale-and-add-vectors ,(show-vector (nth 0 values) state))
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

(trace$ (dag-remove-zvectors-from-vector
         :entry `(dag-remove-zvectors-from-vector ,(show-vector-list zvectors state) ,(show-vector vector state))
         :exit  `(dag-remove-zvectors-from-vector ,(show-vector (nth 0 values) state))
         ))

;;#+joe
(trace$ (dag-remove-opposing-polys-from-vector
         :entry `(dag-remove-opposing-polys-from-vector ,(show-vector vector state) 
                                                        ,(show-vector-list xlist state)
                                                        ,(show-vector-list zbasis state)
                                                        ,(show-vector-list zlist state)
                                                        ,(show-vector-list nnlist state))
         :exit  `(dag-remove-opposing-polys-from-vector ,(nth 0 values)
                                                        ,(show-vector (nth 1 values) state)
                                                        ,(show-vector-list (nth 2 values) state)
                                                        ,(show-vector-list (nth 3 values) state)
                                                        ,(show-vector-list (nth 4 values) state))
         ))

#+joe
(trace$ (DAG-ADD-POLY-LIST
         :entry `(DAG-ADD-POLY-LIST ,(show-vector-list polys state) ,(show-pstat pstat state))
         :exit  `(DAG-ADD-POLY-LIST ,(nth 0 values) ,(show-pstat (nth 1 values) state))
         ))

;;#+joe
(trace$ (DAG-ADD-POLY
         :entry `(DAG-ADD-POLY ,(show-vector poly state) ,(show-pstat pstat state))
         :exit  `(DAG-ADD-POLY ,(nth 0 values) 
                               ,(show-vector-list (nth 1 values) state)
                               ,(show-pstat (nth 2 values) state)
                               )
         ))

;;#+joe
(trace$ (DAG-ADD-POLYS1
         :entry `(DAG-ADD-POLYS1 ,(show-vector-list lst state) ,(untranslate `(poly-pot ,@(poly-pot-list pot-lst)) nil (w state)))
         :exit  `(DAG-ADD-POLYS1 ,(nth 0 values))
         ))

;;#+joe
(trace$ (dag-check-pstat
         :entry `(dag-check-pstat ,(show-pstat pstat state))
         :exit  `(dag-check-pstat ,(nth 0 values))))

(trace$ (ignore-polyp
         :entry `(ignore-polyp)
         :exit  `(ignore-polyp ,(nth 0 values))))

;;#+joe
(trace$ (ADD-POLY
         :entry `(ACL2-ADD-POLY ,(show-vector p state) ,(untranslate `(poly-pot ,@(poly-pot-list pot-lst)) nil (w state)) ,incomplete)
         :exit  `(ACL2-ADD-POLY ,(nth 0 values)
                                ,(untranslate `(poly-pot ,@(poly-pot-list (nth 1 values))) nil (w state))
                                ,(show-vector-list (nth 2 values) state)
                                ,(nth 3 values)
                                )
         ))

;;#+joe
(trace$ (ADD-POLYS1
         :entry `(ACL2-ADD-POLYS1 ,(show-vector-list lst state) ,(untranslate `(poly-pot ,@(poly-pot-list pot-lst)) nil (w state)) ,incomplete)
         :exit  `(ACL2-ADD-POLYS1 ,(nth 0 values) ,(nth 2 values))
         ))

;;#+joe
(trace$ (dag-epsilon-unsat
         :entry `(dag-epsilon-unsat ,(show-pstat pstat state))
         :exit  `(dag-epsilon-unsat ,(nth 0 values))
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

#+joe
(thm
 (implies
  (and
   (acl2-numberp x)
   (acl2-numberp y)
   (< 0 (+ x -1))
   (< 0 (+ x -2))
   (< 0 (+ x -3))
   (< 0 (+ y -3))
   (< 0 (+ y -2))
   (< 0 (+ y -1))
   )
  nil))

(let ((unsat (DAG-ADD-POLYS1
              '((((((I . 1)) NIL) -1 <= T)))
              '(((0) I (((((I . 1)) NIL) 0 <= T)))
                ((0 (((((J . -1) (I . 1)) NIL) 0 <= T))
                    (((((J . -1)) NIL (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL))) 0 <=
                      T)))
                 J (((((J . 1)) NIL) 0 <= T)))))))
  (assert$ (not unsat) nil))

(let ((unsat (DAG-ADD-POLYS1
              '(((((((LEN SEQ1) . 1)) NIL (LEMMA (:TYPE-PRESCRIPTION LEN))) 0 <=
                  T)))
              '(((0) START2
                 (((((START2 . 1)) NIL
                    (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                           (:TYPE-PRESCRIPTION LEN)))
                   -1 <= T))
                 (((((START2 . 1)) NIL
                    (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                           (:TYPE-PRESCRIPTION LEN)))
                   0 <= T)))
                ((0
                  ((((((LEN SEQ1) . -1) (START2 . -1) (END2 . 1)) NIL
                     (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                            (:TYPE-PRESCRIPTION LEN)))
                    0 <= T))
                  ((((((LEN SEQ1) . -1)) NIL
                     (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                            (:TYPE-PRESCRIPTION LEN)))
                    -1 <= T)))
                 (LEN SEQ1))
                ((0) (LEN SEQ2)
                 ((((((LEN SEQ2) . 1) (END2 . -1)) NIL
                    (LEMMA (:TYPE-PRESCRIPTION LEN)))
                   0 <= T)))))))
  (assert$ unsat nil))

(let ((unsat (DAG-ADD-POLYS1
              '((((((Z . -1) (Y . 1)) NIL (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)))
                  0 <= T))
                (((((Z . 1) (Y . -1) (W . -1)) NIL
                   (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)))
                  0 < T))
                (((((W . 1)) NIL) 0 < T)) (((((Y . 1)) NIL) 0 < T)))
              'NIL)))
  (assert$ unsat nil))

#+unsound
(DAG-ADD-POLYS1
   '(((((((MOD (BINARY-+ X Y) Z) . 1)) NIL
        (LEMMA (:TYPE-PRESCRIPTION MOD-TYPE . 4)
         (:TYPE-PRESCRIPTION RATIONALP-MOD)
         (:FAKE-RUNE-FOR-TYPE-SET NIL)))
       0 <= T)))
   '(((0) X
      (((((X . 1)) NIL (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL))) 0 < T))
      (((((X . 1)) NIL) 0 <= T)))
     ((0) Y
      (((((Y . 1) (X . 1)) NIL (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)))
        0 < T))
      (((((Y . 1)) NIL (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL))) 0 < T))
      (((((Y . 1)) NIL) 0 <= T)))
     ((0
       (((((Z . -1) (Y . 1) (X . 1)) NIL
          (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)))
         0 <= T)))
      Z (((((Z . 1) (X . -1)) NIL) 0 < T))
      (((((Z . 1) (Y . -1)) NIL) 0 < T)) (((((Z . 1)) NIL) 0 < T)))
     ((0
       ((((((MOD (BINARY-+ X Y) Z) . -1) (Z . -1) (Y . 1) (X . 1))
          NIL
          (LEMMA (:TYPE-PRESCRIPTION MOD-TYPE . 4)
           (:TYPE-PRESCRIPTION RATIONALP-MOD)
           (:FAKE-RUNE-FOR-TYPE-SET NIL)))
         0 < T)))
      (MOD (BINARY-+ X Y) Z))))
