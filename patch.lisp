(in-package "ACL2")

(defttag :lp)
:redef!

(defun add-polys0 (lst pot-lst pt nonlinearp max-rounds)
  (declare (xargs :mode :program))
  (dag-add-polys0 lst pot-lst pt nonlinearp max-rounds))

(SET-DEBUGGER-ENABLE T)
(break-on-error t)

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

(defun show-vector-alist (alist state)
  (declare (xargs :mode :program))
  (if (not (consp alist)) nil
    (let ((pair (car alist)))
      (cons `(,(show-vector (car pair) state) ! ,(show-vector (cdr pair) state))
            (show-vector-alist (cdr alist) state)))))

(defun show-zlist (zlist state)
  (declare (xargs :mode :program))
  (untranslate `(:zlist ,@(poly-term-lst zlist)) nil (w state)))
 
(defun show-plist (plist state)
  (declare (xargs :mode :program))
  (untranslate `(:plist ,@(poly-term-lst plist)) nil (w state)))

(defun show-evecs (evecs state)
  (declare (xargs :mode :program))
  (untranslate `(:evecs ,@(poly-term-lst evecs)) nil (w state)))

(defun show-gvecs (gvecs state)
  (declare (xargs :mode :program))
  (untranslate `(:gvecs ,@(poly-term-lst gvecs)) nil (w state)))

(defun show-zdb (zdb state)
  (declare (xargs :mode :program))
  (let ((gvecs (access zdb zdb :gvecs))
        (evecs (access zdb zdb :evecs)))
    `(zdb
      ,(show-gvecs gvecs state)
      ,(show-evecs evecs state)
      )))

(defun show-pstat (pstat state)
  (declare (xargs :mode :program))
  (let ((zlist (access pstat pstat :zlist))
        (plist (access pstat pstat :plist))
        (zdb   (access pstat pstat :zdb))
        (sln   (access pstat pstat :sln)))
      `(pstat
        (:sln ,sln)
        ,(show-plist plist state)
        ,(show-zlist zlist state)
        ,(show-zdb zdb state)
        )))

#+joe
(trace$ dag-self-dot)

#+joe
(trace$ dag-dot-alist)

#+joe
(trace$ (dag-dot-vectors
         :entry `(dag-dot-vectors ,(show-vector v1 state)
                                  ,(show-vector v2 state))
         :exit  `(dag-dot-vectors ,(nth 0 values))))

#+joe
(trace$ (dag-insert-deltas
         :entry `(dag-insert-deltas)
         :exit `(dag-insert-deltas ,(show-vector-list (nth 0 values) state)
                                   ,(show-vector-list (nth 1 values) state))))

#+joe
(trace$ (dag-insert-deltas-loop
         :entry `(dag-insert-deltas-loop ,(show-vector vector state) 
                                         ,(show-vector-list deltas state) 
                                         ,(show-vector-list gvecs state)
                                         ,(show-vector-list evecs state))
         :exit `(dag-insert-deltas-loop)))

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
(trace$ (dag-check-non-negative-invariant
         :entry `(dag-check-non-negative-invariant ,(show-vector residual state) ,(show-vector-list bases state))
         :exit  `(dag-check-non-negative-invariant)
         ))

#+joe
(trace$ (remove-negative-zvectors-from-vector1
         :entry `(remove-negative-zvectors-from-vector1 ,(show-vector-list zvectors state) ,(show-vector vector state))
         :exit  `(remove-negative-zvectors-from-vector1 ,(show-vector (nth 0 values) state))
         ))

#+joe
(trace$ (dag-zero-vectorp
         :entry `(dag-zero-vectorp ,(show-vector vector state))
         :exit  `(dag-zero-vectorp ,(nth 0 values))))

#+joe
(trace$ (dag-insert-positive-poly
         :entry `(dag-insert-positive-poly ,score ,(show-vector poly state) ,(show-pstat pstat state))
         :exit  `(dag-insert-positive-poly ,(show-pstat (nth 0 values) state))
         ))

#+joe
(trace$ (dag-insert-zero-poly
         :entry `(dag-insert-zero-poly ,(show-vector poly state) ,(show-pstat pstat state))
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

#+joe
(trace$ (dag-remove-opposing-bases-from-vector
         :entry `(dag-remove-opposing-bases-from-vector ,(show-vector vector state) 
                                                        ,(show-vector-list bases state))
         :exit  `(dag-remove-opposing-bases-from-vector ,(show-vector (nth 0 values) state))
         ))

#+joe
(trace$ (dag-remove-opposing-polys-from-vector
         :entry `(dag-remove-opposing-polys-from-vector ,(show-vector vector state) 
                                                        ,(show-vector-list zlist state))
         :exit  `(dag-remove-opposing-polys-from-vector ,(nth 0 values)
                                                        ,(show-vector (nth 1 values) state)
                                                        ,(show-vector-list (nth 2 values) state)
                                                        ,(show-vector-list (nth 3 values) state))
         ))

#+joe
(trace$ (dag-remove-opposing-polys-from-vector1
         :entry `(dag-remove-opposing-polys-from-vector1)
         :exit   `(dag-remove-opposing-polys-from-vector1
                   ,(nth 0 values)
                   ,(show-vector (nth 1 values) state)
                   )
         ))

#+joe
(trace$ (dag-trace-loop
         :entry `(dag-trace-loop
                  :vector ,(show-vector vector state)
                  :residual ,(show-vector residual state)
                  :xlist  ,(show-vector-list xlist state)
                  :glist  ,(show-vector-list glist state)
                  :gbases ,(show-vector-list gbases state)
                  :ebases ,(show-vector-list ebases state)
                  :ylist  ,(show-vector-list ylist state)
                  )
         :exit   `(dag-trace-loop)
         ))

#+joe
(trace$ (DAG-ADD-POLY-LIST
         :entry `(DAG-ADD-POLY-LIST ,(show-vector-list polys state) ,(show-pstat pstat state))
         :exit  `(DAG-ADD-POLY-LIST ,(nth 0 values) ,(show-pstat (nth 1 values) state))
         ))

#+joe
(trace$ (DAG-backtrack
         :entry `(dag-backtrack ,(show-vector vector state) ,(show-vector residual state) ,(show-vector x state))
         :exit  `(dag-backtrack ,(show-vector (nth 0 values) state)
                                ,(show-vector (nth 1 values) state))
         ))

#+joe
(trace$ (dag-extract-and-apply-equalities
         :entry `(dag-extract-and-apply-equalities
                  :vector ,(show-vector constraint  state)
                  :gvecs  ,(show-vector-list gvecs  state)
                  :deltas ,(show-vector-list deltas state)
                  :evecs  ,(show-vector-list evecs  state))
         :exit  `(dag-extract-and-apply-equalities
                  ,(nth 0 values)
                  :vector ,(show-vector (nth 1 values) state)
                  :gvecs  ,(show-vector-list (nth 2 values) state)
                  :deltas ,(show-vector-list (nth 3 values) state)
                  :evecs  ,(show-vector-list (nth 4 values) state)
                  )
         ))

#+joe
(trace$ (dag-consider-vector
         :entry `(dag-consider-vector
                  :vector ,(show-vector vector state)
                  :gvecs  ,(show-vector-list gvecs state)
                  :evecs  ,(show-vector-list deltas state))
         :exit  `(dag-consider-vector
                  :vector ,(show-vector (nth 0 values) state)
                  :gvecs  ,(show-vector-list (nth 1 values) state)
                  :evecs  ,(show-vector-list (nth 2 values) state)
                  )
         ))

#+joe
(trace$ (dag-remove-base-list-from-vector 
         :entry `(dag-remove-base-list-from-vector ,(show-vector vector state) ,(show-vector-list blist state))
         :exit  `(dag-remove-base-list-from-vector ,(nth 0 values) 
                                                   ,(show-vector (nth 1 values) state))
         ))

#+joe
(trace$ (dag-construct-residuals
        :entry `(dag-construct-residuals
                 :const  ,(show-vector constraint   state)
                 :vlist  ,(show-vector-list vlist   state)
                 :zeros  ,(show-vector-list  zeros  state)
                 :palist ,(show-vector-alist palist state)
                 :zlist  ,(show-vector-list  zlist  state)
                 :nalist ,(show-vector-alist nalist state)
                 )
        :exit  `(dag-construct-residuals
                 :zeros  ,(show-vector-list  (nth 0 values) state)
                 :palist ,(show-vector-alist (nth 1 values) state)
                 :zlist  ,(show-vector-list  (nth 2 values) state)
                 :nalist ,(show-vector-alist (nth 3 values) state)
                 )
        ))
                      
#+joe
(trace$ (dag-extract-triangle-equalities1
         :entry `(dag-extract-triangle-equalities1
                  :ref   ,(show-vector ref state)
                  :alist ,(show-vector-alist aalist state)
                  :evecs ,(show-vector-list evecs state))
         :exit  `(dag-extract-triangle-equalities1
                  :alist ,(show-vector-alist (nth 0 values) state)
                  :evecs ,(show-vector-list (nth 1 values) state)
                  )
         ))

#+joe
(trace$ (dag-realize-vector-zdb
         :entry `(dag-realize-vector-zdb
                  ,(show-vector vector state)
                  ,(show-zdb zdb state)
                  )
         :exit  `(dag-realize-vector-zdb
                  ,(show-vector (nth 0 values) state)
                  ,(show-zdb (nth 1 values) state)
                  )
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

#+joe
(trace$ (dag-check-pstat
         :entry `(dag-check-pstat ,(show-pstat pstat state))
         :exit  `(dag-check-pstat ,(nth 0 values))))

#+joe
(trace$ (ignore-polyp
         :entry `(ignore-polyp)
         :exit  `(ignore-polyp ,(nth 0 values))))

#+joe
(trace$ (ADD-POLY
         :entry `(ACL2-ADD-POLY ,(show-vector p state) ,(untranslate `(poly-pot ,@(poly-pot-list pot-lst)) nil (w state)) ,incomplete)
         :exit  `(ACL2-ADD-POLY ,(nth 0 values)
                                ,(untranslate `(poly-pot ,@(poly-pot-list (nth 1 values))) nil (w state))
                                ,(show-vector-list (nth 2 values) state)
                                ,(nth 3 values)
                                )
         ))

#+joe
(trace$ (ADD-POLYS1
         :entry `(ACL2-ADD-POLYS1 ,(show-vector-list lst state) ,(untranslate `(poly-pot ,@(poly-pot-list pot-lst)) nil (w state)) ,incomplete)
         :exit  `(ACL2-ADD-POLYS1 ,(nth 0 values) ,(nth 2 values))
         ))

#+joe
(trace$ (dag-epsilon-unsat
         :entry `(dag-epsilon-unsat ,(show-pstat pstat state))
         :exit  `(dag-epsilon-unsat ,(nth 0 values) ,(nth 1 values))
         ))

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

(let ((unsat1 (DAG-ADD-POLYS1
              '(((((((IFIX I) . 1) (J . -1)) NIL) 0 <= NIL)))
              '(((0) I (((((I . 1)) (2) (PT 2 3)) 0 <= T)))
                ((0) J (((((J . 1)) (1 0) (PT 0 1)) -1 <= T))
                 (((((J . 1) (I . -1)) (5 1 0 3 2) (PT 2 3 0 1 5)
                    (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)))
                   -1 <= T)))))))
  (assert$ (not unsat1) nil))

(let ((unsat2 (DAG-ADD-POLYS1
              '((((((I . 1)) NIL) -1 <= T)))
              '(((0) I (((((I . 1)) NIL) 0 <= T)))
                ((0 (((((J . -1) (I . 1)) NIL) 0 <= T))
                    (((((J . -1)) NIL (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL))) 0 <=
                      T)))
                 J (((((J . 1)) NIL) 0 <= T)))))))
  (assert$ (not unsat2) nil))

(let ((unsat3 (DAG-ADD-POLYS1
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
  (assert$ unsat3 nil))

(let ((unsat4 (DAG-ADD-POLYS1
              '((((((Z . -1) (Y . 1)) NIL (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)))
                  0 <= T))
                (((((Z . 1) (Y . -1) (W . -1)) NIL
                   (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)))
                  0 < T))
                (((((W . 1)) NIL) 0 < T)) (((((Y . 1)) NIL) 0 < T)))
              'NIL)))
  (assert$ unsat4 nil))

(let ((unsat5 (DAG-ADD-POLYS1
              '(((((((LEN (CDR X)) . -1) (N . 1)) NIL
                   (LEMMA (:TYPE-PRESCRIPTION LEN)
                          (:FAKE-RUNE-FOR-TYPE-SET NIL)))
                  -2 <= T))
                ((((((LEN (NTHCDR (BINARY-+ '-1 N) (CDR X))) . 1)
                    ((LEN (CDR X)) . -1) (N . 1))
                   NIL
                   (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                          (:TYPE-PRESCRIPTION LEN)))
                  -1 <= T . T))
                ((((((LEN (NTHCDR (BINARY-+ '-1 N) (CDR X))) . -1)
                    ((LEN (CDR X)) . 1) (N . -1))
                   NIL
                   (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                          (:TYPE-PRESCRIPTION LEN)))
                  1 <= T . T))
                ((((((LEN (CDR X)) . 1) (N . -1)) NIL
                   (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                          (:TYPE-PRESCRIPTION LEN)))
                  1 <= T))
                (((((N . 1)) NIL (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL))) -1 <=
                  T)))
              'NIL)))
  (assert$ unsat5 nil))

(let ((unsat6 (DAG-ADD-POLYS1
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
                 (MOD (BINARY-+ X Y) Z))))))
  (assert$ (not unsat6) nil))



;; (include-book "projects/smtlink/top" :dir :system)
;; (add-default-hints '((smt::smt-computed-hint clause)))
;; (value-triple (tshell-ensure))

;; (defthm hmm
;;   (implies
;;   (and
;;    (rationalp x)
;;    (rationalp y)
;;    (rationalp z)
;;    (rationalp m)
;;    (< 0 (+ (* -1 M)
;;            (* -1 Z)
;;            Y X 0))
;;    (<= 0 (+ M 0))
;;    (< 0 (+ X 0))
;;    (<= 0 (+ X 0))
;;    (< 0 (+ Y X 0))
;;    (< 0 (+ Y 0))
;;    (<= 0 (+ Y 0))
;;    (< 0 (+ (* -1 Z) Y X 0))
;;    (<= 0 (+ (* -1 Z) Y X 0))
;;    (< 0 (+ Z (* -1 X) 0))
;;    (< 0 (+ Z (* -1 Y) 0))
;;    (< 0 (+ Z 0))   
;;    )
;;   nil)
;;   :rule-classes nil
;;   :hints (("Goal" :smtlink nil)))

;; => (z 3) (x 2) (y 2)

#+joe
(defthm hmm
  (implies
  (and
   (rationalp x)
   (rationalp y)
   (rationalp z)
   (rationalp zz)
   (< 0 (+ (* -1 ZZ)
           (* -1 Z)
           Y X -1))
   (< 0 (+ (* -1 ZZ)
           (* -1 Z)
           Y X 0))
   (<= 0 (+ ZZ 0))
   (< 0 (+ X 0))
   (<= 0 (+ X 0))
   (< 0 (+ Y X 0))
   (< 0 (+ Y 0))
   (<= 0 (+ Y 0))
   (< 0 (+ (* -1 Z) Y X 0))
   (<= 0 (+ (* -1 Z) Y X 0))
   (< 0 (+ Z (* -1 X) 0))
   (< 0 (+ Z (* -1 Y) 0))
   (< 0 (+ Z 0))   
   )
  nil)
  :rule-classes nil)

#|

;; Adding
(< 0 (+ (* -1 (MOD (+ X Y) Z))
        (* -1 Z)
        Y X 0))

;; Consider the zero poly .. don't make it negative .. so ..

(<= 0 (+ (MOD (+ X Y) Z) 0))

;; Resultant vector ..

(< 0 (+ (* -1 Z) Y X 0))

: (= 0 (+ (MOD (+ X Y) Z) 0))

;; Consider the zero poly .. don't make it negative .. so ..

(< 0 (+ Z 0))

;; Resultant vector ..

(< 0 (+ Y X 0))

: (<= 0 (+ (MOD (+ X Y) Z) 0))
: (< 0 (+ Z 0))

|#

(thm
 (IMPLIES (AND (< 0 J)
              (INTEGERP J)
              (<= 0 I)
              (INTEGERP I)
              (NOT (OR (= (NFIX J) 0) (< (IFIX I) J))))
          (<= 0 (+ I (- J)))))

(thm
 (IMPLIES (AND (<= (+ START2 (LENGTH SEQ1)) END2)
              (<= END2 (LENGTH SEQ2))
              (INTEGERP END2)
              (<= 0 START2)
              (INTEGERP START2)
              (TRUE-LISTP SEQ2)
              (TRUE-LISTP SEQ1))
         (LET ((BOUND2 (+ START2 (LENGTH SEQ1))))
              (AND (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (<= 0 START2))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (INTEGERP START2))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL BOUND2 NIL)
                       (<= BOUND2 (LENGTH SEQ2)))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL BOUND2 NIL)
                       (INTEGERP BOUND2))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (TRUE-LISTP SEQ2)
                       (STRINGP SEQ2))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (NOT BOUND2)
                       (<= START2 BOUND2))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       BOUND2 (<= START2 (LENGTH SEQ2)))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                       (RATIONALP BOUND2))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                       (RATIONALP END2))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                       (<= END2 BOUND2)
                       (ACL2-NUMBERP START2))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                       (<= END2 BOUND2)
                       (INTEGERP END2))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                       (<= END2 BOUND2)
                       (INTEGERP (+ 1 START2)))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                       (<= END2 BOUND2)
                       (<= (+ 1 START2 (LENGTH SEQ1)) END2))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                       (<= END2 BOUND2)
                       (<= END2 (LENGTH SEQ2)))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                       (<= END2 BOUND2)
                       (<= 0 (+ 1 START2)))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                       (<= END2 BOUND2)
                       (TRUE-LISTP SEQ1)
                       (STRINGP SEQ1))
                   (OR (OR (NOT (INTEGERP END2))
                           (NOT (INTEGERP START2)))
                       (EQUAL SEQ1 (SUBSEQ SEQ2 START2 BOUND2))
                       (<= END2 BOUND2)
                       (TRUE-LISTP SEQ2)
                       (STRINGP SEQ2))))))

#+joe
(thm
 (IMPLIES (AND (EQUAL TEST 'EQUAL)
               (STRINGP SEQ1)
               (STRINGP SEQ2)
               END1P END2P (INTEGERP START1)
               (<= 0 START1)
               (INTEGERP START2)
               (<= 0 START2)
               (INTEGERP END1)
               (<= 0 END1)
               (INTEGERP END2)
               (<= 0 END2)
               (<= START1 END1)
               (<= START2 END2)
               (<= END1 (LENGTH SEQ1))
               (<= END2 (LENGTH SEQ2))
               (ACL2-NUMBERP START2)
               (<= (+ END1 (- START1))
                   (+ END2 (- START2))))
          (<= (+ START2
                 (LEN (COERCE (SUBSEQ SEQ1 START1 END1)
                              'LIST)))
              END2)))

#+joe
(thm
 (implies
  (and (< 0
          (+ (* -1 (LEN (COERCE SEQ1 'LIST)))
             END1 0))
       (<= 0
           (+ (LEN (COERCE (SUBSEQ SEQ1 START1 END1)
                           'LIST))
              START2 (* -1 END2)
              -1))
       (<= 0 (+ END1 0))
       (<= 0 (+ END1 0))
       (<= 0 (+ END2 0))
       (<= 0 (+ END2 0))
       (<= 0 (+ END2 0))
       (<= 0 (+ (* -1 START1) END1 0))
       (<= 0 (+ START1 END2 (* -1 END1) 0))
       (<= 0 (+ START1 0))
       (<= 0 (+ (* -1 START2) END2 0))
       (<= 0
           (+ (* -1 START2)
              START1 END2 (* -1 END1)
              0))
       (<= 0 (+ START2 0))
       (<= 0 (+ (LENGTH SEQ1) 0))
       (<= 0 (+ (LENGTH SEQ1) (* -1 END1) 0))
       (<= 0 (+ (LENGTH SEQ2) 0))
       (<= 0 (+ (LENGTH SEQ2) (* -1 END2) 0))
       (<= 0
           (+ (LEN (COERCE (SUBSEQ SEQ1 START1 END1)
                           'LIST))
              0)))
  nil))


(let ((unsat (DAG-ADD-POLYS1
              '((((((Y . 1)) (5 4) (PT 4 5)) 0 <= T)))
              '(((0) X (((((X . 1)) (3) (PT 2 3)) 0 <= T)))
                ((0) Y
                 (((((Y . 1) (X . 1)) NIL (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL))
                    (PT 2 3 4 5))
                   0 < T))
                 (((((Y . 1)) (5) (PT 4 5)) 0 <= T)))
                ((0) Z (((((Z . 1) (X . -1)) (0) (PT 0 2 3 6 7)) 0 < T))
                 (((((Z . 1) (Y . -1)) (1) (PT 1 4 5 6 7)) 0 < T))
                 (((((Z . 1)) (7) (PT 6 7)) 0 < T))
                 (((((Z . 1) (Y . -1) (X . -1)) (8) (PT 8 2 3 4 5 6 7)
                    (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)))
                   0 < T)))
                ((0) (MOD (BINARY-+ X Y) Z)
                 ((((((MOD (BINARY-+ X Y) Z) . 1)) (5 4 3 2 7 6)
                    (LEMMA (:TYPE-PRESCRIPTION MOD-TYPE . 4)
                           (:TYPE-PRESCRIPTION RATIONALP-MOD)
                           (:FAKE-RUNE-FOR-TYPE-SET NIL))
                    (PT 6 7 2 3 4 5))
                   0 <= T))
                 ((((((MOD (BINARY-+ X Y) Z) . 1) (Y . -1) (X . -1))
                    (5 4 3 2 9 7 6) (PT 6 7 9 2 3 4 5)
                    (LEMMA (:TYPE-PRESCRIPTION MOD-TYPE . 4)
                           (:TYPE-PRESCRIPTION RATIONALP-MOD)
                           (:FAKE-RUNE-FOR-TYPE-SET NIL)))
                   0 < T)))))))
  unsat)

(let ((unsound (DAG-ADD-POLYS1
                '((((((START2 . 1)) NIL
                     (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                            (:TYPE-PRESCRIPTION LEN)))
                    -1 <= T)))
                '(((0) START2
                   (((((START2 . 1)) NIL
                      (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                             (:TYPE-PRESCRIPTION LEN)))
                     0 <= T)))
                  ((0) (LEN SEQ2)
                   ((((((LEN SEQ2) . 1) (END2 . -1)) NIL
                      (LEMMA (:TYPE-PRESCRIPTION LEN)))
                     0 <= T)))
                  ((0
                    ((((((LEN (COERCE SEQ1 'LIST)) . -1) (START2 . -1) (END2 . 1))
                       NIL
                       (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                              (:TYPE-PRESCRIPTION LEN)))
                      0 <= T))
                    ((((((LEN (COERCE SEQ1 'LIST)) . -1)) NIL
                       (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)
                              (:TYPE-PRESCRIPTION LEN)))
                      -1 <= T)))
                   (LEN (COERCE SEQ1 'LIST)))))))
  (assert$ (not unsound) nil))

(let ((incomplete (DAG-ADD-POLYS1
   '(((((((LEN X) . -1) (N . 1)) NIL) 0 < NIL)))
   '(((0) (LEN X)
      ((((((LEN X) . 1)) (4 0) (PT 0 4)
         (LEMMA (:TYPE-PRESCRIPTION LEN)
          (:COMPOUND-RECOGNIZER ZP-COMPOUND-RECOGNIZER)))
        -1 <= T))
      ((((((LEN X) . 1) (N . -1)) (4) (PT 4 0)
         (LEMMA (:TYPE-PRESCRIPTION LEN)
          (:COMPOUND-RECOGNIZER ZP-COMPOUND-RECOGNIZER)))
        0 <= T)))))))
  (assert$ incomplete nil))
