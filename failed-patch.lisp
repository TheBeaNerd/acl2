(ld "tracing.lisp")

;; Unfortunately your idea is misguided.

;; We endeavor to maintain the following invariants over the linear pot
;; - If we have both :positives and :negatives, we have only one poly for each
;; - A heavy variable appears in a poly outside of its own pot only if
;;   its pot contains only polys with the same polarity

(defun get-coeff-for-cancel-p2 (var alist)
  (declare (xargs :mode :program))
  (cond ((null alist) 
         (mv t 0))
        ((not (arith-term-order var (caar alist))) 
         (mv nil 0))
        ((equal var (caar alist))
         (mv nil (cdar alist)))
        (t
         (get-coeff-for-cancel-p2 var (cdr alist)))))

(defun cancel-p22 (alist coeff)
  (declare (xargs :mode :program))
  (cond ((null alist) nil)
        (t (cons (cons (caar alist)
                       (* coeff (cdar alist)))
                 (cancel-p22 (cdr alist) coeff)))))

(defun cancel-p21 (alist1 alist2 coeff)
  (declare (xargs :mode :program))

; Alist1 and alist2 are the alists from two polys.  We are about to
; cancel alist2 from alist1.  We create a new alist by adding alist1 
; to (* coeff alist2).

  (cond ((null alist2) 
         alist1)
        ((null alist1)
         (cancel-p22 alist2 coeff))
        ((not (arith-term-order (caar alist1) (caar alist2)))
         (cons (car alist1)
               (cancel-p21 (cdr alist1) alist2 coeff)))
        ((equal (caar alist1) (caar alist2))
         (let ((temp (+ (cdar alist1)
                        (* coeff (cdar alist2)))))
           (cond ((= temp 0)
                  (cancel-p21 (cdr alist1) (cdr alist2) coeff))
                 (t (cons (cons (caar alist1) temp)
                          (cancel-p21 (cdr alist1) (cdr alist2) coeff))))))
        (t (cons (cons (caar alist2)
                       (* (cdar alist2) coeff))
                 (cancel-p21 alist1 (cdr alist2) coeff)))))

(defun cancel-p2 (p1 coeff p2)
  (declare (xargs :mode :program))
  (let* ((alist1  (access poly p1 :alist))
         (alist2  (access poly p2 :alist)))
    (make poly
          :constant (+ (access poly p1 :constant)
                       (* coeff (access poly p2 :constant)))
          :alist (cancel-p21 alist1
                             alist2
                             coeff)
          :relation  (if (or (eq (access poly p1 :relation) '<)
                             (eq (access poly p2 :relation) '<))
                         '<
                       '<=)
          :ttree (cons-tag-trees (access poly p1 :ttree)
                                 (access poly p2 :ttree))
          :rational-poly-p (and (access poly p1 :rational-poly-p)
                                (access poly p2 :rational-poly-p))
          :parents (marry-parents (access poly p1 :parents)
                                  (access poly p2 :parents))
          :derived-from-not-equalityp nil)))

(defun reduce-poly-with-pot (p pot)
  (declare (xargs :mode :program))
  (let ((var (access linear-pot pot :var)))
    (mv-let (done coeff) (get-coeff-for-cancel-p2 var (access poly p :alist))
      (if done (mv done p)
        (if (= coeff 0) (mv nil p)
          (let ((diff (if (< 0 coeff) (access linear-pot pot :negatives)
                         (access linear-pot pot :positives))))
            (if (not diff) (mv nil p)
              (mv nil (cancel-p2 p (abs coeff) (car diff))))))))))

(defun reduce-poly-with-pot-lst (p pot-lst)
  (declare (xargs :mode :program))
  (if (not pot-lst) p
    (let ((pot (car pot-lst)))
      (mv-let (done p) (reduce-poly-with-pot p pot)
        (if done p
          (reduce-poly-with-pot-lst p (cdr pot-lst)))))))

(defun remove-poly-from-basis (p basis)
  (declare (xargs :mode :program))
  (let ((var (first-var p)))
    (mv-let (done coeff) (get-coeff-for-cancel-p2 var (access poly basis :alist))
      (if (or done (= coeff 0) (= (signum coeff) (signum (first-coefficient p)))) (mv nil basis)
        (mv t (cancel-p2 basis (abs coeff) p))))))

(defun remove-poly-from-basis-list (p list)
  (declare (xargs :mode :program))
  (if (not list) nil
    (mv-let (change poly) (remove-poly-from-basis p (car list))
      (declare (ignore change))
      (cons poly (remove-poly-from-basis-list p (cdr list))))))

(defun remove-poly-from-rev-pot-lst (p rev-pot-lst pot-lst to-do-next)
  (declare (xargs :mode :program))
  (if (not rev-pot-lst) (mv nil pot-lst to-do-next)
    (let ((pot (car rev-pot-lst)))
      (let ((positives (access linear-pot pot :positives))
            (negatives (access linear-pot pot :negatives)))
        (cond
         ((and positives negatives)
          (mv-let (pchange positive) (remove-poly-from-basis p (car positives))
            (mv-let (nchange negative) (remove-poly-from-basis p (car negatives))
              (cond
               ((or nchange pchange)
                (let ((positives (list positive))
                      (negatives (list negative)))
                (mv-let (unsat res) (cancel positive negative)
                  (cond
                   (unsat (mv unsat nil nil))
                   (t 
                    (let ((pot (change linear-pot pot :positives positives :negatives negatives)))
                      (let ((to-do-next (if res (cons res to-do-next) to-do-next)))
                        (remove-poly-from-rev-pot-lst p (cdr rev-pot-lst) (cons pot pot-lst) to-do-next))))))))
               (t
                (remove-poly-from-rev-pot-lst p (cdr rev-pot-lst) (cons pot pot-lst) to-do-next))))))
         (positives
          (let ((positives (remove-poly-from-basis-list p positives)))
            (let ((pot-lst (cons (change linear-pot pot :positives positives) pot-lst)))
              (remove-poly-from-rev-pot-lst p (cdr rev-pot-lst) pot-lst to-do-next))))
         (t
          (let ((negatives (remove-poly-from-basis-list p negatives)))
            (let ((pot-lst (cons (change linear-pot pot :negatives negatives) pot-lst)))
              (remove-poly-from-rev-pot-lst p (cdr rev-pot-lst) pot-lst to-do-next)))))))))
        
;;
;; You do sometimes want to replace the existing 
;; basis if the new one is "stronger" .. given
;; that this is somewhat arbitrary, you should
;; probably have some metric for that .. ie:
;; fewer variables, prefer < to <= .. etc.
;;
(defun choose-a-over-b (a b)
  (declare (xargs :mode :program))
  (if (or (poly-weakerp b a nil)
          (and (eq (access poly a :relation) '<)
               (eq (access poly b :relation) '<=))
          (< (len (access poly a :alist))
             (len (access poly b :alist)))) a
    b))

(defun keep-stronger (poly list)
  (declare (xargs :mode :program))
  (if (not list) (list poly)
    (if (= (len (access poly (car list) :alist))
           (len (access poly poly :alist)))
        (cond
         ((poly-weakerp (car list) poly nil)
          (cons poly (cdr list)))
         ((poly-weakerp poly (car list) nil)
          list)
         (t
          (cons (car list) (keep-stronger poly (cdr list)))))
      (cons poly list))))

(defun order-polys (poly list)
  (declare (xargs :mode :program))
  (if (not list) (list poly)
    (if (< (len (access poly (car list) :alist))
           (len (access poly poly :alist)))
        (cons (car list) (order-polys poly (cdr list)))
      (keep-stronger poly list))))

(defun add-poly-rec (p pot-lst previous pt to-do-next)
  (declare (xargs :mode :program))
  (cond
   ((or (not pot-lst)
        (not (term-order (first-var p) (access linear-pot (car pot-lst) :var))))
    (let ((p (if (not pot-lst) p (reduce-poly-with-pot-lst p pot-lst))))
      (cond
       ((impossible-polyp p)
        (mv p nil nil))
       ((true-polyp p)
        (mv nil (revappend previous pot-lst) nil))
       (t
        (let ((pot-lst (cons (if (< 0 (first-coefficient p))
                                 (make linear-pot
                                       :var (first-var p)
                                       :loop-stopper-value 0
                                       :positives (list p)
                                       :negatives nil)
                               (make linear-pot
                                     :var (first-var p)
                                     :loop-stopper-value 0
                                     :positives nil
                                     :negatives (list p)))
                             pot-lst)))
          (remove-poly-from-rev-pot-lst p previous pot-lst to-do-next))))))
   ((equal (first-var p) (access linear-pot (car pot-lst) :var))
    (let ((p   (reduce-poly-with-pot-lst p (cdr pot-lst)))
          (pot (car pot-lst)))
      (cond
       ((impossible-polyp p)
        (mv p nil nil))
       ((true-polyp p)
        (mv nil (revappend previous pot-lst) nil))
       (t
        (mv-let (same diff) (if (< 0 (first-coefficient p)) (mv (access linear-pot pot :positives) (access linear-pot pot :negatives))
                              (mv (access linear-pot pot :negatives) (access linear-pot pot :positives)))
          (mv-let (unsat to-do-next) (cancel-poly-against-all-polys p diff pt to-do-next)
            (cond
             (unsat
              (mv unsat nil nil))
             (t
              (mv-let (same diff) (if (not same) (mv (list p) (list (car diff)))
                                    (if (not diff) (mv (order-polys p same) diff)
                                      (mv (list (choose-a-over-b p (car same))) diff)))
                (let ((pot (if (< 0 (first-coefficient p)) (change linear-pot pot :positives same :negatives diff)
                             (change linear-pot pot :negatives same :positives diff))))
                  (let ((pot-lst (cons pot (cdr pot-lst))))
                    (remove-poly-from-rev-pot-lst p previous pot-lst to-do-next))))))))))))
   (t
    (add-poly-rec p (cdr pot-lst) (cons (car pot-lst) previous) pt to-do-next))))

(defttag :normal)
:redef!

(defun add-poly (p pot-lst to-do-next pt nonlinearp)
  (declare (ignore nonlinearp)
           (xargs :mode :program))
  (add-poly-rec p pot-lst nil pt to-do-next))

#+joe
(trace$ (add-poly 
         :entry `(add-poly ,(untranslate (poly-to-expr p) nil (w state)) ,(untranslate `(pot ,@(poly-pot-list pot-lst)) nil (w state)))
         :exit  `(add-poly ,(nth 0 values) ,(untranslate `(pot ,@(poly-pot-list (nth 1 values))) nil (w state))
                           ;;,(untranslate `(to-do ,@(poly-term-lst (nth 2 values))) nil (w state)))
                           )
         ))

(trace$ (add-polys0
         :entry `(add-polys0 ,(untranslate `(to-do ,@(poly-term-lst lst)) nil (w state)) ,(untranslate `(pot ,@(poly-pot-list pot-lst)) nil (w state)))
         :exit  (and (not (break$)) `(add-polys0 ,(nth 0 values) ,(untranslate `(pot ,@(poly-pot-list (nth 1 values))) nil (w state))
                                                ;;,(untranslate `(to-do ,@(poly-term-lst (nth 2 values))) nil (w state)))
                                                ))
         ))

#+joe
(ADD-POLY (< 0
                  (+ (* -1 GETVAL96)
                     (* 2/5 GETVAL107)
                     (* 1/5 GETVAL101)
                     (* 2/5 GETVAL)
                     -3))
               (POT (< 0 (+ (* -1 GETVAL98) 128))
                    (< 0 (+ GETVAL98 (* -1 GETVAL114) 0))
                    (< 0 (+ (* -1 GETVAL96) 113))
                    (<= 0 (+ GETVAL96 128))
                    (< 0 (+ (* -1 GETVAL114) 128))
                    (< 0 (+ GETVAL114 (* -2 GETVAL101) -123))
                    (<= 0 (+ GETVAL101 128))
                    (<= 0 (+ GETVAL -128))))

#+joe
(trace$ (reduce-poly-with-pot-lst
         :entry `(reduce-poly-with-pot-lst ,(untranslate (poly-to-expr p) nil (w state)) ,(untranslate `(pot ,@(poly-pot-list pot-lst)) nil (w state)))
         :exit  `(reduce-poly-with-pot-lst ,(untranslate (poly-to-expr (nth 0 values)) nil (w state)))
         ))



#+joe
(trace$ reduce-poly-with-pot)

#+joe
(trace$ (remove-poly-from-basis 
         :entry `(remove-poly-from-basis
                  ,(untranslate (poly-to-expr p) nil (w state))
                  ,(untranslate (poly-to-expr basis) nil (w state))
                  )
         :exit `(remove-poly-from-basis
                 ,(nth 0 values)
                 ,(untranslate (poly-to-expr (nth 1 values)) nil (w state)))))

#+joe
(trace$ (cancel-poly-against-all-polys
         :entry `(cancel-poly-against-all-polys ,(untranslate (poly-to-expr p) nil (w state))
                                                ,(untranslate `(pot ,@(poly-term-lst polys)) nil (w state))
                                                ,(untranslate `(pot ,@(poly-term-lst ans)) nil (w state)))
         :exit `(cancel-poly-against-all-polys)))

#+joe
(trace$ (cancel
         :entry `(cancel ,(untranslate (poly-to-expr p1) nil (w state))
                         ,(untranslate (poly-to-expr p1) nil (w state)))
         :exit `(cancel ,(untranslate (poly-to-expr (nth 1 values)) nil (w state)))))

#+joe
(trace$ (poly-weakerp
         :entry `(poly-weakerp ,(untranslate (poly-to-expr poly1) nil (w state))
                               ,(untranslate (poly-to-expr poly2) nil (w state)))
         :exit `(poly-weakerp)))

#+joe
(trace$ (poly-member
         :entry `(poly-member ,(untranslate (poly-to-expr p) nil (w state))
                              ,(untranslate `(pot ,@(poly-term-lst lst)) nil (w state)))
         :exit `(poly-member)))

#+joe
(trace$ (remove-poly-from-rev-pot-lst 
         :entry `(remove-poly-from-rev-pot-lst ,(untranslate (poly-to-expr p) nil (w state))
                                               ,(untranslate `(pot ,@(poly-pot-list rev-pot-lst)) nil (w state)) 
                                               ,(untranslate `(pot ,@(poly-pot-list pot-lst)) nil (w state)))
         :exit  `(remove-poly-from-rev-pot-lst ,(untranslate `(pot ,@(poly-pot-list (nth 1 values))) nil (w state)))))

#+joe
(thm
 (implies
  (and
   (rationalp x)
   (rationalp y)
   (rationalp z)
   (< 0 (+ z x))
   (< 0 (+ (- z) y)))
  (integerp z)))

