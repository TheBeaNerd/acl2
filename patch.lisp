(in-package "ACL2")

(include-book "finite-set-theory/total-ordering" :dir :system)
(include-book "coi/util/mv-nth" :dir :system)

;; This is a linear routine built on top of the ACL2 poly
;; representation.

;; pstat holds the status of the current polys.
;; It consists of a rational valued solution vector and
;; a list of polys ordered by their satisfaction score.
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
;; NOTE: If the score is zero, we say that the solution
;; "satisfies" the poly conditionally.  The condition is that
;; the resultant vector
;;
;; Negative satisfaction

;;

#+joe
(defun << (a b) 
  (declare (xargs :mode :program))
  (not (arith-term-order a b)))

(defrec pstat (sln zeros plist) t)
(defrec zeros (originals . zbases) t)

(defun self-dot (alist1 dot)
  (if (not (consp alist1)) dot
    (self-dot (cdr alist1) (+ (* (cdar alist1) (cdar alist1)) dot))))

(defun dot-alist (alist1 alist2 dot)
  (declare (xargs :measure (+ (len alist1) (len alist2))))
  (cond
   ((not (consp alist1))
    dot)
   ((not (consp alist2)) 
    dot)
   ((<< (caar alist1) (caar alist2))
    (dot-alist (cdr alist1) alist2 dot))
   ((equal (caar alist1) (caar alist2))
    (let ((dot (+ dot (* (cdar alist1) (cdar alist2)))))
      (dot-alist (cdr alist1) (cdr alist2) dot)))
   (t
    (dot-alist alist1 (cdr alist2) dot))))

(defun scale-alist (alist coeff)
  (if (not (consp alist)) nil
    (cons (cons (caar alist) (* coeff (cdar alist)))
          (scale-alist (cdr alist) coeff))))

(defun scale-and-add (alist1 alist2 coeff)
  (declare (xargs :measure (+ (len alist1) (len alist2))))
  (cond
   ((not (consp alist1))
    (scale-alist alist2 coeff))
   ((not (consp alist2)) 
    alist1)
   ((<< (caar alist1) (caar alist2))
    (cons (car alist1) (scale-and-add (cdr alist1) alist2 coeff)))
   ((equal (caar alist1) (caar alist2))
    (cons (cons (caar alist1) (+ (cdar alist1) (* coeff (cdar alist2))))
          (scale-and-add (cdr alist1) (cdr alist2) coeff)))
   (t
    (cons (car alist2) (scale-and-add alist1 (cdr alist2) coeff)))))

(defun dot-bases (b1 b2)
  (dot-alist (access poly b1 :alist) (access poly b2 :alist) 0))

(defun scale-and-add-base-to-sln (alist base coeff)
  (scale-and-add alist (access poly base :alist) coeff))

(defun scale-and-add-bases (b1 b2 coeff)
  (let* ((alist1  (access poly b1 :alist))
         (alist2  (access poly b2 :alist)))
    (make poly
          :constant 0
          :alist (scale-and-add alist1 alist2 coeff)
          :relation  '<=
          :ttree nil #+joe(cons-tag-trees (access poly b1 :ttree)
                                          (access poly b2 :ttree))
          :rational-poly-p (and (access poly b1 :rational-poly-p)
                                (access poly b2 :rational-poly-p))
          :parents nil #+joe(marry-parents (access poly b1 :parents)
                                           (access poly b2 :parents))
          :derived-from-not-equalityp nil)))

(defun score-poly (poly pstat)
  (dot-alist (access poly poly :alist) (access pstat pstat :sln) (access poly poly :constant)))

(defun score-list (kind list ref plist zlist nlist)
  (if (not (consp list)) (mv plist zlist nlist)
    (let ((poly (car list)))
      (let ((score (dot-alist (access poly poly :alist) ref (if (eq kind :polys) (access poly poly :constant) 0))))
        (cond
         ((< 0 score) (score-list kind (cdr list) ref (cons poly plist) zlist nlist))
         ((= 0 score) (score-list kind (cdr list) ref plist (cons poly zlist) nlist))
         (t           (score-list kind (cdr list) ref plist zlist (cons poly nlist))))))))

(defun insert-positive-poly (score poly plist)
  (declare (ignore score))
  (cons poly plist))

(defun poly-to-base (poly)
  (change poly poly 
          :relation '<=
          :constant 0))

(defun remove-negative-zbases-from-base (zbases mag base)
  (if (not (consp zbases)) base
    (let ((dot (dot-bases (car zbases) base)))
      (if (<= 0 dot) (remove-negative-zbases-from-base (cdr zbases) mag base)
        (let ((coeff (/ (- mag) dot)))
          ;; base * (base + coeff*ref) = 0
          ;; base^2 + coeff*base*ref = 0
          ;; coeff= (- base^2)/(base*ref)
          ;; coeff = (- mag)/dot
          (let ((base (scale-and-add-bases base (car zbases) coeff)))
            (remove-negative-zbases-from-base (cdr zbases) mag base)))))))

(defun zero-basep (base)
  (= (len (access poly base :alist)) 0))

(defun insert-zero-poly (poly zeros)
  (let ((originals (access zeros zeros :originals))
        (zbases    (access zeros zeros :zbases)))
    (let ((base (poly-to-base poly)))
      (let ((base (remove-negative-zbases-from-base zbases (self-dot base 0) base)))
        ;; Yeah .. so this would happen if any motion on the
        ;; vector would violate the existing zbases.
        (if (zero-basep base) (change zeros zeros :originals (cons poly originals))
          (make zeros 
                :originals (cons poly originals)
                :zbases    (cons base zbases)))))))

(defun insert-zero-poly-list (list zeros)
  (if (not (consp list)) zeros
    (insert-zero-poly-list (cdr list) (insert-zero-poly (car list) zeros))))

(defun unexpected (term)
  (cw "~x0~%" term))

(defun insert-negative-poly (poly pstat)
  (let ((zeros (access pstat pstat :zeros))
        (plist (access pstat pstat :plist))
        (sln   (access pstat pstat :sln)))
    (let ((originals (access zeros zeros :originals))
          (zbases    (access zeros zeros :zbases)))
      (let ((base (poly-to-base poly)))
        (met ((pzbases zzbases nzbases) (score-list :bases zbases (access poly base :alist) nil nil nil))
          (declare (ignore pzbases))
          (let ((base (remove-negative-zbases-from-base nzbases (self-dot base 0) base)))
            (let ((zbases (revappend zzbases nzbases)))
              ;; This is a contradiction .. we need to change the solution but we cannot ..
              (if (zero-basep base) (mv base nil pstat)
                (met ((new-plist originals empty) (score-list :bases originals (access poly base :alist) nil nil nil))
                  ;; This test should never succeed ..
                  (if (consp empty) (mv (unexpected "**ERROR**") pstat nil)
                    ;; (base * (sln + coeff*base)) = base*sln + coeff*base^2 = 0 
                    ;; coeff = (- base*sln)/base^2
                    (let ((coeff (/ (- (dot-alist (access poly base :alist) sln 0)) (self-dot base 0))))
                      (let ((sln (scale-and-add-base-to-sln sln base coeff)))
                        (met ((plist zlist0 nlist) (score-list :bases plist (access poly base :alist) new-plist nil nil))
                          (met ((plist zlist nlist) (score-list :polys nlist sln plist nil nil))
                            (let ((plist (revappend zlist0 plist))) 
                              (let ((zeros (make zeros 
                                                 :originals (cons poly originals)
                                                 :zbases    (cons base zbases))))
                                (let ((zeros (insert-zero-poly-list zlist zeros)))
                                  (let ((pstat (make pstat
                                                     :sln   sln
                                                     :zeros zeros
                                                     :plist plist)))
                                    (mv nil nlist pstat)))))))))))))))))))

;; zeros contains two lists:
;; - original polys
;; - basis polys (derived)

(defun dag-add-poly (poly pstat)
  (let ((score (score-poly poly pstat)))
    (if (< 0 score) (mv nil nil (change pstat pstat :plist (cons poly (access pstat pstat :plist))))
      (if (= 0 score) (mv nil nil (change pstat pstat :zeros (insert-zero-poly poly (access pstat pstat :zeros))))
        (insert-negative-poly poly pstat)))))

(defun dag-add-poly-list (polys pstat)
  (declare (xargs :mode :program))
  (if (not (consp polys)) (mv nil pstat)
    (met ((unsat new-polys pstat) (dag-add-poly (car polys) pstat))
      (if (not unsat) (dag-add-poly-list (revappend new-polys (cdr polys)) pstat)
        (mv unsat pstat)))))
