(in-package "ACL2")

(defun poly-alist-to-expr (alist const)
  (if (not (consp alist)) `(quote ,const)
    (let ((entry (car alist)))
      (cond
       ((equal (cdr entry) 0)
        (poly-alist-to-expr (cdr alist) const))
       ((equal (cdr entry) 1)
        `(binary-+ ,(car entry)
                   ,(poly-alist-to-expr (cdr alist) const)))
       (t
        `(binary-+ (binary-* (quote ,(cdr entry)) ,(car entry))
                   ,(poly-alist-to-expr (cdr alist) const)))))))

(defun poly-to-expr (poly)
  (let* ((relation (access acl2::poly poly :relation))
         (const    (access acl2::poly poly :constant))
         (alist    (access acl2::poly poly :alist)))
    (case-match relation
      ('<  `(< (quote 0) ,(poly-alist-to-expr alist const)))
      (&   `(not (< ,(poly-alist-to-expr alist const) (quote 0)))))))
  
(defun poly-term-lst (poly-lst)
  (cond ((not (consp poly-lst)) nil)
        (t (cons (poly-to-expr (car poly-lst))
                 (poly-term-lst (cdr poly-lst))))))

(defun poly-pot (pot)
  (append
   (poly-term-lst (access acl2::linear-pot pot :negatives))
   (poly-term-lst (access acl2::linear-pot pot :positives))))

(defun poly-pot-lst (pot-list)
  (if (not (consp pot-list)) nil
    (append (poly-pot (car pot-list))
            (poly-pot-lst (cdr pot-list)))))

(defun show-poly-list (list)
  (declare (xargs :mode :program))
  (if (not (consp list)) nil
    (cons (show-poly (car list))
          (show-poly-list (cdr list)))))

(defun show-pot-lst (pot-lst)
  (declare (xargs :mode :program))
  (cond
   ((null pot-lst) nil)
   (t (cons
       (list* :var (access linear-pot (car pot-lst) :var)
              (append (show-poly-lst
                       (access linear-pot (car pot-lst) :negatives))
                      (show-poly-lst
                       (access linear-pot (car pot-lst) :positives))))
       (show-pot-lst (cdr pot-lst))))))


