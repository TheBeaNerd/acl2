; A utility to check whether all values in a list are greater than a given value
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(defund all-> (x n)
  (declare (xargs :guard (and (rational-listp x)
                              (rationalp n))))
  (if (atom x)
      t
      (and (> (first x) n)
           (all-> (rest x) n))))

(defthm all->-of-cons
  (equal (all-> (cons a x) b)
         (and (> a b)
              (all-> x b)))
  :hints (("Goal" :in-theory (enable all->))))

(defthm all->-of-nil
  (all-> nil n)
  :hints (("Goal" :in-theory (enable all->))))

(defthm all->-of-cdr
  (implies (all-> x n)
           (all-> (cdr x) n))
  :hints (("Goal" :in-theory (enable all->))))
