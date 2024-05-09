; A more abstract idiom for getting the length of an array1
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

;dup
(local
 (defthm equal-of-assoc-equal-same
  (implies key
           (iff (equal key (car (assoc-equal key array)))
                (assoc-equal key array)))
  :hints (("Goal" :in-theory (enable assoc-equal)))))

;; Get the length of a 1-d array.  We prefer this to (car (dimensions ...))
;; because car in many cases get rewritten to a call of nth.
(defund alen1 (name l)
  (declare (xargs :guard (array1p name l)))
  (car (dimensions name l)))

(defthmd normalize-alen1-name
  (implies (syntaxp (not (equal name '':fake-name)))
           (equal (alen1 name l)
                  (alen1 :fake-name l)))
  :hints (("Goal" :in-theory (enable alen1))))

;; Introduce alen1
(defthm alen1-intro
  (equal (car (dimensions array-name array))
         (alen1 array-name array))
  :hints (("Goal" :in-theory (enable alen1))))

(theory-invariant (incompatible (:rewrite alen1-intro) (:definition alen1)))

;; Introduce alen1
;; (car (dimensions ..)) can arise from the guard of aref1 and can then be turned into (nth 0 (dimensions ...))
(defthm alen1-intro2
  (equal (nth 0 (dimensions array-name array))
         (alen1 array-name array))
  :hints (("Goal" :in-theory (e/d (alen1) (alen1-intro)))))

(theory-invariant (incompatible (:rewrite alen1-intro2) (:definition alen1)))

(defthm alen1-of-compress1
  (equal (alen1 array-name (compress1 array-name2 array))
         (alen1 array-name array))
  :hints (("Goal" :in-theory (e/d (alen1) (alen1-intro alen1-intro2)))))

(defthm integerp-of-alen1-gen
  (implies (array1p array-name2 array) ;array-name2 is a free var
           (integerp (alen1 array-name array)))
  :hints (("Goal" :in-theory (e/d (alen1) (alen1-intro alen1-intro2)))))

;; no free vars
(defthm integerp-of-alen1
  (implies (array1p array-name array)
           (integerp (alen1 array-name array)))
  :hints (("Goal" :in-theory (disable array1p))))

(defthm posp-of-alen1
  (implies (array1p array-name2 array) ; array-name2 is a free var
           (posp (alen1 array-name array)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (e/d (alen1 array1p) (alen1-intro alen1-intro2)))))

;; ;todo: why is posp-of-alen1 above not sufficient?
;; (defthm alen1-type
;;   (implies (array1p name l)
;;            (posp (alen1 name l)))
;;   :rule-classes :type-prescription)

;; (defthm natp-of-alen1
;;   (implies (array1p name l)
;;            (natp (alen1 name l))))

(defthm alen1-of-cons
  (equal (alen1 array-name (cons entry alist))
         (if (eq :header (car entry))
             (car (cadr (assoc-keyword :dimensions (cdr entry))))
           (alen1 array-name alist)))
  :hints (("Goal" :in-theory (e/d (alen1)
                                  (alen1-intro alen1-intro2)))))

(defthm alen1-of-acons-of-header
  (equal (alen1 array-name (acons :header header alist))
         (car (cadr (assoc-keyword :dimensions header))))
  :hints (("Goal" :in-theory (enable acons))))

(defthm rationalp-of-alen1-when-array1p
  (implies (array1p array-name array)
           (rationalp (alen1 array-name array)))
  :hints (("Goal" :use (:instance integerp-of-alen1)
           :in-theory (disable integerp-of-alen1))))
