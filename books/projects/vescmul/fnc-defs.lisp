; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "ihs/basic-definitions" :dir :system)

(include-book "misc/total-order" :dir :system)

(include-book "projects/rp-rewriter/top" :dir :system)

;;(include-book "centaur/svl/bits-sbits" :dir :system)

(include-book "centaur/svl/portcullis" :dir :system)

(include-book "centaur/svl/fnc-defs" :dir :system)

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(defconst *large-number*
  (expt 2 50))

(progn
  (define binary-sum (x y)
    (+ (ifix x)
       (ifix y))
    :returns (res integerp))

  (add-rp-rule integerp-of-binary-sum)

  (defmacro sum (&rest rp::rst)
    (cond ((null rp::rst) 0)
          ((null (cdr rp::rst))
           (list 'ifix (car rp::rst)))
          (t (xxxjoin 'binary-sum rp::rst))))

  (add-macro-fn sum binary-sum t))

(define -- (x)
  (- (ifix x)))

;; for backwards compatibility.
(defmacro bit-of (x pos)
  `(logbit$inline ,pos ,x))

(define sum-list (lst)
  (if (atom lst)
      0
    (sum (car lst)
         (sum-list (cdr lst))))
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-sum-list))

(define sum-list-list (lst)
  (if (atom lst)
      0
    (sum (sum-list (car lst))
         (sum-list-list (cdr lst))))
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-sum-list-list))

(define s (hash-code pp c)
  (declare (ignore hash-code))
  (mod (sum (sum-list pp)
            (sum-list c))
       2)
  :returns (res integerp)
  ///

  (local
   (use-arith-5 t))

  (defret bitp-of-s
    (bitp res)
    :hints (("Goal"
             :in-theory (e/d () (mod)))))
  (defret natp-of-s
    (natp res))

  (add-rp-rule bitp-of-s)
  (add-rp-rule natp-of-s)
  (add-rp-rule integerp-of-s))

(define c (hash-code s pp c)
  (declare (ignore hash-code))
  (floor (sum (sum-list s)
              (sum-list pp)
              (sum-list c))
         2)
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-c))

(define pp (term)
  :returns (res)
  term
  ///

  (defret integerp-of-<fn>
    (implies (integerp term)
             (integerp res)))

  (defret bitp-of-<fn>
    (implies (bitp term)
             (bitp res)))

  (add-rp-rule integerp-of-pp)
  (add-rp-rule bitp-of-pp))

#|(define d-sum (s-lst pp-lst c)
(sum (sum-list s-lst)
(sum-list pp-lst)
c)
:returns (res integerp)
///
(add-rp-rule integerp-of-d-sum))||#

#|(define d ((d-sum integerp))
(floor (sum d-sum (-- (mod (ifix d-sum) 2))) 2)
:returns (res integerp)
///
(add-rp-rule integerp-of-d))||#

(define s-spec (lst)
  (mod (sum-list lst) 2)
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-s-spec))

(define d-spec (lst)
  (/ (sum-list lst) 2))

(define c-spec (lst)
  (floor (sum-list lst) 2)
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-c-spec))

(define s-c-spec (lst)
  (list (s-spec lst)
        (c-spec lst)))

(define c-s-spec (lst)
  (list (c-spec lst)
        (s-spec lst)))

(define s-c-res (s-lst pp-lst c-lst)
  (sum (sum-list pp-lst)
       (sum-list s-lst)
       (sum-list c-lst))
  :returns (res integerp)
  ///
  (add-rp-rule integerp-of-s-c-res))

#|(define d-new (s pp c/d new)
(sum (c-new s pp c/d new)
(-- (mod (+ (sum-list s)
(sum-list pp)
(sum-list c/d)
(sum-list new))
2)))
:returns (res integerp)
///
(add-rp-rule integerp-of-d-new))||#

(define bit-fix (x)
  (if (bitp x)
      x
    0)
  ///
  (def-rp-rule bit-fix-opener
    (implies (bitp x)
             (equal (bit-fix x) x))))

(define bit-listp (lst)
  (if (atom lst)
      (equal lst nil)
    (and (bitp (car lst))
         (bit-listp (cdr lst)))))

(define bit-fix-lst (lst)
  (if (atom lst)
      nil
    (cons (bit-fix (car lst))
          (bit-fix-lst (cdr lst))))
  ///
  (defthm bit-fix-lst-opener
    (implies (bit-listp lst)
             (equal (bit-fix-lst lst)
                    lst))
    :hints (("Goal"
             :in-theory (e/d (bit-listp) ())))))

(define binary-not (bit)
  (- 1 (bit-fix bit))
  ///
  (def-rp-rule natp-bitp-binary-not
    (and (bitp (binary-not x))
         (natp (binary-not x)))
    :hints (("Goal"
             :in-theory (e/d (binary-not bitp) ())))))

(defmacro not$ (term)
  `(binary-not ,term))

(add-macro-fn not$ binary-not t)

(define binary-and (bit1 bit2)
  (if (and (equal (bit-fix bit1) 1)
           (equal (bit-fix bit2) 1))
      1
    0)
  ///
  (def-rp-rule bitp-binary-and
    (and (bitp (binary-and x y))
         (natp (binary-and x y)))))

(defmacro and$ (&rest rp::rst)
  (cond ((null rp::rst) 0)
        ((null (cdr rp::rst))
         (list 'bit-fix (car rp::rst)))
        (t (xxxjoin 'binary-and rp::rst))))

(add-macro-fn and$ binary-and t)

(define and-list (hash-code lst)
  (declare (ignorable hash-code))
  (if (atom lst)
      1
    (if (atom (cdr lst))
        (and$ (car lst) 1)
      (and$ (car lst)
            (and-list hash-code (cdr lst)))))
  ///
  (def-rp-rule bitp-and-list
    (and (bitp (and-list hash y))
         (natp (and-list hash y)))))

(define and-times-list (hash-code lst s/c)
  (declare (ignorable hash-code))
  (* (ifix s/c)
     (and-list hash-code lst)))

(define binary-or (bit1 bit2)
  (if (and (equal (bit-fix bit1) 0)
           (equal (bit-fix bit2) 0))
      0
    1)
  ///

  (def-rp-rule bitp-binary-or
    (and (bitp (binary-or x y))
         (natp (binary-or x y)))))

(defmacro or$ (&rest rp::rst)
  (cond ((null rp::rst) 0)
        ((null (cdr rp::rst))
         (list 'bit-fix (car rp::rst)))
        (t (xxxjoin 'binary-or rp::rst))))

(add-macro-fn or$ binary-or t)

(define binary-xor (bit1 bit2)
  (if (equal (bit-fix bit1) (bit-fix bit2))
      0
    1)
  ///
  (def-rp-rule bitp-binary-xor
    (and (bitp (binary-xor x y))
         (natp (binary-xor x y)))))

(define binary-? (test x y)
  (if (equal (bit-fix test) 1)
      (bit-fix x)
    (bit-fix y))
  ///
  (def-rp-rule natp-bitp-binary-?*
    (and (natp (binary-? test x y))
         (bitp (binary-? test x y)))))

(defun binary-cond-macro (clauses)
  (declare (xargs :guard (cond-clausesp clauses)))
  (if (consp clauses)
      (if (and (eq (car (car clauses)) t)
               (eq (cdr clauses) nil))
          (if (cdr (car clauses))
              (car (cdr (car clauses)))
            (car (car clauses)))
        (if (cdr (car clauses))
            (list 'binary-?
                  (car (car clauses))
                  (car (cdr (car clauses)))
                  (binary-cond-macro (cdr clauses)))
          (list 'or$
                (car (car clauses))
                (binary-cond-macro (cdr clauses)))))
    nil))

(defmacro binary-cond (&rest acl2::clauses)
  (declare (xargs :guard (cond-clausesp acl2::clauses)))
  (binary-cond-macro acl2::clauses))

(define sort-sum (x)
  ;; trigger function to be used by a meta to sort and convert (sum d b a c)
  ;; (sum-list (list a b c d))
  (ifix x))

(define s-of-c-trig (x)
  x
  ///
  (add-rp-rule s-of-c-trig))

(define evenpi (term)
  (evenp (ifix term)))

(define small-alphorder ((x)
                         (y))
  (cond ((symbolp x)
         (cond ((symbolp y)
                (symbol< x y))
               (t nil)))
        ((integerp x)
         (cond ((integerp y)
                (< x y))
               (t (symbolp y))))
        (t
         nil))
  ///

  (defthm small-alphorder-sanity
    (implies (and (small-alphorder a b))
             (not (small-alphorder b a)))
    :hints (("Goal"
             :in-theory (e/d (ACL2::BAD-ATOM<= alphorder) ())))))

(encapsulate
  nil

  (local
   (in-theory (enable measure-lemmas)))

  (defun lexorder2 (x y)
    ;; returns (mv order equal-x-y)
    (declare (xargs :guard t
                    :measure (+ (cons-count x) (cons-count y))))
    (let ((x (ex-from-rp-loose x))
          (y (ex-from-rp-loose y)))
      (cond ((atom x)
             (cond
              ((atom y)
               (if (equal x y)
                   (mv nil t)
                 (mv (small-alphorder x y)
                     #|(or (equal x nil)
                     (and (small-alphorder x y) ;
                     (not (equal y nil))))||#
                     nil)))
              (t
               (b* (((mv order-res &) (lexorder2 x (car y))))
                 (mv order-res nil)))))
            ((atom y)
             (b* (((mv order-res &) (lexorder2 (car x) y)))
               (mv order-res nil)))
            ((or (equal (car x) (car y)))
             (lexorder2 (cdr x) (cdr y)))
            (t (b* (((mv order-res equal-x-y)
                     (lexorder2 (car x) (car y))))
                 (if equal-x-y
                     (lexorder2 (cdr x) (cdr y))
                   (mv order-res nil)))))))

  (defun lexorder2- (x y)
    (declare (xargs :guard t))
    (b* (((mv x-logbit-p x-var x-index)
          (case-match x (('acl2::logbit$inline index var) (mv t var index)) (& (mv nil nil nil))))
         ((mv y-logbit-p y-var y-index)
          (case-match y (('acl2::logbit$inline index var) (mv t var index)) (& (mv nil nil nil))))
         ((when (or* x-logbit-p
                     y-logbit-p))
          (cond ((and* x-logbit-p
                       y-logbit-p)
                 (if (equal x-var y-var)
                     (not (lexorder y-index x-index))
                   (not (lexorder y-var x-var))))
                (t x-logbit-p)))
         ((mv order &)
          (lexorder2 x y)))
      order))

  (encapsulate
    nil

    (defthmd lexorder2-sanity-lemma1
      (implies (equal x y)
               (NOT (MV-NTH 0
                            (LEXORDER2 x y))))
      :hints (("Goal"
               :induct (LEXORDER2 X y)
               :in-theory (e/d () ()))))

    (defthmd lexorder2-sanity-lemma2
      (implies (MV-NTH 1 (LEXORDER2 x y))
               (not (MV-NTH 0 (LEXORDER2 x y)))))

    (defthmd lexorder2-sanity-lemma3
      (implies (MV-NTH 1 (LEXORDER2 x y))
               (MV-NTH 1 (LEXORDER2 y x))))

    (defthmd
      lexorder2-sanity
      (implies (MV-NTH 0 (LEXORDER2 X Y))
               (NOT (MV-NTH 0 (LEXORDER2 Y X))))
      :otf-flg t
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp-loose
                                lexorder2-sanity-lemma3
                                lexorder2-sanity-lemma2
                                is-rp
                                lexorder2-sanity-lemma1) ()))))))

(define adder-b+ ((x )
                  (y ))
  (+ (ifix x)
     (ifix y)))

(define adder-mux ((select bitp)
                   (i0 bitp)
                   (i1 bitp))
  :returns (res bitp)
  (if (equal (bit-fix select) 0)
      (bit-fix i0)
    (bit-fix i1))
  ///
  (add-rp-rule bitp-of-adder-mux))

(defmacro adder-sum (&rest rst)
  (cond ((null rst) 0)
        ((null (cdr rst))
         (list 'adder-b+ (car rst) 0))
        (t (xxxjoin 'adder-b+ rst))))

(add-macro-fn adder-sum adder-b+ t)

(defthm bitp-of-logbit
  (bitp (logbit x y)))

(add-rp-rule bitp-of-logbit)

#|(define medw-compress (term)
term
///
(add-rp-rule medw-compress :disabled nil))||#

(define unpack-booth (term)
  (ifix term)
  ///
  (add-rp-rule unpack-booth :disabled nil))

(rp::def-rw-opener-error
  s-spec-opener-error
  (rp::s-spec x))

(rp::def-rw-opener-error
  c-spec-opener-error
  (rp::c-spec x))

(rp::def-rw-opener-error
  s-c-spec-opener-error
  (rp::s-c-spec x))

(rp::def-rw-opener-error
  c-s-spec-opener-error
  (rp::c-s-spec x))

(rp::def-rw-opener-error
  sort-sum-opener-error
  (sort-sum x))

;; for proofs:
(define m2 (x)
  (mod (ifix x) 2))

(define f2 (x)
  (floor (ifix x) 2))

(define d2 (x)
  (f2 (sum x (-- (m2 x)))))

(define times2 (x)
  (sum x x))

(define quarternaryp (term)
  :inline t
  (or (equal term 0)
      (equal term 1)
      (equal term 2)
      (equal term 3)))

(define ba2 (n1 i1 n2 i2)
  :verify-guards nil
  (and$ (logbit n1 i1)
        (logbit n2 i2))
  ///
  (def-rp-rule bitp-ba2
    (bitp (ba2 n1 i1 n2 i2))))

(define ba3 (n1 i1 n2 i2 n3 i3)
  :verify-guards nil
  (and$ (logbit n1 i1)
        (logbit n2 i2)
        (logbit n3 i3))
  ///
  (def-rp-rule bitp-ba3
    (bitp (ba3 n1 i1 n2 i2 n3 i3))))

(define ba4 (n1 i1 n2 i2 n3 i3 n4 i4)
  :verify-guards nil
  (and$ (logbit n1 i1)
        (logbit n2 i2)
        (logbit n3 i3)
        (logbit n4 i4))
  ///
  (def-rp-rule bitp-ba4
    (bitp (ba4 n1 i1 n2 i2 n3 i3 n4 i4))))

(define safe-i-nth ((i natp)
                    lst)
  (if (atom lst)
      0
    (if (zp i)
        (car lst)
      (safe-i-nth (1- i) (cdr lst)))))

(progn
  (define list-to-lst (term)
    :returns (lst rp-term-listp
                  :hyp (rp-termp term))
    :prepwork ((local
                (in-theory (enable rp-termp
                                   rp-term-listp))))
    (case-match term
      (('list . lst) lst)
      (''nil nil)
      (& (or (hard-error 'list-instance-to-lst
                         "Unexpected list instance: ~p0 ~%"
                         (list (cons #\0 term)))
             (list `(sum-list ,term))))))

  (define create-list-instance (lst)
    :returns (res rp-termp :hyp (rp-term-listp lst))
    (cond ((or (Not lst)
               (equal lst (list ''0)))
           ''nil)
          #|((quote-listp lst)
          `',(unquote-all lst))||#
          (t
           `(list . ,lst)))))

(defsection times
  (define times (coef term)
    (* (ifix coef)
       (ifix term))
    ///
    (def-rp-rule integerp-and-list
      (integerp (times coef term))))

  (define times-p (term)
    (case-match term
      (('times ('quote coef) &)
       (integerp coef)))
    ///
    (defthm times-p-implies
      (implies (times-p term)
               (and (case-match term
                      (('times ('quote coef) &)
                       (integerp coef)))
                    ;; (equal (rp-trans (cadr term))
                    ;;        (cadr term))
                    ))
               :rule-classes ((:forward-chaining)))
    ;; (defthm times-p-implies-2
    ;;   (implies (times-p term)
    ;;            (quotep (cadr term)))
    ;;   :rule-classes (:type-prescription))
    )

  (define get-pp-and-coef (term)
    :inline t
    :returns (mv (coef integerp :rule-classes (:type-prescription :rewrite))
                 (res-term rp-termp :hyp (rp-termp term)))
    (cond ((times-p term)
           (mv (ifix (cadr (cadr term))) (caddr term)))
          (t (mv 1  term))))
   ;; (case-match term (('times ('quote coef) a) (mv (ifix coef) a)) (& (mv 1  term))))

  (define create-times-instance ((coef integerp)
                                 term)
    :returns (res rp-termp :hyp (and (rp-termp term)))
    (cond ((= coef 0) ''0)
          ((= coef 1) term)
          (t (case-match term
               (('times ('quote c2) term)
                (b* ((new-coef (* (ifix c2) (mbe :exec coef :logic (ifix coef)))))
                `(times ',new-coef 
                        ,term)))
               (& `(times ',coef ,term))))))

  (define cons-with-times ((coef integerp) term rest)
    :returns (res-lst rp-term-listp :hyp (and (rp-termp term)
                                              (rp-term-listp rest)))
    :inline t
    (if (= coef 0)
        rest
      (cons (create-times-instance coef term) rest)))

  (define append-with-times-aux ((coef integerp) term-lst rest)
    :returns (res-lst rp-term-listp :hyp (and (rp-term-listp rest)
                                              (rp-term-listp term-lst)))
    (if (atom term-lst)
        rest 
      (cons ;;`(times ',coef ,(car term-lst))
            (create-times-instance coef (car term-lst))
            (append-with-times-aux coef (cdr term-lst) rest))))

  (define append-with-times ((coef integerp)
                             (term-lst)
                             rest)
    :guard (or (true-listp term-lst)
               (not rest))
    :returns (res-lst rp-term-listp :hyp (and (rp-term-listp rest)
                                              (rp-term-listp term-lst)))
    :inline t
    (cond ((= coef 0) rest)
          ((and (= coef 1)
                (not rest))
           term-lst)
          ((= coef 1)
           (append term-lst rest))
          (t (append-with-times-aux coef term-lst rest)))))


(progn
  (encapsulate
    (((unpack-booth-later-enabled) => *))
    (local
     (defun unpack-booth-later-enabled ()
       nil)))

  (define return-t ()
    t)
  (define return-nil ()
    nil)

  (defmacro enable-unpack-booth-later (enable)
    (if enable
        `(defattach unpack-booth-later-enabled return-t)
      `(defattach unpack-booth-later-enabled return-nil)))

  (enable-unpack-booth-later nil))

(acl2::defines
  m-eval
  (define m-eval (term a)
    (cond ((atom term)
           (cdr (hons-assoc-equal term a)))
          ((and (quotep term)
                (consp (cdr term)))
           (unquote term))
          (t
           (b* ((args (m-eval-lst (cdr term) a)))
             (cond ((equal (car term) 's)
                    (s (safe-i-nth 0 args)
                       (safe-i-nth 1 args)
                       (safe-i-nth 2 args)))
                   ((equal (car term) 'c)
                    (c (safe-i-nth 0 args)
                       (safe-i-nth 1 args)
                       (safe-i-nth 2 args)
                       (safe-i-nth 3 args)))
                   ((equal (car term) 's-c-res)
                    (s-c-res (safe-i-nth 0 args)
                             (safe-i-nth 1 args)
                             (safe-i-nth 2 args)))
                   ((equal (car term) 'binary-and)
                    (and$ (safe-i-nth 0 args)
                          (safe-i-nth 1 args)))
                   ((equal (car term) 'binary-xor)
                    (binary-xor (safe-i-nth 0 args)
                                (safe-i-nth 1 args)))
                   ((equal (car term) 'binary-or)
                    (binary-or (safe-i-nth 0 args)
                               (safe-i-nth 1 args)))
                   ((equal (car term) 'binary-sum)
                    (sum (safe-i-nth 0 args)
                         (safe-i-nth 1 args)))
                   ((equal (car term) 'equal)
                    (equal (safe-i-nth 0 args)
                           (safe-i-nth 1 args)))
                   ((equal (car term) 'cons)
                    (cons (safe-i-nth 0 args)
                          (safe-i-nth 1 args)))
                   ((equal (car term) 's-c-spec)
                    (s-c-spec (safe-i-nth 0 args)))
                   ((equal (car term) 'binary-not)
                    (not$ (safe-i-nth 0 args)))
                   ((equal (car term) 'and-list)
                    (and-list (safe-i-nth 0 args)
                              (safe-i-nth 1 args)))
                   ((equal (car term) 'sum-list)
                    (sum-list (safe-i-nth 0 args)))
                   ((equal (car term) 'sum-list-list)
                    (sum-list-list (safe-i-nth 0 args)))
                   ((equal (car term) 'rp)
                    (safe-i-nth 1 args))
                   ((equal (car term) 'logbit$inline)
                    (logbit
                     (nfix (safe-i-nth 0 args))
                     (ifix (safe-i-nth 1 args))))
                   ((equal (car term) '--)
                    (--
                     (safe-i-nth 0 args)))
                   ((equal (car term) 'times)
                    (times
                     (safe-i-nth 0 args)
                     (safe-i-nth 1 args)))
                   ((equal (car term) 's-spec)
                    (s-spec
                     (safe-i-nth 0 args)))
                   ((equal (car term) 'c-spec)
                    (c-spec
                     (safe-i-nth 0 args)))
                   ((equal (car term) 'list)
                    args)
                   ((equal (car term) 'sum)
                    (sum-list args))
                   (t
                    (hard-error 'm-eval
                                "unexpected function symbol: ~p0 ~%"
                                (list (cons #\0 (car term))))))))))
  (define m-eval-lst (lst a)
    (if (atom lst)
        nil
      (cons (m-eval (car lst) a)
            (m-eval-lst (cdr lst) a)))))

(define m-eval-lst-lst (lst-lst a)
  (and nil
       (if (atom lst-lst)
           nil
         (cons (m-eval-lst (car lst-lst) a)
               (m-eval-lst-lst (cdr lst-lst) a)))))

(define m-eval-compare (exp1 exp2 &key
                             (a '*a*)
                             (id '0)
                             (print-exps 'nil))
  (and nil
       (b* ((eval1 (m-eval exp1 a))
            (eval2 (m-eval exp2 a)))
         (and (not (equal eval1 eval2))
              (not (cw "ID: ~p0, eval1: ~p1, eval2: ~p2 ~%" id eval1 eval2))
              (or (not print-exps)
                  (not (cw "exp1: ~p0, exp2: ~p1 ~%"
                           exp1 exp2)))
              (hard-error 'm-eval-compare
                          "Read above.."
                          nil)))))

(mutual-recursion
 (defun count-fnc (term fnc)
   (declare (xargs :guard (symbolp fnc)
                   :verify-guards nil))
   (if (or (atom term) (quotep term))
       0
     (+ (if (eq (car term) fnc)
            1
          0)
        (count-fnc-subterms (cdr term)
                            fnc))))

 (defun count-fnc-subterms (subterms fnc)
   (declare (xargs :guard (symbolp fnc)))
   (if (atom subterms)
       0
     (+ (count-fnc (car subterms) fnc)
        (count-fnc-subterms (cdr subterms)
                            fnc)))))

(progn
  (define s-c-res-p (term)
    :inline t
    (case-match term (('s-c-res & & &) t))
    ///
    (defthm s-c-res-p-implies-fc
      (implies (s-c-res-p term)
               (case-match term (('s-c-res & & &) t)))
      :rule-classes :forward-chaining))

  (define single-c-p (term)
    :inline t
    (case-match term (('c & & & &) t))
    ///
    (defthm single-c-p-implies-fc
      (implies (single-c-p term)
               (case-match term (('c & & & &) t)))
      :rule-classes :forward-chaining))

  (define --.p (term)
    :inline t
    (case-match term (('-- &) t))
    ///
    (defthm --.p-implies-fc
      (implies (--.p term)
               (case-match term (('-- &) t)))
      :rule-classes :forward-chaining))

  (define single-s-p (term)
    :inline t
    (case-match term (('s & & &) t))
    ///
    (defthm single-s-p-implies-fc
      (implies (single-s-p term)
               (case-match term (('s & & &) t)))
      :rule-classes :forward-chaining))

  (define single-s-c-res-p (term)
    :inline t
    (case-match term (('s-c-res & & &) t))
    ///
    (defthm single-c-res-p-implies-fc
      (implies (single-s-c-res-p term)
               (case-match term (('s-c-res & & &) t)))
      :rule-classes :forward-chaining))

  (define sum-list-p (term)
    :inline t
    (case-match term (('sum-list &) t))
    ///
    (defthm sum-list-p-implies-fc
      (implies (sum-list-p term)
               (case-match term (('sum-list &) t)))
      :rule-classes :forward-chaining))

  (define and-list-p (term)
    :inline t
    (case-match term (('and-list & &) t))
    ///
    (defthm and-list-p-implies-fc
      (implies (and-list-p term)
               (case-match term (('and-list & &) t)))
      :rule-classes :forward-chaining))

  (define and-times-list-p (term)
    :inline t
    (case-match term (('and-times-list & & &) t))
    ///
    (defthm and-times-list-p-implies-fc
      (implies (and-times-list-p term)
               (case-match term (('and-times-list & & &) t)))
      :rule-classes :forward-chaining))

  (define quote-p (term)
    :inline t
    (case-match term (('quote &) t))
    ///
    (defthm quote-p-implies-fc
      (implies (quote-p term)
               (case-match term (('quote &) t)))
      :rule-classes :forward-chaining))

  (define binary-sum-p (term)
    :inline t
    (case-match term (('binary-sum & &) t))
    ///
    (defthm binary-sum-p-implies-fc
      (implies (binary-sum-p term)
               (case-match term (('binary-sum & &) t)))
      :rule-classes :forward-chaining))

  (define adder-sum-p (term)
    :inline t
    (case-match term (('adder-b+ & &) t))
    ///
    (defthm adder-sum-p-implies-fc
      (implies (adder-sum-p term)
               (case-match term (('adder-b+ & &) t)))
      :rule-classes :forward-chaining))

  (define binary-or-p (term)
    :inline t
    (case-match term (('binary-or & &) t))
    ///
    (defthm binary-or-p-implies-fc
      (implies (binary-or-p term)
               (case-match term (('binary-or & &) t)))
      :rule-classes :forward-chaining)
    (defthm binary-or-p-implies-length-fc
      (implies (binary-or-p term)
               (case-match term ((& & &) t)))
      :rule-classes :forward-chaining)
    (defthm binary-or-p-transient
      (implies (binary-or-p term)
               (binary-or-p `(,(car term) ,x ,y))))
    (defthm binary-or-p-bad-arg-length
      (and (not (binary-or-p `(,fn ,x)))
           (not (binary-or-p `(,fn ,x ,y ,z)))))
    (defthm binary-or-p-of-binary-or
      (equal (binary-or-p (cons 'binary-or y))
             (let ((term (cons 'binary-or y)))
               (case-match term (('binary-or & &) t))))
      :hints (("Goal"
               :in-theory (e/d (binary-or-p) ())))))

  (define binary-and-p (term)
    :inline t
    (case-match term (('binary-and & &) t))
    ///
    (defthm binary-and-p-implies-fc
      (implies (binary-and-p term)
               (case-match term (('binary-and & &) t)))
      :rule-classes :forward-chaining)
    (defthm binary-and-p-implies-length-fc
      (implies (binary-and-p term)
               (case-match term ((& & &) t)))
      :rule-classes :forward-chaining)
    (defthm binary-and-p-transient
      (implies (binary-and-p term)
               (binary-and-p `(,(car term) ,x ,y))))
    (defthm binary-and-p-bad-arg-length
      (and (not (binary-and-p `(,fn ,x)))
           (not (binary-and-p `(,fn ,x ,y ,z)))))
    (defthm binary-and-p-of-binary-and
      (equal (binary-and-p (cons 'binary-and y))
             (let ((term (cons 'binary-and y)))
               (case-match term (('binary-and & &) t))))
      :hints (("goal"
               :in-theory (e/d (binary-and-p) ())))))

  (define binary-xor-p (term)
    :inline t
    (case-match term (('binary-xor & &) t))
    ///
    (defthm binary-xor-p-implies-fc
      (implies (binary-xor-p term)
               (case-match term (('binary-xor & &) t)))
      :rule-classes :forward-chaining)
    (defthm binary-xor-p-implies-length-fc
      (implies (binary-xor-p term)
               (case-match term ((& & &) t)))
      :rule-classes :forward-chaining)
    (defthm binary-xor-p-transient
      (implies (binary-xor-p term)
               (binary-xor-p `(,(car term) ,x ,y))))
    (defthm binary-xor-p-bad-arg-length
      (and (not (binary-xor-p `(,fn ,x)))
           (not (binary-xor-p `(,fn ,x ,y ,z)))))
    (defthm binary-xor-p-of-binary-xor
      (equal (binary-xor-p (cons 'binary-xor y))
             (let ((term (cons 'binary-xor y)))
               (case-match term (('binary-xor & &) t))))
      :hints (("goal"
               :in-theory (e/d (binary-xor-p) ())))))

  (define binary-?-p (term)
    :inline t
    (case-match term (('binary-? & & &) t))
    ///
    (defthm binary-?-p-implies-fc
      (implies (binary-?-p term)
               (case-match term (('binary-? & & &) t)))
      :rule-classes :forward-chaining)
    (defthm binary-?-p-implies-length-fc
      (implies (binary-?-p term)
               (case-match term ((& & & &) t)))
      :rule-classes :forward-chaining)
    (defthm binary-?-p-transient
      (implies (binary-?-p term)
               (binary-?-p `(,(car term) ,x ,y ,z))))
    (defthm binary-?-p-bad-arg-length
      (and (not (binary-?-p `(,fn ,x ,y)))
           (not (binary-?-p `(,fn ,x)))))
    (defthm binary-?-p-of-binary-?
      (equal (binary-?-p (cons 'binary-? y))
             (let ((term (cons 'binary-? y)))
               (case-match term (('binary-? & & &) t))))
      :hints (("goal"
               :in-theory (e/d (binary-?-p) ())))))

  (define binary-not-p (term)
    :inline t
    (case-match term (('binary-not &) t))
    ///
    (defthm binary-not-p-implies-fc
      (implies (binary-not-p term)
               (case-match term (('binary-not &) t)))
      :rule-classes :forward-chaining)
    (defthm binary-not-p-implies-length-fc
      (implies (binary-not-p term)
               (case-match term ((& &) t)))
      :rule-classes :forward-chaining)
    (defthm binary-not-p-transient
      (implies (binary-not-p term)
               (binary-not-p `(,(car term) ,x))))
    (defthm binary-not-p-bad-arg-length
      (and (not (binary-not-p `(,fn ,x ,y)))
           (not (binary-not-p `(,fn ,x ,y ,z)))))
    (defthm binary-not-p-of-binary-not
      (equal (binary-not-p (cons 'binary-not y))
             (let ((term (cons 'binary-not y)))
               (case-match term (('binary-not &) t))))
      :hints (("goal"
               :in-theory (e/d (binary-not-p) ())))))

  (define binary-fnc-p (term)
    :inline t
    (or (binary-or-p term)
        (binary-and-p term)
        (binary-xor-p term)
        (binary-?-p term)
        (binary-not-p term))
    ///
    (defthm binary-fnc-p-implies-fc
      (implies (binary-fnc-p x)
               (and (consp x)
                    (true-listp x)
                    (not (equal (car x) 'quote))
                    (not (equal (car x) 'falist))
                    (SYMBOLP (CAR x))
                    (CAR x)))
      :rule-classes :forward-chaining)

    (defthm binary-fnc-p-relieve
      (implies (OR (BINARY-OR-P TERM)
                   (BINARY-AND-P TERM)
                   (BINARY-XOR-P TERM)
                   (BINARY-?-P TERM)
                   (BINARY-NOT-P TERM))
               (binary-fnc-p term))
      :hints (("Goal"
               :in-theory (e/d (binary-fnc-p) ())))))

  (define logbit-p (term)
    :inline t
    (case-match term (('logbit$inline & &) t))
    ///
    (defthm logbit-p-implies-fc
      (implies (logbit-p term)
               (case-match term (('logbit$inline & &) t)))
      :rule-classes :forward-chaining))

  (define bit-fix-p (term)
    :inline t
    (case-match term (('bit-fix &) t))
    ///
    (defthm bit-fix-p-implies-fc
      (implies (bit-fix-p term)
               (case-match term (('bit-fix &) t)))
      :rule-classes :forward-chaining))

  (define adder-or-p (term)
    :inline t
    (case-match term (('adder-or & &) t))
    ///
    (defthm adder-or-p-implies-fc
      (implies (adder-or-p term)
               (case-match term (('adder-or & &) t)))
      :rule-classes :forward-chaining))

  (define adder-and-p (term)
    :inline t
    (case-match term (('adder-and & &) t))
    ///
    (defthm adder-and-p-implies-fc
      (implies (adder-and-p term)
               (case-match term (('adder-and & &) t)))
      :rule-classes :forward-chaining))

  (define f2-p (term)
    :inline t
    (case-match term (('f2 &) t))
    ///
    (defthm f2-p-implies-fc
      (implies (f2-p term)
               (case-match term (('f2 &) t)))
      :rule-classes :forward-chaining))

  (define m2-p (term)
    :inline t
    (case-match term (('m2 &) t))
    ///
    (defthm m2-p-implies-fc
      (implies (m2-p term)
               (case-match term (('m2 &) t)))
      :rule-classes :forward-chaining))

  (define pp-p (term)
    :inline t
    (case-match term (('pp &) t))
    ///
    (defthm pp-p-implies-fc
      (implies (pp-p term)
               (case-match term (('pp &) t)))
      :rule-classes :forward-chaining)))

(define make-readable-4vec-concat-aux (term)
  :mode :program
  (case-match term
    (('svl::4vec-concat$ ''1 this rest)
     (cons this
           (make-readable-4vec-concat-aux rest)))
    (('svl::4vec-concat ''1 this rest)
     (cons this
           (make-readable-4vec-concat-aux rest)))
    (('svl::4vec-concat$ 1 this rest)
     (cons this
           (make-readable-4vec-concat-aux rest)))
    (('svl::4vec-concat 1 this rest)
     (cons this
           (make-readable-4vec-concat-aux rest)))
    (& term)))

(acl2::defines
  make-readable1
  :mode :program
  (define make-readable1 (term)
    (case-match term
      (('rp & term)
       (make-readable1 term))
      (('equal x y)
       `(equal ,(make-readable1 x) ,(make-readable1 y)))
      (('s & pp c)
       `(ss . ,(append (make-readable1 pp) (make-readable1 c))))
      (('s pp c)
       `(ss . ,(append (make-readable1 pp) (list (make-readable1 c)))))
      (('c & s pp c)
       `(cc . ,(append (make-readable1 s) (make-readable1 pp) (make-readable1 c))))
      (('c s pp c)
       `(cc . ,(append (make-readable1 s) (make-readable1 pp) (list (make-readable1 c)))))
      (('-- term)
       `(-- ,(make-readable1 term)))
      (('times ('quote coef) term)
       `(times ,coef ,(make-readable1 term)))
      (('list . lst)
       (make-readable1-lst lst))
      (('quote a)
       a)
      (('d ('rp ''evenpi ('d-sum s pp c)))
       `(dd . ,(append (make-readable1 s) (make-readable1 pp) (list (make-readable1 c)))))
      (('cons a b)
       (cons (make-readable1 a)
             (make-readable1 b)))
      #|(('binary-and & &)
      term)||#
      (('binary-and ('logbit$inline ('quote i) a) ('logbit$inline ('quote j) b))
       (progn$
;(cw "term~p0 ~%" term)
        (b* ((a (ex-from-rp-loose a))
             (a (if (equal a 'in1) 'a a))
             (b (ex-from-rp-loose b))
             (b (if (equal b 'in2) 'b b)))
;`(rp 'bitp
          `   ,(sa (symbol-name a) i (symbol-name b) j)
;    )
              )))
      (('and-list & x)
       `(and$ ,@(make-readable1 x)))
      (('logbit$inline ('quote n) x)
       `(bit ,n ,(make-readable1 x)))

      (('svl::4vec-concat$ 1 & &)
       `(4list . ,(make-readable1-lst (make-readable-4vec-concat-aux term))))
      (('svl::4vec-concat$ ''1 & &)
       `(4list . ,(make-readable1-lst (make-readable-4vec-concat-aux term))))

      (&
       (cond ((binary-fnc-p term)
              `(,(car term) "..."))
             ((atom term)
              term)
             (t
              `(,(car term) . ,(make-readable1-lst (cdr term))))))))
  (define make-readable1-lst (lst)
    (if (atom lst)
        nil
      (cons (make-readable1 (car lst))
            (make-readable1-lst (cdr lst))))))

(define str-cat-lst ((lst string-listp))
  (if (atom lst)
      ""
    (str::cat (car lst)
              (if (atom (cdr lst)) "" "-")
              (str-cat-lst (cdr lst)))))

(acl2::defines
  make-readable
  :verify-guards nil
  (define make-readable (term)
    (declare (xargs :mode :program))
    (b* ((term (ex-from-rp-loose term)))
      (case-match term
        (('equal a b)
         `(equal ,(make-readable a)
                 ,(make-readable b)))
        (('s hash pp c)
         (b* ((pp-lst (make-readable-lst (list-to-lst pp)))
              (c-lst (make-readable-lst (list-to-lst c))))
           `(s (,hash). ,(append pp-lst c-lst))))
        (('c hash s pp c)
         (b* ((s-lst (make-readable-lst (list-to-lst s)))
              (pp-lst (make-readable-lst (list-to-lst pp)))
              (c-lst (make-readable-lst (list-to-lst c))))
           `(c (,hash) . ,(append s-lst pp-lst c-lst))))
        (('-- n)
         `(-- ,(make-readable n)))
        (('times ('quote coef) n)
         `(times ,coef ,(make-readable n)))
        (''1
         1)
        (('and-list & bits)
         (b* ((lst (make-readable-lst (list-to-lst bits)))
              (str (str-cat-lst lst))
              (sym (intern$ str "RP")))
           sym))
        (('logbit$inline ('quote index) name)
         (b* ((sym (sa  (ex-from-rp-loose name) index)))
           (symbol-name sym)))
        (('logbit$inline index name)
         (b* ((sym (sa  (ex-from-rp-loose name) index)))
           (symbol-name sym)))
        (('binary-and x y)
         `(and$ ,(make-readable x) ,(make-readable y)))
        (('binary-or x y)
         `(or$ ,(make-readable x) ,(make-readable y)))
        (('binary-xor x y)
         `(xor$ ,(make-readable x) ,(make-readable y)))
        (('binary-? x y z)
         `(binary-? ,(make-readable x) ,(make-readable y) ,(make-readable z)))
        (('binary-not x)
         `(not$ ,(make-readable x)))
        (& (if (atom term)
               (symbol-name term)
             (progn$
              (hard-error 'make-readable
                          "Unexpected term instance~p0~%"
                          (list (cons #\0 term)))
              nil))))))
  (define make-readable-lst (lst)
    (if (atom lst)
        nil
      (cons (make-readable (car lst))
            (make-readable-lst (cdr lst))))))

(defmacro ss (&rest args)
  `(s-spec (list . ,args)))

(defmacro dd (&rest args)
  `(d-spec (list . ,args)))

(defmacro cc (&rest args)
  `(c-spec (list . ,args)))

(defmacro sc (&rest args)
  `(s-c-spec (list . ,args)))

(defmacro cs (&rest args)
  `(c-s-spec (list . ,args)))

(define is-rp-bitp (term)
  (case-match term
    (('rp ''bitp &)
     t)))

(define bit-concat ((x integerp)
                    (y integerp))
  (logapp 1 x y))

(define 2vec-adder ((x integerp)
                    (y integerp)
                    (carry-in integerp)
                    (size natp))
  (if (zp size)
      0
    (let ((sum (list (logbit 0 x)
                     (logbit 0 y)
                     carry-in)))
      (bit-concat
       (s-spec sum)
       (2vec-adder (ash x -1)
                   (ash y -1)
                   (c-spec sum)
                   (1- size))))))

(define has-bitp-rp (term)
  :hints (("Goal"
           :in-theory (e/d (is-rp) ())))
  :guard-hints (("goal"
                 :in-theory (e/d (is-rp) ())))
  (if (is-rp term)
      (or (equal (cadr term)
                 ''bitp)
          (has-bitp-rp (caddr term)))
    nil))

(define has-integerp-rp (term)
  :hints (("Goal"
           :in-theory (e/d (is-rp) ())))
  :guard-hints (("goal"
                 :in-theory (e/d (is-rp) ())))
  (if (is-rp term)
      (or (equal (cadr term)
                 ''integerp)
          (has-integerp-rp (caddr term)))
    nil))

(define append-wog (l1 l2)
  ;;(append l1 l2)
  ;; same as append
  (if (atom l1)
      l2
    (cons (car l1)
          (append-wog (cdr l1) l2))))

(progn
  (define negate-lst-aux ((lst rp-term-listp))
    :returns (negated-lst rp-term-listp :hyp (rp-term-listp lst))
    (b* (((when (atom lst)) lst)
         ((mv coef cur) (get-pp-and-coef (car lst))))
      (cons-with-times (- coef) cur
                       (negate-lst-aux (cdr lst)))))

  (define negate-lst ((lst rp-term-listp)
                      &optional (enabled 't))
    :inline t
    :returns (negated-lst rp-term-listp :hyp (rp-term-listp lst))
    (if enabled
        (negate-lst-aux lst)
      lst))

  (define negate-list-instance ((term rp-termp)
                                &optional (enabled 't))
    :returns (res rp-termp :hyp (rp-termp term))
    :inline t
    (create-list-instance (negate-lst (list-to-lst term) enabled))))

(defun hons-list-macro-fn (acl2::lst)
  (declare (xargs :guard t))
  (if (consp acl2::lst)
      (cons 'hons
            (cons (car acl2::lst)
                  (cons (hons-list-macro-fn (cdr acl2::lst))
                        nil)))
    nil))

(DEFMACRO hons-LIST (&REST ARGS)
  (hons-list-macro-fn ARGS))

(define int-vector-adder (x y)
  :verify-guards nil
  (+ (ifix (sv::4vec-fix x))
     (ifix (sv::4vec-fix y)))
  ///
  (defwarrant-rp int-vector-adder))

(define int-vector-adder-lst (lst)
  :verify-guards nil
  (if (atom lst)
      0
    (int-vector-adder (car lst)
                      (int-vector-adder-lst (cdr lst)))))

(define int-vector-adder-lst-w/carry (lst carry)
  :verify-guards nil
  (int-vector-adder carry
                    (int-vector-adder-lst lst)))

(encapsulate
  nil

  (local
   (in-theory (disable
               ;; +-is-SUM
               ;; mod2-is-m2
               ;; floor2-if-f2
               ;; c-is-f2
               ;; s-is-m2
               ;; s-spec-is-m2
               ;;SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
               ;;c-spec-is-f2
               ;;s-c-spec-is-list-m2-f2
               ;;c-s-spec-is-list-m2-f2
               ;;s-of-c-trig-def
               )))

  (with-output
    :off :all
    :gag-mode nil

    (def-formula-checks
      mult-formula-checks
      (binary-append
       ifix

       acl2::logcar$inline
       acl2::logcdr$inline
       acl2::logbit$inline
       unpack-booth
       --
       sum-list
       binary-and
       and-list
       times
       sort-sum
       rp::c-s-spec
       rp::s-c-spec
       rp::c-spec
       rp::s-spec
       logbit
       ;; svl::bits
       ;; svl::4vec-bitand
       ;; svl::4vec-bitor
       ;; svl::4vec-?
       ;; svl::4vec-?*
       ;; sv::4vec-bitxor
       ;; svl::4vec-bitnot
       ;; svl::4vec-bitnot$
       adder-b+
       s-of-c-trig
       binary-?
       binary-xor
       binary-or
       binary-not
       bit-fix
       s-c-res
       c
       m2
       f2
       times2
       s
       pp
       binary-sum
       ;;sv::3vec-fix
       bit-concat
       ;;sv::4vec-fix
       svl::bits

       and-times-list

       int-vector-adder-lst
       int-vector-adder-lst-w/carry

       ))))

