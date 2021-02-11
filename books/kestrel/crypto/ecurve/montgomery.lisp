; Elliptic Curve Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ECURVE")

(include-book "prime-field-squares")

(include-book "centaur/fty/top" :dir :system)
(include-book "kestrel/crypto/ecurve/points-fty" :dir :system)
(include-book "kestrel/fty/deffixequiv-sk" :dir :system)
(include-book "kestrel/prime-fields/prime-fields" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

(local (include-book "kestrel/prime-fields/prime-fields-rules" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ montgomery
  :parents (elliptic-curves)
  :short "Elliptic curves over prime fields in Montgomery form."
  :long
  (xdoc::topstring
   (xdoc::p
    "Montgomery curves are introduced in (Section 10.3.1 of) "
    (xdoc::ahref
     "https://www.ams.org/journals/mcom/1987-48-177/S0025-5718-1987-0866113-7/"
     "Montgomery's
      ``Speeding the Pollard and Elliptic Curve Methods of Factorization''")
    " and described in perhaps more detail in "
    (xdoc::ahref
     "https://eprint.iacr.org/2008/013.pdf"
     "Bernstein and Lange's ``Montgomery curves and the Montgomery ladder''")
    " and "
    (xdoc::ahref
     "https://eprint.iacr.org/2008/013.pdf"
     "Bernstein, Birkner, Joye, Lange, and Peters's ``Twisted Edwards Curves''")
    ".")
   (xdoc::p
    "A Montgomery curve over a prime field of size @($p \\neq 2$)
    is described by the equation")
   (xdoc::@[]
    "B y^2 = x^3 + A x^2 + x")
   (xdoc::p
    "where @($B \\neq 0$) and @($A \\not\\in \\{-2, 2\\}$).
     The curve consists of
     all the finite points @($(x,y)$) that satisfy the equation,
     plus the point at infinity."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(fty::defprod montgomery-curve
  :short "Fixtype of elliptic curve over prime fields in Montgomery form."
  :long
  (xdoc::topstring
   (xdoc::p
    "This kind of curve is specified by
     the prime @($p$) and the coefficients @($A$) and @($B$);
     see @(see montgomery-curves).
     Thus, we formalize a curve as a triple of these numbers,
     via a fixtype product.")
   (xdoc::p
    "Because @('primep') is slow on large numbers,
     we do not include this requirement into the fixtype;
     otherwise, it may take a long time to construct a value of this fixtype
     for a practical curve.
     We just require @($p$) to be greater than 2;
     see @(see montgomery-curves).
     We express the primality of @($p$) separately.")
   (xdoc::p
    "We require @($A$) and @($B$) to be in the prime field of @($p$).
     We also require them to satisfy the condition @(see montgomery-curves).")
   (xdoc::p
    "To fix the three components to satisfy the requirements above,
     we pick 3 for @($p$), 0 for @($A$), and 1 for @($B$)."))
  ((p nat :reqfix (if (> p 2) p 3))
   (a :reqfix (if (and (> p 2)
                       (fep a p)
                       (not (equal a 2))
                       (not (equal a (mod -2 p))))
                  a
                0))
   (b :reqfix (if (and (fep b p)
                       (not (equal b 0)))
                  b
                1)))
  :require (and (> p 2)
                (fep a p)
                (fep b p)
                (not (equal a 2))
                (not (equal a (mod -2 p)))
                (not (equal b 0)))
  :pred montgomery-curvep
  :prepwork ((local (include-book "arithmetic-3/top" :dir :system)))
  ///

  (defrule montgomery->p-lower-bound
    (> (montgomery-curve->p curve) 2)
    :rule-classes :linear))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define montgomery-curve-primep ((curve montgomery-curvep))
  :returns (yes/no booleanp)
  :short "Check that the prime of a Montgomery curve is prime."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is in a separate predicate
     for the reason explained in @(tsee montgomery)."))
  (rtl::primep (montgomery-curve->p curve))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define point-on-montgomery-p ((point pointp) (curve montgomery-curvep))
  :guard (montgomery-curve-primep curve)
  :returns (yes/no booleanp)
  :short "Check if a point is on a Montgomery curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "The primality requirement in the guard of this function
     is not strictly needed to define this function,
     but in general we should only deal with well-formed curves.
     In particular, curves whose @($p$) is prime.")
   (xdoc::p
    "The point at infinity is on the cure.
     A finite point @($(x, y)$) is on the curve if and only if
     its components satisfy the curve equation;
     we require its components to be below the prime,
     i.e. that the point is in the cartesian product of the prime field."))
  (b* ((p (montgomery-curve->p curve))
       (a (montgomery-curve->a curve))
       (b (montgomery-curve->b curve))
       ((when (eq (point-kind point) :infinite)) t)
       (x (point-finite->x point))
       (y (point-finite->y point))
       ((unless (< x p)) nil)
       ((unless (< y p)) nil)
       (x^2 (mul x x p))
       (x^3 (mul x x^2 p))
       (y^2 (mul y y p))
       (a.x^2 (mul a x^2 p))
       (b.y^2 (mul b y^2 p))
       (x^3+a.x^2+x (add x^3 (add a.x^2 x p) p)))
    (equal b.y^2 x^3+a.x^2+x))
  :guard-hints (("Goal" :in-theory (enable fep)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule montgomery-only-point-with-y-0-when-aa-minus-4-non-square
  :short "Theorem about the only point with zero ordinate
          for certain Montgomery curves."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @($A^2 - 4$) is not a square,
     then @($(0,0)$) is the only point on a Montgomery curve
     with @($y = 0$).
     The proof is carried out via a series of lemmas
     that explain it.
     It requires some algebraic manipulations that are not simplifications;
     thus, it would be interesting to see whether and how it is possible
     to carry out the proofs more automatically
     via sufficiently general rules.")
   (xdoc::p
    "This theorem has some significance, in particular, for the "
    (xdoc::seetopic "birational-montgomery-twisted-edwards"
                    "birational equivalence between
                     Montgomery and twisted Edwards curves")
    ": points with @($y = 0$) on a Montgomery curve
     are not amenable to the rational mapping,
     because they make a denominator zero;
     thus, they have to be treated specially for the mapping.
     This theorem, under the aforementioned condition on @($A$),
     tells us that there is just one such point."))
  (b* ((p (montgomery-curve->p curve))
       (a (montgomery-curve->a curve))
       (x (point-finite->x point)))
    (implies (and (montgomery-curve-primep curve)
                  (not (pfield-squarep (sub (mul a a p) 4 p) p))
                  (not (equal (point-kind point) :infinite))
                  (equal (point-finite->y point) 0))
             (equal (point-on-montgomery-p point curve)
                    (equal x 0))))
  :enable (point-on-montgomery-p montgomery-curve-primep)
  :use (lemma)

  :prep-lemmas

  (;; if the point is finite, has y = 0, and is on the curve,
   ;; then x^3 + a x^2 + x = 0:
   (defrule step1
     (b* ((p (montgomery-curve->p curve))
          (a (montgomery-curve->a curve))
          (x (point-finite->x point)))
       (implies (and (not (equal (point-kind point) :infinite))
                     (equal (point-finite->y point) 0)
                     (point-on-montgomery-p point curve))
                (equal (add (mul x (mul x x p) p)
                            (add (mul a (mul x x p) p)
                                 x
                                 p)
                            p)
                       0)))
     :rule-classes nil
     :enable point-on-montgomery-p)

   ;; if x^3 + a x^2 + x = 0,
   ;; then x (x^2 + a x + 1) = 0:
   (defrule step2
     (b* ((p (montgomery-curve->p curve))
          (a (montgomery-curve->a curve))
          (x (point-finite->x point)))
       (implies (equal (add (mul x (mul x x p) p)
                            (add (mul a (mul x x p) p)
                                 x
                                 p)
                            p)
                       0)
                (equal (mul x
                            (add (mul x x p)
                                 (add (mul a x p)
                                      1
                                      p)
                                 p)
                            p)
                       0)))
     :rule-classes nil)

   ;; if x (x^2 + a x + 1) = 0,
   ;; then x = 0 or x^2 + a x + 1 = 0:
   (defrule step3
     (b* ((p (montgomery-curve->p curve))
          (a (montgomery-curve->a curve))
          (x (point-finite->x point)))
       (implies (and (montgomery-curve-primep curve)
                     (not (equal (point-kind point) :infinite))
                     (point-on-montgomery-p point curve))
                (implies (equal (mul x
                                     (add (mul x x p)
                                          (add (mul a x p)
                                               1
                                               p)
                                          p)
                                     p)
                                0)
                         (or (equal x 0)
                             (equal (add (mul x x p)
                                         (add (mul a x p)
                                              1
                                              p)
                                         p)
                                    0)))))
     :rule-classes nil
     :enable (point-on-montgomery-p montgomery-curve-primep)
     :disable pfield::mul-of-add-arg2)

   ;; if x^2 + a x + 1 = 0,
   ;; then 4 x^2 + 4 a x + 4 = 0
   ;; (i.e. multiply by 4, in order to complete the square in the next step):
   (defrule step4
     (b* ((p (montgomery-curve->p curve))
          (a (montgomery-curve->a curve))
          (x (point-finite->x point)))
       (implies (equal (add (mul x x p)
                            (add (mul a x p)
                                 1
                                 p)
                            p)
                       0)
                (equal (mul 4
                            (add (mul x x p)
                                 (add (mul a x p)
                                      1
                                      p)
                                 p)
                            p)
                       0)))
     :rule-classes nil)

   ;; if 4 x^2 + 4 a x + 4 = 0,
   ;; then (2 x + a)^2 = a^2 - 4
   ;; (we have completed the square):
   (defrule step5
     (b* ((p (montgomery-curve->p curve))
          (a (montgomery-curve->a curve))
          (x (point-finite->x point)))
       (implies (equal (mul 4
                            (add (mul x x p)
                                 (add (mul a x p)
                                      1
                                      p)
                                 p)
                            p)
                       0)
                (equal (mul (add (mul 2 x p) a p)
                            (add (mul 2 x p) a p)
                            p)
                       (sub (mul a a p) 4 p))))
     :rule-classes nil)

   ;; if (2 x + a)^2 = a^2 - 4,
   ;; then false (i.e. nil),
   ;; because by hypothesis a^2 - 4 is not a square:
   (defrule step6
     (b* ((p (montgomery-curve->p curve))
          (a (montgomery-curve->a curve))
          (x (point-finite->x point)))
       (implies (not (pfield-squarep (sub (mul a a p) 4 p) p))
                (implies (equal (mul (add (mul 2 x p) a p)
                                     (add (mul 2 x p) a p)
                                     p)
                                (sub (mul a a p) 4 p))
                         nil)))
     :rule-classes nil
     :use (:instance pfield-squarep-suff
           (p (montgomery-curve->p curve))
           (x (sub (mul (montgomery-curve->a curve)
                        (montgomery-curve->a curve)
                        (montgomery-curve->p curve))
                   4
                   (montgomery-curve->p curve)))
           (r (add (mul 2
                        (point-finite->x point)
                        (montgomery-curve->p curve))
                   (montgomery-curve->a curve)
                   (montgomery-curve->p curve)))))

   ;; combine steps 1-6 above to show that
   ;; if the point is finite, has y = 0, and is on the curve,
   ;; then x = 0 (because the other disjunct led to nil above):
   (defrule lemma
     (b* ((p (montgomery-curve->p curve))
          (a (montgomery-curve->a curve))
          (x (point-finite->x point)))
       (implies (and (montgomery-curve-primep curve)
                     (not (pfield-squarep (sub (mul a a p) 4 p) p))
                     (not (equal (point-kind point) :infinite))
                     (equal (point-finite->y point) 0)
                     (point-on-montgomery-p point curve))
                (equal x 0)))
     :rule-classes nil
     :use (step1 step2 step3 step4 step5 step6))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defrule montgomery-not-point-with-x-minus1-when-a-minus-2-over-b-not-square
  :short "Theorem about no points with abscissa -1 on a Montgomery curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "If @($(A - 2) / B$) is not a square,
     then the Montgomery curve has no pont with @($x = -1$).
     The proof is obtained by substituting  @($x = -1$) in the curve equation,
     obtaining an equality of @($y^2$) to @($(A - 2) / B$),
     and thus concluding the impossibility of @($x = -1$).
     But we need to disable some distributivity rules
     because otherwise they take things in the wrong direction.")
   (xdoc::p
    "This theorem has some significance, in particular, for the "
    (xdoc::seetopic "birational-montgomery-twisted-edwards"
                    "birational equivalence between
                     Montgomery and twisted Edwards curves")
    ": points with @($x = -1$) on a Montgomery curve
     are not amenable to the rational mapping,
     because they make a denominator zero.
     This theorem, under the aforementioned condition on @($A$) and @($B$),
     tells us that there is no such point.")
   (xdoc::p
    "Note that @($(A - 2) / B$) is the @($d$) coefficient
     of the birationally equivalent twisted Edwards curve.
     In particular, if the Montgomery curve is birationally equivalent
     to a complete twisted Edwards curve, which is characterized by
     @($a$) being a square and @($d$) not being a square,
     then the hypothesis of this theorem is satisfied.
     Since complete twisted Edwards curves are often used
     because of their completeness,
     this theorem tells us that
     the birationally equivalent Montgomery curve
     has no exceptional point for @($x = -1$)."))
  (b* ((p (montgomery-curve->p curve))
       (a (montgomery-curve->a curve))
       (b (montgomery-curve->b curve))
       (x (point-finite->x point)))
    (implies (and (equal (point-kind point) :finite)
                  (point-on-montgomery-p point curve)
                  (montgomery-curve-primep curve)
                  (not (pfield-squarep (div (sub a 2 p) b p) p)))
             (not (equal x (neg 1 p)))))
  :use (lemma (:instance pfield-squarep-suff
               (p (montgomery-curve->p curve))
               (x (div (sub (montgomery-curve->a curve)
                            2
                            (montgomery-curve->p curve))
                       (montgomery-curve->b curve)
                       (montgomery-curve->p curve)))
               (r (point-finite->y point))))
  :enable point-on-montgomery-p

  :prep-lemmas
  ((defruled lemma
     (b* ((p (montgomery-curve->p curve))
          (a (montgomery-curve->a curve))
          (b (montgomery-curve->b curve))
          (x (point-finite->x point))
          (y (point-finite->y point)))
       (implies (and (equal (point-kind point) :finite)
                     (point-on-montgomery-p point curve)
                     (montgomery-curve-primep curve)
                     (equal x (neg 1 p)))
                (equal (mul y y p)
                       (div (sub a 2 p) b p))))
     :enable (point-on-montgomery-p
              montgomery-curve-primep
              div)
     :disable (pfield::mul-of-add-arg1
               pfield::mul-of-add-arg2
               pfield::mul-of-1-arg1-gen))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define montgomery-add ((point1 pointp)
                        (point2 pointp)
                        (curve montgomery-curvep))
  :guard (and (montgomery-curve-primep curve)
              (point-on-montgomery-p point1 curve)
              (point-on-montgomery-p point2 curve))
  :returns (point3 pointp)
  :short "Group addition on a Montgomery curve."
  :long
  (xdoc::topstring
   (xdoc::p
    "We require, in the guard, both points to be on the curve.
     Indeed, the group addition operation is only defined
     on points on the curve, not on any points.")
   (xdoc::p
    "As in short Weierstrass curves, there are various cases to consider;
     things are not as uniform as in (complete) twisted Edwards curves.
     If either point is the one at infinity,
     the result is the other point.
     Otherwise, both points are finite, and we proceed as follows.
     If the two points have
     the same @($x$) coordinates and opposite @($y$) coordinates,
     the result is the point at infinity.
     Otherwise, if the points have the same @($x$) coordinates,
     then the @($y$) coordinates must also be the same,
     and different from 0,
     since both points are on the curve
     (we should formally prove this eventually, for validation):
     we are thus in the point doubling case,
     and the formula from the referenced papers applies.
     Finally, if the @($x$) coordinates differ,
     we are in the ``normal'' (but incomplete) case,
     and the formula from the referenced papers applies.")
   (xdoc::p
    "Note that, to verify guards,
     we need to use @($3 \\mod p$) instead of just @($3$),
     in case @($p = 3$)."))
  (b* ((p (montgomery-curve->p curve))
       (a (montgomery-curve->a curve))
       (b (montgomery-curve->b curve))
       ((when (eq (point-kind point1) :infinite)) (point-fix point2))
       ((when (eq (point-kind point2) :infinite)) (point-fix point1))
       (x1 (point-finite->x point1))
       (y1 (point-finite->y point1))
       (x2 (point-finite->x point2))
       (y2 (point-finite->y point2))
       ((when (and (equal x1 x2)
                   (equal y1 (neg y2 p))))
        (point-infinite))
       ((when (equal x1 x2))
        (b* ((x x1)
             (y y1)
             (x^2 (mul x x p))
             (3.x^2 (mul (mod 3 p) x^2 p))
             (a.x (mul a x p))
             (2.a.x (mul 2 a.x p))
             (b.y (mul b y p))
             (2.b.y (mul 2 b.y p))
             (3.x^2+2.a.x+1 (add 3.x^2 (add 2.a.x 1 p) p))
             (l (div 3.x^2+2.a.x+1 2.b.y p))
             (l^2 (mul l l p))
             (b.l^2 (mul b l^2 p))
             (2.x (mul 2 x p))
             (b.l^2-a (sub b.l^2 a p))
             (b.l^2-a-2.x (sub b.l^2-a 2.x p))
             (x3 b.l^2-a-2.x)
             (x3-x (sub x3 x p))
             (l.[x3-x] (mul l x3-x p))
             (y+l.[x3-x] (add y l.[x3-x] p))
             (y3 (neg y+l.[x3-x] p)))
          (point-finite x3 y3)))
       (y2-y1 (sub y2 y1 p))
       (x2-x1 (sub x2 x1 p))
       (l (div y2-y1 x2-x1 p))
       (l^2 (mul l l p))
       (b.l^2 (mul b l^2 p))
       (b.l^2-a (sub b.l^2 a p))
       (b.l^2-a-x1 (sub b.l^2-a x1 p))
       (b.l^2-a-x1-x2 (sub b.l^2-a-x1 x2 p))
       (x3 b.l^2-a-x1-x2)
       (x3-x1 (sub x3 x1 p))
       (l.[x3-x1] (mul l x3-x1 p))
       (y1+l.[x3-x1] (add y1 l.[x3-x1] p))
       (y3 (neg y1+l.[x3-x1] p)))
    (point-finite x3 y3))
  :guard-hints (("Goal" :in-theory (enable montgomery-curve-primep
                                           point-on-montgomery-p
                                           fep)))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define montgomery-neutral ()
  :returns (point pointp)
  :short "Neutral point of the Montgomery curve group."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the point at infinity."))
  (point-infinite)
  ///

  (defrule point-on-montgomery-p-of-montgomery-neutral
    (point-on-montgomery-p (montgomery-neutral) curve)
    :enable point-on-montgomery-p)

  (in-theory (disable (:e montgomery-neutral))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define montgomery-neg ((point pointp) (curve montgomery-curvep))
  :guard (and (montgomery-curve-primep curve)
              (point-on-montgomery-p point curve))
  :returns (point1 pointp)
  :short "Negation of a point of the Montgomery curve group."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is the inverse with respect to the group addition operation.")
   (xdoc::p
    "The negation of the point at infinity is the point at infinity.
     The negation of a finite point is obtained
     by negating the @($y$) coordinate."))
  (case (point-kind point)
    (:infinite (point-infinite))
    (:finite (b* ((p (montgomery-curve->p curve))
                  (x (point-finite->x point))
                  (y (point-finite->y point)))
               (point-finite x (neg y p)))))
  :guard-hints (("Goal" :in-theory (enable point-on-montgomery-p fep)))
  :hooks (:fix)
  ///

  (defrule point-on-montgomery-p-of-montgomery-neg
    (implies (and (montgomery-curvep curve)
                  (montgomery-curve-primep curve)
                  (pointp point)
                  (point-on-montgomery-p point curve))
             (point-on-montgomery-p (montgomery-neg point curve)
                                    curve))
    :enable point-on-montgomery-p
    :disable pfield::fep-of-neg
    :use (:instance pfield::fep-of-neg
          (x (point-finite->y point))
          (p (montgomery-curve->p curve)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define montgomery-sub ((point1 pointp) (point2 pointp) (curve montgomery-curvep))
  :guard (and (montgomery-curve-primep curve)
              (point-on-montgomery-p point1 curve)
              (point-on-montgomery-p point2 curve))
  :returns (point pointp)
  :short "Subtraction of two points of the Montgomery group."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is, as usual in groups, essentially an abbreviation for
     adding the first point to the negation of the second point."))
  (montgomery-add point1
                  (montgomery-neg point2 curve)
                  curve)
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define montgomery-mul ((scalar integerp)
                        (point pointp)
                        (curve montgomery-curvep))
  :guard (and (montgomery-curve-primep curve)
              (point-on-montgomery-p point curve))
  :returns (mv (okp booleanp) (point1 pointp))
  :short "Scalar multiplication in the Montgomery group."
  :long
  (xdoc::topstring
   (xdoc::p
    "If the group were multiplicative, this would be exponentiation.
     Since the Montgomery group is additive,
     here we talk about scalar multiplication instead.")
   (xdoc::p
    "We first define the operation for non-negative scalars,
     by simple recursion in the same manner as exponentiation:
     multiplication by 0 yields the neutral element;
     multiplication by a non-zero scalar yields the sum of the point and
     the scalar multiplication by the scalar minus one.
     Then we extend it to negative scalars,
     by negating the result of multiplying by the negated scalar.")
   (xdoc::p
    "We also return a flag saying whether
     the resulting point is on the curve or not.
     This is always the case, because addition is closed in the group
     (i.e. adding two points on the curve always yields a point on the curve).
     However, we have not proved that yet,
     and thus for now we resort to using this additional flag.
     We plan to remove it eventually."))
  (b* ((scalar (ifix scalar))
       ((when (>= scalar 0)) (montgomery-mul-nonneg scalar point curve))
       ((mv okp point1) (montgomery-mul-nonneg (- scalar) point curve))
       ((when (not okp)) (mv nil (point-fix point))))
    (mv t (montgomery-neg point1 curve)))
  :hooks (:fix)

  :prepwork
  ((define montgomery-mul-nonneg ((scalar natp)
                                  (point pointp)
                                  (curve montgomery-curvep))
     :guard (and (montgomery-curve-primep curve)
                 (point-on-montgomery-p point curve))
     :returns (mv (okp booleanp) (point1 pointp))
     (b* (((when (zp scalar)) (mv t (montgomery-neutral)))
          ((mv okp point1) (montgomery-mul-nonneg (1- scalar) point curve))
          ((when (not okp)) (mv nil (point-fix point)))
          (point2 (montgomery-add point point1 curve)))
       (if (point-on-montgomery-p point2 curve)
           (mv t point2)
         (mv nil (point-fix point))))
     :hooks (:fix)
     :verify-guards nil ; done below
     ///
     (defrule point-on-montgomery-p-of-montgomery-mul-nonneg
       (implies (and (montgomery-curvep curve)
                     (montgomery-curve-primep curve)
                     (pointp point)
                     (point-on-montgomery-p point curve))
                (point-on-montgomery-p
                 (mv-nth 1 (montgomery-mul-nonneg scalar point curve))
                 curve)))
     (verify-guards montgomery-mul-nonneg)))

  ///

  (defrule point-on-montgomery-p-of-montgomery-mul
    (implies (and (montgomery-curvep curve)
                  (montgomery-curve-primep curve)
                  (pointp point)
                  (point-on-montgomery-p point curve))
             (point-on-montgomery-p
              (mv-nth 1 (montgomery-mul scalar point curve))
              curve))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define montgomery-point-orderp ((point pointp)
                                 (order natp)
                                 (curve montgomery-curvep))
  :guard (and (montgomery-curve-primep curve)
              (point-on-montgomery-p point curve))
  :returns (yes/no booleanp)
  :short "Check if a point on a Montgomery curve has a certain order."
  :long
  (xdoc::topstring
   (xdoc::p
    "A point @($P$) has order @($n$) if and only if
     @($n > 0$),
     @($n P$) is the neutral element, and
     @($m P$) is not for every @($m < n$).")
   (xdoc::p
    "Every point on the curve has an order,
     so there should really be a function that returns that.
     However, defining that function requires some theorems
     that we do not have yet;
     thus, for now we define this predicate instead.
     We plan to define the function that returns the order eventually."))
  (b* ((order (nfix order))
       ((mv okp order*point) (montgomery-mul order point curve)))
    (and okp
         (> order 0)
         (equal order*point
                (montgomery-neutral))
         (montgomery-point-order-leastp point order curve)))
  :hooks (:fix)

  :prepwork
  ((define-sk montgomery-point-order-leastp ((point pointp)
                                             (order natp)
                                             (curve montgomery-curvep))
     :guard (and (montgomery-curve-primep curve)
                 (point-on-montgomery-p point curve))
     (forall (order1)
             (implies (and (natp order1)
                           (< 0 order1)
                           (< order1 (nfix order)))
                      (b* (((mv okp order1*point)
                            (montgomery-mul order1 point curve)))
                        (implies okp
                                 (not (equal order1*point
                                             (montgomery-neutral)))))))
     ///
     (fty::deffixequiv-sk montgomery-point-order-leastp
       :args ((point pointp) (order natp) (curve montgomery-curvep))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled montgomery-points-with-same-x
  :short "Theorem about points on Montgomery curves with the same abscissa."
  :long
  (xdoc::topstring
   (xdoc::p
    "If two points on a Montgomey curve have the same abscissa,
     their squares ordinates must be equal (just use the curve equation),
     and therefore the two ordinates are equal or opposite.
     Therefore, the two points are equal or opposite."))
  (implies (and (montgomery-curve-primep curve)
                (pointp point1)
                (pointp point2)
                (point-on-montgomery-p point1 curve)
                (point-on-montgomery-p point2 curve)
                (equal (point-kind point1) :finite)
                (equal (point-kind point2) :finite)
                (equal (point-finite->x point1)
                       (point-finite->x point2)))
           (or (equal point1 point2)
               (equal point1 (montgomery-neg point2 curve))))
  :use (step1 step2)

  :prep-lemmas

  ((defruled step1
     (implies (and (montgomery-curve-primep curve)
                   (point-on-montgomery-p point1 curve)
                   (point-on-montgomery-p point2 curve)
                   (equal (point-kind point1) :finite)
                   (equal (point-kind point2) :finite)
                   (equal (point-finite->x point1)
                          (point-finite->x point2)))
              (or (equal (point-finite->y point1)
                         (point-finite->y point2))
                  (equal (point-finite->y point1)
                         (neg (point-finite->y point2)
                              (montgomery-curve->p curve)))))
     :enable (point-on-montgomery-p montgomery-curve-primep)
     :prep-books ((include-book "prime-field-extra-rules")))

   (defruled step2
     (implies (and (montgomery-curve-primep curve)
                   (pointp point1)
                   (pointp point2)
                   (point-on-montgomery-p point1 curve)
                   (point-on-montgomery-p point2 curve)
                   (equal (point-kind point1) :finite)
                   (equal (point-kind point2) :finite)
                   (equal (point-finite->x point1)
                          (point-finite->x point2))
                   (or (equal (point-finite->y point1)
                              (point-finite->y point2))
                       (equal (point-finite->y point1)
                              (neg (point-finite->y point2)
                                   (montgomery-curve->p curve)))))
              (or (equal point1 point2)
                  (equal point1 (montgomery-neg point2 curve))))
     :enable (point-on-montgomery-p
              montgomery-curve-primep
              montgomery-neg
              point-finite
              point-finite->x
              point-finite->y
              pointp))))
