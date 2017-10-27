; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "AIGNET")
(include-book "arrays")
(include-book "std/stobjs/updater-independence" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/misc/u32-listp" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/resize-list" :dir :system))
(local (include-book "std/lists/index-of" :dir :system))
(local (include-book "std/lists/repeat" :dir :system))

(local (in-theory (disable nth update-nth
                           acl2::nth-when-zp
                           acl2::zp-open
                           acl2::resize-list-when-atom
                           resize-list)))

;; Functions like aignet-copy-dfs-rec use a bit array called mark.  Using a
;; simple bit array is sometimes expensive because if we want to do several
;; separate traversals we need to clear or reallocate the array before each
;; one.  In this book are other implementations that may be cheaper to clear
;; whereas their get/set behavior and logical representations are equivalent.



;; EBA stands for Erasable Bit Array.  It is just a bit array (represented as
;; 32-bit words) along with a vector containing the indices of all words that
;; have at least one bit set, and a counter for how many such words we have.
;; The bit array can be cleared by clearing all the listed entries.  We can
;; also limit the number of indices to store, in which case if we have more
;; entries than that, we will just iterate over the whole array to clear it.

(defstobj eba$c
  (eba$c->bits :type (array (unsigned-byte 32) (1)) :resizable t :initially 0)
  (eba$c->wordlist :type (array (unsigned-byte 32) (0)) :resizable t :initially 0)
  (eba$c->wordcount :type (unsigned-byte 32) :initially 0)
  (eba$c->length :type (unsigned-byte 32) :initially 0)
  :inline t)

(local (defthm eba$c->bitsp-is-u32-listp
         (equal (eba$c->bitsp x)
                (acl2::u32-listp x))))

(local (defthm eba$c->wordlistp-is-u32-listp
         (equal (eba$c->wordlistp x)
                (acl2::u32-listp x))))

(local (in-theory (enable acl2::nth-in-u32-listp-natp
                          acl2::nth-in-u32-listp-integerp
                          acl2::nth-in-u32-listp-gte-0
                          acl2::nth-in-u32-listp-upper-bound)))

;; (local (Defthm nth-in-u32-listp-natp-type
;;          (implies (and (acl2::u32-listp gates)
;;                        (< (nfix idx) (len gates)))
;;                   (natp (nth idx gates)))
;;          :rule-classes :type-prescription))

(defsection eba$c-words-in-bounds
  (defun-sk eba$c-words-in-bounds (eba$c)
    (forall idx
            (implies (and (< (nfix idx) (nfix (eba$c->wordcount eba$c)))
                          (< (nfix idx) (len (nth *eba$c->wordlisti* eba$c))))
                     (< (nfix (nth idx (nth *eba$c->wordlisti* eba$c)))
                        (len (nth *eba$c->bitsi* eba$c)))))
    :rewrite :direct)

  (in-theory (disable eba$c-words-in-bounds))

  (defthm eba$c-words-in-bounds-necc-no-nfix
    (implies (and (eba$c-words-in-bounds eba$c)
                  (< (nfix idx) (nfix (eba$c->wordcount eba$c)))
                  (< (nfix idx) (len (nth *eba$c->wordlisti* eba$c)))
                  (natp (nth idx (nth *eba$c->wordlisti* eba$c))))
             (<  (nth idx (nth *eba$c->wordlisti* eba$c))
                 (len (nth *eba$c->bitsi* eba$c))))
    :hints (("goal" :use eba$c-words-in-bounds-necc))
    :rule-classes (:rewrite :linear))

  (defthm eba$c-words-in-bounds-necc-linear
    (implies (and (eba$c-words-in-bounds eba$c)
                  (< (nfix idx) (nfix (eba$c->wordcount eba$c)))
                  (< (nfix idx) (len (nth *eba$c->wordlisti* eba$c))))
             (<  (nfix (nth idx (nth *eba$c->wordlisti* eba$c)))
                 (len (nth *eba$c->bitsi* eba$c))))
    :hints (("goal" :use eba$c-words-in-bounds-necc))
    :rule-classes :linear)

  (defthm eba$c-words-in-bounds-necc-lte
    (implies (and (eba$c-words-in-bounds eba$c)
                  (< (nfix idx) (nfix (eba$c->wordcount eba$c)))
                  (< (nfix idx) (len (nth *eba$c->wordlisti* eba$c))))
             (<= (+ 1 (nfix (nth idx (nth *eba$c->wordlisti* eba$c))))
                 (len (nth *eba$c->bitsi* eba$c))))
    :hints (("goal" :use eba$c-words-in-bounds-necc)))

  (defthm eba$c-words-in-bounds-necc-lte-no-nfix
    (implies (and (eba$c-words-in-bounds eba$c)
                  (< (nfix idx) (nfix (eba$c->wordcount eba$c)))
                  (< (nfix idx) (len (nth *eba$c->wordlisti* eba$c)))
                  (natp (nth idx (nth *eba$c->wordlisti* eba$c))))
             (<= (+ 1 (nth idx (nth *eba$c->wordlisti* eba$c)))
                 (len (nth *eba$c->bitsi* eba$c))))
    :hints (("goal" :use eba$c-words-in-bounds-necc))
    :rule-classes (:rewrite :linear))

  (stobjs::def-updater-independence-thm eba$c-words-in-bounds-updater-independence
    (implies (and (eba$c-words-in-bounds old)
                  (equal (nth *eba$c->wordlisti* new)
                         (nth *eba$c->wordlisti* old))
                  (equal (len (nth *eba$c->bitsi* new))
                         (len (nth *eba$c->bitsi* old)))
                  (nat-equiv (nth *eba$c->wordcount* new)
                             (nth *eba$c->wordcount* old)))
             (eba$c-words-in-bounds new))
    :hints ((and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :use ((:instance eba$c-words-in-bounds-necc
                          (eba$c old)
                          (idx (eba$c-words-in-bounds-witness new))))
                   :in-theory (disable eba$c-words-in-bounds-necc))))))

(defsection eba$c-set-bits-in-words

  (defun-sk eba$c-set-bits-in-words (eba$c)
    (forall idx
            (implies (and (not (equal 0 (nfix (eba$c->bitsi idx eba$c))))
                          (natp idx))
                     (member idx
                             (take (nth *eba$c->wordcount* eba$c)
                                   (nth *eba$c->wordlisti* eba$c)))))
    :rewrite :direct)

  (in-theory (disable eba$c-set-bits-in-words)))
    
             
                  

  



(define eba$c-set-bit$ ((word-idx :type (unsigned-byte 27))
                        (bit-idx :type (unsigned-byte 5))
                        (eba$c))
  :guard (< word-idx (eba$c->bits-length eba$c))
  :enabled t
  (b* (((the (unsigned-byte 32) word) (lnfix (eba$c->bitsi (the (unsigned-byte 32) word-idx) eba$c)))
       ((the (unsigned-byte 32) new-word)
        (the (unsigned-byte 32)
             (logior (The (unsigned-byte 32) (ash 1 bit-idx))
                     (the (unsigned-byte 32) word))))
       (eba$c (update-eba$c->bitsi (the (unsigned-byte 32) word-idx)
                                   (the (unsigned-byte 32) new-word)
                                   eba$c))
       ((unless (eql (the (unsigned-byte 32) word) 0))
        eba$c)
       ((the (unsigned-byte 32) wc) (lnfix (eba$c->wordcount eba$c)))
       ((when (<= (eba$c->wordlist-length eba$c) wc))
        (if (eql (eba$c->wordlist-length eba$c) wc)
            (mbe :logic
                 (update-eba$c->wordcount (+ 1 wc) eba$c)
                 :exec (if (< wc #xffffffff)
                           (update-eba$c->wordcount (+ 1 wc) eba$c)
                         (ec-call (update-eba$c->wordcount (+ 1 wc) eba$c))))
          eba$c))
       (eba$c (update-eba$c->wordlisti (the (unsigned-byte 32) wc)
                                       (the (unsigned-byte 32) word-idx) eba$c))
       (new-wc (+ 1 wc)))
    (mbe :logic
         (update-eba$c->wordcount new-wc eba$c)
         :exec (if (< wc #xffffffff)
                   (update-eba$c->wordcount new-wc eba$c)
                 (ec-call (update-eba$c->wordcount new-wc eba$c))))))

(local
 #!acl2
 (defthmd logtail-monotonic
   (implies (and (integerp x)
                 (<= x y) (integerp y))
            (<= (logtail n x) (logtail n y)))
   :hints(("Goal" :in-theory (enable* ihsext-recursive-redefs
                                     ihsext-inductions
                                     logcons)
           :induct t))
   :rule-classes
   ((:linear :trigger-terms ((logtail n x)))
    (:linear :trigger-terms ((logtail n y))
     :corollary (implies (and (integerp y)
                              (<= x y) (integerp x))
                         (<= (logtail n x) (logtail n y)))))))


(local (defthm take-of-update-last-lemma
         (equal (take (+ 1 (nfix n))
                      (update-nth n v x))
                (append (take n x) (list v)))
         :hints (("goal" :in-theory (enable update-nth)))
         :rule-classes nil))

(local (defthm take-of-update-last
         (implies (equal nn (nfix n))
                  (equal (take (+ 1 nn) (update-nth n v x))
                         (append (take n x) (list v))))
         :hints (("goal" :use take-of-update-last-lemma))))

(local (defthm member-append
         (iff (member x (append a b))
              (or (member x a) (member x b)))))



(define eba$c-set-bits-invar ((eba$c))
  (implies (<= (lnfix (eba$c->wordcount eba$c)) (eba$c->wordlist-length eba$c))
           (ec-call (eba$c-set-bits-in-words eba$c))))

(define eba$c-set-bit ((n natp)
                       (eba$c))
  :guard (and (< n (eba$c->length eba$c))
              (< (ash (eba$c->length eba$c) -5) (eba$c->bits-length eba$c)))
  :guard-hints (("goal" :use ((:instance acl2::logtail-monotonic
                               (x n) (y (eba$c->length eba$c)) (n 5)))))
  :returns (new-eba$c)
  :inline t
  (b* ((word-idx (ash (lnfix n) -5))
       (bit-idx (logand #x1f (lnfix n))))
    (mbe :logic (eba$c-set-bit$ word-idx bit-idx eba$c)
         :exec
         (if (< word-idx #x4000000) ;; 2^27
             (eba$c-set-bit$ word-idx bit-idx eba$c)
           (ec-call (eba$c-set-bit$ word-idx bit-idx eba$c)))))
  ///
  (defret eba$c-set-bit-words-in-bounds
    (implies (and (eba$c-words-in-bounds eba$c)
                  (< (nfix n) (nfix (eba$c->length eba$c)))
                  (< (acl2::logtail 5 (nfix (eba$c->length eba$c))) (eba$c->bits-length eba$c)))
             (eba$c-words-in-bounds new-eba$c))
    :hints (("goal" :use ((:instance acl2::logtail-monotonic
                           (x (nfix n)) (y (eba$c->length eba$c)) (n 5))))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret eba$c-set-bit-preserves-eba$c-set-bits-invar
    (implies (eba$c-set-bits-invar eba$c)
             (eba$c-set-bits-invar new-eba$c))
    :hints(("Goal" :in-theory (e/d (eba$c-set-bits-invar)
                                   (;; eba$c-set-bit
                                    acl2::take-redefinition))
            :use ((:instance acl2::logtail-monotonic
                           (x (nfix n)) (y (eba$c->length eba$c)) (n 5))))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  ;; (defret eba$c-set-bit-preserves-eba$c-set-bits-in-words
  ;;   (implies (and (eba$c-set-bits-in-words eba$c)
  ;;                 (< (nfix (eba$c->wordcount eba$c))
  ;;                    (eba$c->wordlist-length eba$c)))
  ;;            (eba$c-set-bits-in-words new-eba$c))
  ;;   :hints (("goal" :use ((:instance acl2::logtail-monotonic
  ;;                          (x (nfix n)) (y (eba$c->length eba$c)) (n 5)))
  ;;            :in-theory (disable acl2::take-redefinition))
  ;;           (and stable-under-simplificationp
  ;;                `(:expand (,(car (last clause)))))))

  (defret eba$c-set-bit-preserves-wordlist-length
    (equal (len (nth *eba$c->wordlisti* new-eba$c))
           (len (nth *eba$c->wordlisti* eba$c))))

  (defret eba$c-set-bit-preserves-bits-length
    (implies (and (< (nfix n) (nfix (eba$c->length eba$c)))
                  (< (ash (nfix (eba$c->length eba$c)) -5)
                     (eba$c->bits-length eba$c)))
             (equal (len (nth *eba$c->bitsi* new-eba$c))
                    (len (nth *eba$c->bitsi* eba$c))))
    :hints (("goal" :use ((:instance acl2::logtail-monotonic
                           (x (nfix n)) (y (eba$c->length eba$c)) (n 5)))
             :in-theory (disable acl2::take-redefinition))))

  (defret eba$c-set-bit-wordcount-incr
    (<= (nfix (nth *eba$c->wordcount* eba$c))
        (nfix (nth *eba$c->wordcount* new-eba$c)))
    :rule-classes (:rewrite :linear))

  (defret eba$c-set-bit-preserves-length
    (equal (nth *eba$c->length* new-eba$c)
           (nth *eba$c->length* eba$c))))


(define eba$c-clear-bit$ ((word-idx :type (unsigned-byte 27))
                          (bit-idx :type (unsigned-byte 5))
                          (eba$c))
  :guard (< word-idx (eba$c->bits-length eba$c))
  :enabled t
  (b* (((the (unsigned-byte 32) word) (lnfix (eba$c->bitsi (the (unsigned-byte 32) word-idx) eba$c)))
       ((the (unsigned-byte 32) new-word)
        (the (unsigned-byte 32)
             (logand (the (signed-byte 33) (lognot (the (unsigned-byte 32) (ash 1 bit-idx))))
                     (the (unsigned-byte 32) word)))))
    (update-eba$c->bitsi (the (unsigned-byte 32) word-idx)
                         (the (unsigned-byte 32) new-word)
                         eba$c)))

(define eba$c-clear-bit ((n natp)
                         (eba$c))
  :guard (and (< n (eba$c->length eba$c))
              (< (ash (eba$c->length eba$c) -5) (eba$c->bits-length eba$c)))
  :guard-hints (("goal" :use ((:instance acl2::logtail-monotonic
                               (x n) (y (eba$c->length eba$c)) (n 5)))))
  :returns (new-eba$c)
  :inline t
  (b* ((word-idx (ash (lnfix n) -5))
       (bit-idx (logand #x1f (lnfix n))))
    (mbe :logic (eba$c-clear-bit$ word-idx bit-idx eba$c)
         :exec
         (if (< word-idx #x4000000) ;; 2^27
             (eba$c-clear-bit$ word-idx bit-idx eba$c)
           (ec-call (eba$c-clear-bit$ word-idx bit-idx eba$c)))))
  ///
  (defret eba$c-clear-bit-words-in-bounds
    (implies (and (eba$c-words-in-bounds eba$c)
                  (< (nfix n) (nfix (eba$c->length eba$c)))
                  (< (acl2::logtail 5 (nfix (eba$c->length eba$c))) (eba$c->bits-length eba$c)))
             (eba$c-words-in-bounds new-eba$c))
    :hints (("goal" :use ((:instance acl2::logtail-monotonic
                           (x (nfix n)) (y (eba$c->length eba$c)) (n 5))))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))))))

  (defret eba$c-clear-bit-preserves-eba$c-clear-bits-invar
    (implies (eba$c-set-bits-invar eba$c)
             (eba$c-set-bits-invar new-eba$c))
    :hints(("Goal" :in-theory (e/d (eba$c-set-bits-invar)
                                   (;; eba$c-clear-bit
                                    acl2::take-redefinition))
            :use ((:instance acl2::logtail-monotonic
                           (x (nfix n)) (y (eba$c->length eba$c)) (n 5))))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  ;; (defret eba$c-clear-bit-preserves-eba$c-set-bits-in-words
  ;;   (implies (and (eba$c-set-bits-in-words eba$c)
  ;;                 (< (nfix (eba$c->wordcount eba$c))
  ;;                    (eba$c->wordlist-length eba$c)))
  ;;            (eba$c-set-bits-in-words new-eba$c))
  ;;   :hints (("goal" :use ((:instance acl2::logtail-monotonic
  ;;                          (x (nfix n)) (y (eba$c->length eba$c)) (n 5)))
  ;;            :in-theory (disable acl2::take-redefinition))
  ;;           (and stable-under-simplificationp
  ;;                `(:expand (,(car (last clause)))))))

  (defret eba$c-clear-bit-preserves-wordlist-length
    (equal (len (nth *eba$c->wordlisti* new-eba$c))
           (len (nth *eba$c->wordlisti* eba$c))))

  (defret eba$c-clear-bit-preserves-bits-length
    (implies (and (< (nfix n) (nfix (eba$c->length eba$c)))
                  (< (ash (nfix (eba$c->length eba$c)) -5)
                     (eba$c->bits-length eba$c)))
             (equal (len (nth *eba$c->bitsi* new-eba$c))
                    (len (nth *eba$c->bitsi* eba$c))))
    :hints (("goal" :use ((:instance acl2::logtail-monotonic
                           (x (nfix n)) (y (eba$c->length eba$c)) (n 5)))
             :in-theory (disable acl2::take-redefinition))))

  (defret eba$c-clear-bit-preserves-wordcount
    (equal (nth *eba$c->wordcount* new-eba$c)
           (nth *eba$c->wordcount* eba$c)))

  (defret eba$c-clear-bit-preserves-length
    (equal (nth *eba$c->length* new-eba$c)
           (nth *eba$c->length* eba$c))))

;; (local (defthm max-equal-second
;;          (implies (<= a b)
;;                   (equal (equal (max a b) b) t))))

;; (local (in-theory (disable max)))

(define eba$c-clear-words ((n natp :type (unsigned-byte 32))
                           (eba$c))
  :guard (and (<= n (eba$c->wordcount eba$c))
              (<= (eba$c->wordcount eba$c) (eba$c->wordlist-length eba$c))
              (ec-call (eba$c-words-in-bounds eba$c)))
  :measure (nfix (- (nfix (eba$c->wordcount eba$c)) (nfix n)))
  :returns (new-eba$c)
  (b* (((when (mbe :logic (zp (- (nfix (eba$c->wordcount eba$c)) (nfix n)))
                   :exec (eql (the (unsigned-byte 32) n)
                              (the (unsigned-byte 32) (eba$c->wordcount eba$c)))))
        eba$c)
       ((the (unsigned-byte 32) word)
        (the (unsigned-byte 32) (lnfix (eba$c->wordlisti n eba$c))))
       (eba$c (update-eba$c->bitsi (the (unsigned-byte 32) word) 0 eba$c)))
    (eba$c-clear-words (the (unsigned-byte 32)
                            (+ 1 (the (unsigned-byte 32) (lnfix n))))
                       eba$c))
  ///
  (local (defret eba$c-clear-words-preserves-zero
           (implies (equal 0 (nth idx (nth *eba$c->bitsi* eba$c)))
                    (equal (nth idx (nth *eba$c->bitsi* new-eba$c)) 0))))

  (local (defret eba$c-clear-words-preserves-zero-nat-equiv
           (implies (nat-equiv 0 (nth idx (nth *eba$c->bitsi* eba$c)))
                    (nat-equiv (nth idx (nth *eba$c->bitsi* new-eba$c)) 0))))

  (local (defret eba$c-clear-words-effect-rec
           (implies (and (<= (nfix n) (nfix m))
                         (< (nfix m) (nfix (eba$c->wordcount eba$c))))
                    (equal (nth (nth m (nth *eba$c->wordlisti* eba$c))
                                (nth *eba$c->bitsi* new-eba$c))
                           0))
           :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))
           :rule-classes nil))

  (local (defthm nth-index-of-of-take-when-member
           (implies (and (member x (take n y))
                         (<= (nfix n) (len y)))
                    (equal (nth (acl2::index-of x (take n y)) y)
                           x))
           :hints(("Goal" :in-theory (enable acl2::index-of nth)))))

  (defthm eba$c-clear-words-effect
    (implies (and (eba$c-set-bits-in-words eba$c)
                  (<= (nfix (eba$c->wordcount eba$c)) (eba$c->wordlist-length eba$c)))
             (nat-equiv (nth idx (nth *eba$c->bitsi* (eba$c-clear-words 0 eba$c)))
                        0))
    :hints (("goal" :use ((:instance eba$c-clear-words-effect-rec
                           (m (acl2::index-of (nfix idx)
                                              (take (eba$c->wordcount eba$c)
                                                    (nth *eba$c->wordlisti* eba$c))))
                           (n 0))
                          (:instance eba$c-set-bits-in-words-necc
                           (idx (nfix idx))))
             :do-not-induct t
             :in-theory (disable eba$c-clear-words
                                 eba$c-set-bits-in-words-necc))))

  (defret eba$c-clear-words-preserves-wordlist-length
    (equal (nth *eba$c->wordlisti* new-eba$c)
           (nth *eba$c->wordlisti* eba$c)))

  (defret eba$c-clear-words-preserves-bits-length
    (implies (and (eba$c-words-in-bounds eba$c)
                  (<= (nfix (eba$c->wordcount eba$c)) (eba$c->wordlist-length eba$c)))
             (equal (len (nth *eba$c->bitsi* new-eba$c))
                    (len (nth *eba$c->bitsi* eba$c)))))

  (defret eba$c-clear-words-preserves-length
    (equal (nth *eba$c->length* new-eba$c)
           (nth *eba$c->length* eba$c))))

(define eba$c-clear-all ((n natp :type (unsigned-byte 32))
                         (eba$c))
  :guard (and (<= n (eba$c->bits-length eba$c))
              (unsigned-byte-p 32 (eba$c->bits-length eba$c)))
  :measure (nfix (- (eba$c->bits-length eba$c) (nfix n)))
  :returns (new-eba$c)
  (b* (((when (mbe :logic (zp (- (eba$c->bits-length eba$c) (nfix n)))
                   :exec (eql (the (unsigned-byte 32) n)
                              (the (unsigned-byte 32) (eba$c->bits-length eba$c)))))
        eba$c)
       (eba$c (update-eba$c->bitsi (the (unsigned-byte 32) n) 0 eba$c)))
    (eba$c-clear-all (the (unsigned-byte 32)
                          (+ 1 (the (unsigned-byte 32) (lnfix n))))
                     eba$c))
  ///
  (local (defret eba$c-clear-all-preserves-zero
           (implies (equal 0 (nth idx (nth *eba$c->bitsi* eba$c)))
                    (equal (nth idx (nth *eba$c->bitsi* new-eba$c)) 0))))

  (local (defret eba$c-clear-all-preserves-zero-nat-equiv
           (implies (nat-equiv 0 (nth idx (nth *eba$c->bitsi* eba$c)))
                    (nat-equiv (nth idx (nth *eba$c->bitsi* new-eba$c)) 0))))

  (defret eba$c-clear-all-effect
    (implies (<= (nfix n) (nfix idx))
             (nat-equiv (nth idx (nth *eba$c->bitsi* new-eba$c)) 0)))

  (defret eba$c-clear-all-preserves-wordlist
    (equal (nth *eba$c->wordlisti* new-eba$c)
           (nth *eba$c->wordlisti* eba$c)))

  (defret eba$c-clear-all-preserves-bits-length
    (equal (len (nth *eba$c->bitsi* new-eba$c))
           (len (nth *eba$c->bitsi* eba$c))))

  (defret eba$c-clear-all-preserves-length
    (equal (nth *eba$c->length* new-eba$c)
           (nth *eba$c->length* eba$c))))


(define eba$c-clear ((eba$c))
  :guard (ec-call (eba$c-words-in-bounds eba$c))
  :returns (new-eba$c)
  (b* ((eba$c (if (<= (lnfix (eba$c->wordcount eba$c))
                      (eba$c->wordlist-length eba$c))
                  (eba$c-clear-words 0 eba$c)
                (if (<= (eba$c->bits-length eba$c) #xffffffff)
                    (eba$c-clear-all 0 eba$c)
                  (ec-call (eba$c-clear-all 0 eba$c))))))
    (update-eba$c->wordcount 0 eba$c))
  ///
  (defret eba$c-clear-effect
    (implies (eba$c-set-bits-invar eba$c)
             (nat-equiv (nth idx (nth *eba$c->bitsi* new-eba$c)) 0))
    :hints(("Goal" :in-theory (enable eba$c-set-bits-invar))))

  (defret eba$c-clear-preserves-wordlist
    (equal (nth *eba$c->wordlisti* new-eba$c)
           (nth *eba$c->wordlisti* eba$c)))

  (defret eba$c-clear-preserves-bits-length
    (implies (eba$c-words-in-bounds eba$c)
             (equal (len (nth *eba$c->bitsi* new-eba$c))
                    (len (nth *eba$c->bitsi* eba$c)))))

  (defret eba$c-clear-preserves-length
    (equal (nth *eba$c->length* new-eba$c)
           (nth *eba$c->length* eba$c)))

  (defret eba$c-clear-wordcount
    (equal (nth *eba$c->wordcount* new-eba$c) 0))

  (defret eba$c-set-bits-invar-of-eba$c-clear
    (implies (eba$c-set-bits-invar eba$c)
             (eba$c-set-bits-invar new-eba$c))
    :hints(("goal" :in-theory (disable eba$c-clear))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause))))))))


(define eba$c-resize$ ((n natp :type (unsigned-byte 32)) eba$c)
  :returns (new-eba$c)
  :guard (ec-call (eba$c-words-in-bounds eba$c))
  :enabled t
  (b* ((eba$c (eba$c-clear eba$c))
       (nwords (+ 1 (ash (lnfix n) -5)))
       (eba$c (resize-eba$c->bits nwords eba$c))
       (eba$c (update-eba$c->length (lnfix n) eba$c)))
    ;; Heuristic: If we write bits to more than 1/4 the words, then we
    ;; should just traverse the whole array to clear it instead of
    ;; collecting and visiting specifically the words that were visited.
    (resize-eba$c->wordlist (ash nwords -2) eba$c)))

(define eba$c-resize ((n natp) eba$c)
  :returns (new-eba$c)
  :guard (ec-call (eba$c-words-in-bounds eba$c))
  :inline t
  (mbe :logic (eba$c-resize$ n eba$c)
       :exec (if (<= n #xffffffff)
                 (eba$c-resize$ n eba$c)
               (ec-call (eba$c-resize$ n eba$c))))
  ///
  
  (defret eba$c-resize-effect
    (implies (eba$c-set-bits-invar eba$c)
             (nat-equiv (nth idx (nth *eba$c->bitsi* new-eba$c)) 0))
    :hints(("Goal" :in-theory (enable eba$c-set-bits-invar))))

  (defret eba$c-resize-length
    (equal (nth *eba$c->length* new-eba$c)
           (nfix n)))

  (defret eba$c-resize-wordcount
    (equal (nth *eba$c->wordcount* new-eba$c) 0))

  (defret eba$c-set-bits-invar-of-eba$c-resize
    (implies (eba$c-set-bits-invar eba$c)
             (eba$c-set-bits-invar new-eba$c))
    :hints(("goal" :in-theory (disable eba$c-resize))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))
           (and stable-under-simplificationp
                `(:expand (,(car (last clause)))))))

  (defret eba$c-resize-bits-length
    (equal (len (nth *eba$c->bitsi* new-eba$c))
           (+ 1 (logtail 5 (nfix n))))))


(define eba$c-get-bit ((n natp :type (unsigned-byte 32))
                       (eba$c))
  :split-types t
  :guard (and (< n (eba$c->length eba$c))
              (< (ash (eba$c->length eba$c) -5) (eba$c->bits-length eba$c)))
  :returns (bit bitp :rule-classes :type-prescription)

  :guard-hints (("goal" :use ((:instance acl2::logtail-monotonic
                               (x n) (y (eba$c->length eba$c)) (n 5)))))
  :inline t
  (b* ((word-idx (ash (lnfix n) -5))
       (bit-idx (logand #x1f (lnfix n))))
    (logbit (the (unsigned-byte 5) bit-idx)
            (the (unsigned-byte 32) (lnfix (eba$c->bitsi word-idx eba$c)))))
  ///
  (local (defthm logtail-not-equal-if-unequal
           (implies (and (integerp x) (integerp y)
                         (equal (loghead n x) (loghead n y)))
                    (iff (equal (logtail n x) (logtail n y))
                         (equal x y)))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (defret eba$c-get-bit-of-set-bit
    (equal (eba$c-get-bit n (eba$c-set-bit m eba$c))
           (if (nat-equiv n m)
               1
             (eba$c-get-bit n eba$c)))
    :hints(("Goal" :in-theory (enable eba$c-set-bit bool->bit
                                      bitops::logbitp-of-ash-split))))

  (defret eba$c-get-bit-of-clear-bit
    (equal (eba$c-get-bit n (eba$c-clear-bit m eba$c))
           (if (nat-equiv n m)
               0
             (eba$c-get-bit n eba$c)))
    :hints(("Goal" :in-theory (enable eba$c-clear-bit b-and
                                      bitops::logbitp-of-ash-split))))

  (defret eba$c-get-bit-of-clear
    (implies (eba$c-set-bits-invar eba$c)
             (equal (eba$c-get-bit n (eba$c-clear eba$c))
                    0)))

  (defret eba$c-get-bit-of-resize
    (implies (eba$c-set-bits-invar eba$c)
             (equal (eba$c-get-bit n (eba$c-resize size eba$c))
                    0))))

  

(define eba$ap (eba$a)
  :enabled t
  (true-listp eba$a))
   
(define eba$a-length (eba$a)
  :guard t
  :enabled t
  (len eba$a))
       

(define eba$a-set-bit ((n natp) eba$a)
  :guard (< n (eba$a-length eba$a))
  :enabled t
  (ec-call (update-nth n 1 eba$a)))

(define eba$a-clear-bit ((n natp) eba$a)
  :guard (< n (eba$a-length eba$a))
  :enabled t
  (ec-call (update-nth n 0 eba$a)))

(define eba$a-get-bit ((n natp) eba$a)
  :guard (< n (eba$a-length eba$a))
  :enabled t
  (bfix (ec-call (nth n eba$a))))

(define eba$a-clear (eba$a)
  :enabled t
  (acl2::repeat (len eba$a) 0))

(define eba$a-resize ((n natp) eba$a)
  :ignore-ok t :irrelevant-formals-ok t
  :enabled t
  (acl2::repeat n 0))
 
(define create-eba$a ()
  :enabled t
  nil)



(defsection eba
  
  (local (defun-sk eba-bits-corr (eba$c eba$a)
           (forall idx
                   (implies (< (nfix idx) (len eba$a))
                            (equal (eba$c-get-bit idx eba$c)
                                   (eba$a-get-bit idx eba$a))))
           :rewrite :direct))

  (local (in-theory (disable eba-bits-corr)))

  (local
   (define eba-corr (eba$c eba$a)
     :non-executable t
     :verify-guards nil
     :enabled t
     (and (eba$c-set-bits-invar eba$c)
          (eba$c-words-in-bounds eba$c)
          (equal (eba$c->length eba$c) (len eba$a))
          (< (ash (eba$c->length eba$c) -5) (eba$c->bits-length eba$c))
          (eba-bits-corr eba$c eba$a))))


  (local (in-theory (disable (eba-corr)
                             (eba$c-set-bits-invar)
                             (eba$c-words-in-bounds)
                             (eba-bits-corr))))

  (local (defthm eba$c-set-bits-invar-when-empty
           (implies (equal (nth *eba$c->bitsi* eba$c) '(0))
                    (eba$c-set-bits-invar eba$c))
           :hints(("Goal" :in-theory (enable eba$c-set-bits-invar
                                             eba$c-set-bits-in-words
                                             nth)))))

  (local (defthm eba$c-words-in-bounds-when-empty
           (implies (equal (eba$c->wordcount eba$c) 0)
                    (eba$c-words-in-bounds eba$c))
           :hints(("Goal" :in-theory (enable eba$c-words-in-bounds)))))

  (local (defthm eba$c-bits-corr-when-empty
           (implies (equal (len eba$a) 0)
                    (eba-bits-corr eba$c eba$a))
           :hints(("Goal" :in-theory (enable eba-bits-corr)))))


  (local (set-default-hints
          '((and stable-under-simplificationp
                 (let* ((lit (car (last clause)))
                        (fn (car lit)))
                   (if (member fn '(eba-bits-corr
                                    ;; eba$c-set-bits-invar
                                    ;; eba$c-set-bits-in-words
                                    ))
                       `(:expand (,lit))
                     nil))))))

  (defabsstobj-events eba
    :concrete eba$c
    :recognizer (ebap :exec eba$cp :logic eba$ap)
    :creator (create-eba :exec create-eba$c :logic create-eba$a)
    :corr-fn eba-corr
    :exports ((eba-length :exec eba$c->length :logic eba$a-length)
              (eba-get-bit :exec eba$c-get-bit$inline :logic eba$a-get-bit)
              (eba-set-bit :exec eba$c-set-bit$inline :logic eba$a-set-bit :protect t)
              (eba-clear-bit :exec eba$c-clear-bit$inline :logic eba$a-clear-bit)
              (eba-clear :exec eba$c-clear :logic eba$a-clear :protect t)
              (resize-eba :exec eba$c-resize$inline :logic eba$a-resize :protect t)))

  )

