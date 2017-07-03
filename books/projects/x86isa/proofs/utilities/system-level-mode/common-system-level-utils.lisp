;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")
(include-book "physical-memory-utils")
(include-book "gl-lemmas")
(include-book "bind-free-utils")
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "centaur/bitops/ihs-extensions" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "centaur/gl/gl" :dir :system))

(local (in-theory (e/d* () (signed-byte-p unsigned-byte-p))))

;; ======================================================================

(defsection common-system-level-utils
  :parents (proof-utilities)

  :short "Reasoning in the system-level mode"

  :long "<p>This book contains lemmas that come in useful in both the
  marking and non-marking sub-modes of the system-level mode.</p>" )

(local (xdoc::set-default-parents common-system-level-utils))

;; ======================================================================
;; Normalizing memory reads:

;; All these functions open up to rb.
(in-theory (e/d (rm16 rm32 rm64) ()))

(defthm mv-nth-2-rb-in-system-level-non-marking-mode
  (implies (and (not (page-structure-marking-mode x86))
                (not (mv-nth 0 (rb n addr r-x x86))))
           (equal (mv-nth 2 (rb n addr r-x x86)) x86))
  :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

(defthm mv-nth-2-rb-in-system-level-marking-mode
  (implies (and (not (programmer-level-mode x86))
                (page-structure-marking-mode x86)
                (not (mv-nth 0 (rb n addr r-x (double-rewrite x86)))))
           (equal (mv-nth 2 (rb n addr r-x x86))
                  (mv-nth 2 (las-to-pas
                             (create-canonical-address-list n addr)
                             r-x (double-rewrite x86)))))
  :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

(defthm mv-nth-0-rb-and-mv-nth-0-las-to-pas-in-system-level-mode
  (implies (not (xr :programmer-level-mode 0 x86))
           (equal (mv-nth 0 (rb n addr r-x x86))
                  (mv-nth 0 (las-to-pas
                             (create-canonical-address-list n addr)
                             r-x x86))))
  :hints (("Goal" :in-theory (e/d* (rb) (force (force))))))

;; ======================================================================

;; Normalizing memory writes:

;; All these functions open up to wb.
(in-theory (e/d (wm16 wm32 wm64) ()))

(defthm mv-nth-0-wb-and-mv-nth-0-las-to-pas-in-system-level-mode
  (implies (not (xr :programmer-level-mode 0 x86))
           (equal (mv-nth 0 (wb n addr w value x86))
                  (mv-nth 0 (las-to-pas (create-canonical-address-list n addr)
                                        :w (double-rewrite x86)))))
  :hints (("Goal" :in-theory (e/d* (wb) (force (force))))))

;; ======================================================================

;; Lemmas about prog-at:

(defthm prog-at-pop-x86-oracle-in-system-level-mode
  (implies (not (programmer-level-mode x86))
           (equal (prog-at addr bytes (mv-nth 1 (pop-x86-oracle x86)))
                  (prog-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d (prog-at pop-x86-oracle pop-x86-oracle-logic)
                                  (rb)))))

;; (defthm prog-at-xw-in-system-level-mode
;;   (implies (and (not (programmer-level-mode x86))
;;                 (not (equal fld :mem))
;;                 (not (equal fld :rflags))
;;                 (not (equal fld :ctr))
;;                 (not (equal fld :seg-visible))
;;                 (not (equal fld :msr))
;;                 (not (equal fld :fault))
;;                 (not (equal fld :programmer-level-mode))
;;                 (not (equal fld :page-structure-marking-mode)))
;;            (equal (prog-at l-addrs bytes (xw fld index value x86))
;;                   (prog-at l-addrs bytes x86)))
;;   :hints (("Goal" :in-theory (e/d* (prog-at) (rb)))))

;; The following make-event generates a bunch of rules that together
;; say the same thing as prog-at-xw-in-system-level-mode but these
;; rules are more efficient than prog-at-xw-in-system-level-mode as
;; they match less frequently.

(make-event
 (generate-read-fn-over-xw-thms
  (remove-elements-from-list
   '(:mem :rflags :ctr :seg-visible :msr :fault :programmer-level-mode :page-structure-marking-mode)
   *x86-field-names-as-keywords*)
  'prog-at
  (acl2::formals 'prog-at (w state))
  :hyps '(not (programmer-level-mode x86))
  :prepwork '((local (in-theory (e/d (prog-at) (rb)))))))

(defthm prog-at-xw-rflags-not-ac-values-in-system-level-mode
  (implies (and (not (programmer-level-mode x86))
                (equal (rflags-slice :ac value)
                       (rflags-slice :ac (rflags x86))))
           (equal (prog-at addr bytes (xw :rflags 0 value x86))
                  (prog-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d* (prog-at) (rb)))))

(defthm prog-at-values-and-!flgi
  (implies (and (not (equal index *ac*))
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (prog-at addr bytes (!flgi index value x86))
                  (prog-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d* (rflags-slice-ac-simplify
                                    !flgi-open-to-xw-rflags)
                                   (rb)))))

(defthm prog-at-values-and-!flgi-undefined
  (implies (and (not (equal index *ac*))
                (not (programmer-level-mode x86))
                (x86p x86))
           (equal (prog-at addr bytes (!flgi-undefined index x86))
                  (prog-at addr bytes x86)))
  :hints (("Goal" :in-theory (e/d* (!flgi-undefined) (rb)))))

;; ======================================================================

;; Lemmas about ia32e-la-to-pa and las-to-pas when an error is
;; encountered:

(defthm mv-nth-1-ia32e-la-to-pa-when-error
  (implies (mv-nth 0 (ia32e-la-to-pa lin-addr r-x x86))
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-x x86)) 0))
  :hints (("Goal" :in-theory (e/d (ia32e-la-to-pa
                                   ia32e-la-to-pa-pml4-table)
                                  (force (force))))))

(defthm mv-nth-1-las-to-pas-when-error
  (implies (mv-nth 0 (las-to-pas l-addrs r-x x86))
           (equal (mv-nth 1 (las-to-pas l-addrs r-x x86)) nil))
  :hints (("Goal" :in-theory (e/d (las-to-pas) (force (force))))))

;; ======================================================================

;; r-x field is irrelevant for address translation if no errors are
;; encountered:

(defthmd r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-directory-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                                (logand 18446744073709547520
                                                                                        (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (logand
                                      u/s-acc
                                      (page-user-supervisor
                                       (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                             (logand 18446744073709547520
                                                                                     (loghead 52 base-addr)))
                                                  x86))))
                            (r/w-acc (logand
                                      r/w-acc
                                      (page-read-write
                                       (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                             (logand 18446744073709547520
                                                                                     (loghead 52 base-addr)))
                                                  x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                     (logand 18446744073709547520
                                                                             (loghead 52 base-addr)))
                                          x86))))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-directory)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-directory-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                    (logand 18446744073709547520
                                                                                            (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (logand
                                      u/s-acc
                                      (page-user-supervisor
                                       (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                 (logand 18446744073709547520
                                                                                         (loghead 52 base-addr)))
                                                  x86))))
                            (r/w-acc (logand
                                      r/w-acc
                                      (page-read-write
                                       (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                 (logand 18446744073709547520
                                                                                         (loghead 52 base-addr)))
                                                  x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                         (logand 18446744073709547520
                                                                                 (loghead 52 base-addr)))
                                          x86))))))
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table)
                            (r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-pml4-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 1
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 1
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                            (logand 18446744073709547520
                                                                                    (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (page-user-supervisor
                                      (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                        (logand 18446744073709547520
                                                                                (loghead 52 base-addr)))
                                                 x86)))
                            (r/w-acc (page-read-write
                                      (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                        (logand 18446744073709547520
                                                                                (loghead 52 base-addr)))
                                                 x86)))
                            (x/d-acc
                             (page-execute-disable
                              (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                (logand 18446744073709547520
                                                                        (loghead 52 base-addr)))
                                         x86)))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-when-no-errors
  (implies (and (bind-free (find-almost-matching-ia32e-la-to-pas
                            'ia32e-la-to-pa 'r-x-1
                            (list lin-addr r-x-2 x86) mfc state)
                           (r-x-1))
                (syntaxp (and
                          ;; The bind-free ensures that r-x-2 and
                          ;; r-x-1 are unequal, but I'll still leave
                          ;; this thing in.
                          (not (eq r-x-2 r-x-1))
                          ;; r-x-2 must be smaller than r-x-1.
                          (term-order r-x-2 r-x-1)))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-x-1 x86)))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-x-2 x86))))
           (equal (mv-nth 1 (ia32e-la-to-pa lin-addr r-x-2 x86))
                  (mv-nth 1 (ia32e-la-to-pa lin-addr r-x-1 x86))))
  :hints (("Goal"
           :use ((:instance r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-pml4-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (cpl (cpl x86))
                            (base-addr (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))
                            (wp (bool->bit (logbitp 16 (xr :ctr *cr0* x86))))
                            (smep (loghead 1 (bool->bit (logbitp 20 (xr :ctr *cr4* x86)))))
                            (smap 0)
                            (ac (bool->bit (logbitp 18 (xr :rflags 0 x86))))
                            (nxe (loghead 1 (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86)))))))
           :in-theory (e/d* (ia32e-la-to-pa) ()))))

;; ----------------------------------------------------------------------

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (equal r-x-1 :w))
                (not (equal r-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-page-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-directory-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (equal r-x-1 :w))
                (not (equal r-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-directory
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-page-directory
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                                (logand 18446744073709547520
                                                                                        (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (logand
                                      u/s-acc
                                      (page-user-supervisor
                                       (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                             (logand 18446744073709547520
                                                                                     (loghead 52 base-addr)))
                                                  x86))))
                            (r/w-acc (logand
                                      r/w-acc
                                      (page-read-write
                                       (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                             (logand 18446744073709547520
                                                                                     (loghead 52 base-addr)))
                                                  x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64 (page-directory-entry-addr (logext 48 lin-addr)
                                                                     (logand 18446744073709547520
                                                                             (loghead 52 base-addr)))
                                          x86))))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-directory)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (equal r-x-1 :w))
                (not (equal r-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-page-dir-ptr-table
                              lin-addr base-addr u/s-acc r/w-acc x/d-acc
                              wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-page-dir-ptr-table
                           lin-addr base-addr u/s-acc r/w-acc x/d-acc
                           wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-directory-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                    (logand 18446744073709547520
                                                                                            (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (logand
                                      u/s-acc
                                      (page-user-supervisor
                                       (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                 (logand 18446744073709547520
                                                                                         (loghead 52 base-addr)))
                                                  x86))))
                            (r/w-acc (logand
                                      r/w-acc
                                      (page-read-write
                                       (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                                 (logand 18446744073709547520
                                                                                         (loghead 52 base-addr)))
                                                  x86))))
                            (x/d-acc
                             (logand
                              x/d-acc
                              (page-execute-disable
                               (rm-low-64 (page-dir-ptr-table-entry-addr (logext 48 lin-addr)
                                                                         (logand 18446744073709547520
                                                                                 (loghead 52 base-addr)))
                                          x86))))))
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-page-dir-ptr-table)
                            (r-x-is-irrelevant-for-mv-nth-1-ia32e-la-to-pa-page-table-when-no-errors
                             bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthmd r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-pml4-table-when-no-errors
  (implies (and (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-x-1 cpl x86)))
                (syntaxp (not (eq r-x-2 r-x-1)))
                (not (equal r-x-1 :w))
                (not (equal r-x-2 :w))
                (not (mv-nth 0
                             (ia32e-la-to-pa-pml4-table
                              lin-addr base-addr wp smep smap ac nxe r-x-2 cpl x86))))
           (equal (mv-nth 2
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-x-2 cpl x86))
                  (mv-nth 2
                          (ia32e-la-to-pa-pml4-table
                           lin-addr base-addr wp smep smap ac nxe r-x-1 cpl x86))))
  :hints (("Goal"
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-page-dir-ptr-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (base-addr (ash
                                        (loghead
                                         40
                                         (logtail
                                          12
                                          (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                            (logand 18446744073709547520
                                                                                    (loghead 52 base-addr)))
                                                     x86)))
                                        12))
                            (u/s-acc (page-user-supervisor
                                      (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                        (logand 18446744073709547520
                                                                                (loghead 52 base-addr)))
                                                 x86)))
                            (r/w-acc (page-read-write
                                      (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                        (logand 18446744073709547520
                                                                                (loghead 52 base-addr)))
                                                 x86)))
                            (x/d-acc
                             (page-execute-disable
                              (rm-low-64 (pml4-table-entry-addr (logext 48 lin-addr)
                                                                (logand 18446744073709547520
                                                                        (loghead 52 base-addr)))
                                         x86)))))
           :do-not-induct t
           :in-theory (e/d* (disjoint-p
                             member-p
                             ia32e-la-to-pa-pml4-table)
                            (bitops::logand-with-negated-bitmask
                             (:meta acl2::mv-nth-cons-meta)
                             force (force))))))

(defthm r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-when-no-errors
  (implies (and (bind-free (find-almost-matching-ia32e-la-to-pas
                            'ia32e-la-to-pa 'r-x-1
                            (list lin-addr r-x-2 x86) mfc state)
                           (r-x-1))
                (syntaxp (and
                          ;; The bind-free ensures that r-x-2 and
                          ;; r-x-1 are unequal, but I'll still leave
                          ;; this thing in.
                          (not (eq r-x-2 r-x-1))
                          ;; r-x-2 must be smaller than r-x-1.
                          (term-order r-x-2 r-x-1)))
                (not (equal r-x-1 :w))
                (not (equal r-x-2 :w))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-x-1 x86)))
                (not (mv-nth 0 (ia32e-la-to-pa lin-addr r-x-2 x86))))
           (equal (mv-nth 2 (ia32e-la-to-pa lin-addr r-x-2 x86))
                  (mv-nth 2 (ia32e-la-to-pa lin-addr r-x-1 x86))))
  :hints (("Goal"
           :use ((:instance r/x-is-irrelevant-for-mv-nth-2-ia32e-la-to-pa-pml4-table-when-no-errors
                            (lin-addr (logext 48 lin-addr))
                            (cpl (cpl x86))
                            (base-addr (ash (loghead 40 (logtail 12 (xr :ctr *cr3* x86))) 12))
                            (wp (bool->bit (logbitp 16 (xr :ctr *cr0* x86))))
                            (smep (loghead 1 (bool->bit (logbitp 20 (xr :ctr *cr4* x86)))))
                            (smap 0)
                            (ac (bool->bit (logbitp 18 (xr :rflags 0 x86))))
                            (nxe (loghead 1 (bool->bit (logbitp 11 (xr :msr *ia32_efer-idx* x86)))))))
           :in-theory (e/d* (ia32e-la-to-pa) ()))))

;; ======================================================================
