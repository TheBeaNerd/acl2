; A lightweight book about the built-in function read-byte$.
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/channel-contents" :dir :system)
(local (include-book "kestrel/utilities/state" :dir :system))
(local (include-book "channels"))
(local (include-book "kestrel/lists-light/cons" :dir :system))
(local (include-book "kestrel/lists-light/cdr" :dir :system))

;; So the rules in the book fire
(in-theory (disable mv-nth read-byte$))

(local (in-theory (disable open-input-channels
                           open-input-channel-p1
                           open-input-channel-p
                           update-open-input-channels
                           member-equal)))

;; ;move
;; (defthm update-open-input-channels-of-open-input-channels
;;   (implies (state-p state) ; or (consp state)
;;            (equal (update-open-input-channels (open-input-channels state) state)
;;                   state))
;;   :hints (("Goal" :in-theory (enable open-input-channels update-open-input-channels))))

(local
 (defthm cadr-of-cadr-of-assoc-equal-of-open-input-channels-when-open-input-channel-p1
   (implies (open-input-channel-p1 channel typ state)
            (equal (cadr (cadr (assoc-equal channel (open-input-channels state))))
                   typ))
   :hints (("Goal" :in-theory (enable open-input-channel-p1)))))

(local
 (defthm cadr-of-cadr-of-assoc-equal-of-open-input-channels-when-open-input-channel-p
   (implies (open-input-channel-p channel typ state)
            (equal (cadr (cadr (assoc-equal channel (open-input-channels state))))
                   typ))
   :hints (("Goal" :in-theory (enable open-input-channel-p)))))


;move
(local
 (defthm open-input-channel-p1-of-update-open-input-channels-of-add-pair-same
  (equal (open-input-channel-p1 channel
                                typ
                                (update-open-input-channels (add-pair channel val (open-input-channels state))
                                                            state))
         (equal (cadr (car val))
                typ))
  :hints (("Goal" :in-theory (enable open-input-channel-p1)))))

;move
(local
 (defthm open-input-channel-p1-of-update-open-input-channels-of-add-pair-diff
  (implies (not (equal channel channel2))
           (equal (open-input-channel-p1 channel
                                         typ
                                         (update-open-input-channels (add-pair channel2 val channels)
                                                                     state))
                  (open-input-channel-p1 channel
                                         typ
                                         (update-open-input-channels channels
                                                                     state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p1)))))

;; Trying to introduce some abstractions to the channel machinery
(local
 (defund channel-header-type (header)
  (cadr header)))

(local
 (defthm channel-header-type-of-cadr-of-assoc-equal-of-open-input-channels
  (implies (open-input-channel-p1 channel typ state)
           (equal (channel-header-type
                   (cadr (assoc-equal channel (open-input-channels state))))
                  typ))
  :hints (("Goal" :in-theory (enable open-input-channel-p1 channel-header-type)))))

;move
(local
 (defthm open-input-channel-p1-of-update-open-input-channels-of-add-pair-both
  (equal (open-input-channel-p1 channel typ (update-open-input-channels (add-pair channel2 val channels) state))
         (if (equal channel channel2)
             (equal (channel-header-type (car val)) typ)
           (open-input-channel-p1 channel typ (update-open-input-channels channels state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p1 channel-header-type)))))

;; Note that this doesn't assume state-p.
(defthm open-input-channel-p1-of-update-open-input-channels-of-open-input-channels-same
  (implies (open-input-channel-p1 channel typ state)
           (open-input-channel-p1 channel typ
                                  (update-open-input-channels (open-input-channels state) state) ; just state, if we know state-p
                                  ))
  :hints (("Goal" :in-theory (enable open-input-channel-p1))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm state-p1-of-mv-nth-1-of-read-byte$
  (implies (state-p1 state)
           (equal (state-p1 (mv-nth 1 (read-byte$ channel state)))
                  (and (assoc-equal channel (open-input-channels state))
                       (symbolp channel))))
  :hints (("Goal" :in-theory (enable read-byte$))))

(defthm state-p-of-mv-nth-1-of-read-byte$
  (implies (state-p1 state)
           (equal (state-p (mv-nth 1 (read-byte$ channel state)))
                  (and (assoc-equal channel (open-input-channels state))
                       (symbolp channel))))
  :hints (("Goal" :in-theory (enable state-p))))

(defthm open-input-channel-p1-of-mv-nth-1-of-read-byte$
  (implies (open-input-channel-p1 channel typ state)
           (open-input-channel-p1 channel typ (mv-nth 1 (read-byte$ channel2 state))))
  :hints (("Goal" :in-theory (enable read-byte$))))

(defthm open-input-channel-p-of-mv-nth-1-of-read-byte$
  (implies (open-input-channel-p channel typ state)
           (open-input-channel-p channel typ (mv-nth 1 (read-byte$ channel2 state))))
  :hints (("Goal" :in-theory (enable open-input-channel-p))))

(defthm open-input-channel-any-p1-of-mv-nth-1-of-read-byte$
  (implies (open-input-channel-any-p1 channel state)
           (open-input-channel-any-p1 channel (mv-nth 1 (read-byte$ channel2 state))))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p1))))

(defthm open-input-channels-of-mv-nth-1-of-read-byte$
  (implies (and (open-input-channel-p1 channel :byte state)
                (state-p1 state)
                )
           (equal (open-input-channels (mv-nth 1 (read-byte$ channel state)))
                  (if (cddr (assoc-equal channel (open-input-channels state)))
                      ;; more data to read:
                      (add-pair channel
                                (cons (cadr (assoc-equal channel (open-input-channels state))) ;header
                                      (cdddr (assoc-equal channel (open-input-channels state))) ;cdr of values
                                      )
                                (open-input-channels state))
                    ;; no more data to read:
                    (open-input-channels state))))
  :hints (("Goal" :in-theory (enable read-byte$ open-input-channel-p1))))

;; Reading gives a non-nil value iff the channel contents are non-empty
(defthm mv-nth-0-of-read-byte$-iff
  (implies (and (open-input-channel-p channel :byte state)
                (state-p1 state))
           (iff (mv-nth 0 (read-byte$ channel state))
                (consp (channel-contents channel state)
                       ;; (cddr (assoc-equal channel (open-input-channels state)))
                       )))
  :hints (("Goal" :use (:instance nat-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                                  (channels (open-input-channels state)))
           :in-theory (e/d (read-byte$ channel-contents)
                           (nat-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                            true-listp)))))

(defthm integer-of-mv-nth-0-of-read-byte$-iff
  (implies (and (open-input-channel-p channel :byte state)
                (state-p1 state))
           (iff (integerp (mv-nth 0 (read-byte$ channel state)))
                (mv-nth 0 (read-byte$ channel state))))
  :hints (("Goal" :use (:instance nat-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                                  (channels (open-input-channels state)))
           :in-theory (e/d (read-byte$ channel-contents)
                           (nat-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                            true-listp)))))

(defthm unsigned-byte-p-of-mv-nth-0-of-read-byte$-iff
  (implies (and (open-input-channel-p channel :byte state)
                (state-p1 state))
           (iff (unsigned-byte-p 8 (mv-nth 0 (read-byte$ channel state)))
                (mv-nth 0 (read-byte$ channel state))))
  :hints (("Goal" :use (:instance unsigned-byte-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                                  (channels (open-input-channels state)))
           :in-theory (e/d (read-byte$ channel-contents UNSIGNED-BYTE-LISTP)
                           (unsigned-byte-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                            true-listp)))))

(defthm not-<-of-and-mv-nth-0-of-read-byte$
  (implies (and (open-input-channel-p channel :byte state)
                (state-p1 state))
           (not (< (mv-nth 0 (read-byte$ channel state))
                   0)))
  :hints (("Goal" :use (:instance nat-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                                  (channels (open-input-channels state)))
           :in-theory (e/d (read-byte$ channel-contents open-input-channel-p1)
                           (nat-listp-of-cddr-of-assoc-equal-when-open-channel-listp
                            true-listp)))))

;; (defthm <-of-and-mv-nth-0-of-read-byte$-and-256
;;   (implies (and (open-input-channel-p channel :byte state)
;;                 (state-p1 state))
;;            (< (mv-nth 0 (read-byte$ channel state))
;;               256))
;;   :hints (("Goal" :use (:instance nat-listp-of-cddr-of-assoc-equal-when-open-channel-listp
;;                                   (channels (open-input-channels state)))
;;            :in-theory (e/d (read-byte$ channel-contents)
;;                            (nat-listp-of-cddr-of-assoc-equal-when-open-channel-listp
;;                             true-listp)))))

(defthm <-of-len-of-channel-contents-of-mv-nth-1-of-read-byte$
  (implies (consp (channel-contents channel state))
           (< (len (channel-contents channel (mv-nth 1 (read-byte$ channel state))))
              (len (channel-contents channel state))))
  :hints (("Goal" :in-theory (enable read-byte$ channel-contents))))

;; this version has channel-contents inlined
;; or perhaps make a rule for (open-input-channels (mv-nth 1 (read-byte$ channel state)))
(defthm <-of-len-of-channel-contents-of-mv-nth-1-of-read-byte$-alt
  (implies (consp (cddr (assoc-equal channel (open-input-channels state))))
           (< (len (cddr (assoc-equal channel (open-input-channels (mv-nth 1 (read-byte$ channel state))))))
              (len (cddr (assoc-equal channel (open-input-channels state))))))
  :hints (("Goal" :in-theory (enable read-byte$ channel-contents))))
