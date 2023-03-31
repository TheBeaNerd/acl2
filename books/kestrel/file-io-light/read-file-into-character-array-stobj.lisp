; A lightweight function to read a file into a stobj array of characters
;
; Copyright (C) 2021-2023 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; (include-book "kestrel/utilities/channel-contents" :dir :system)
(local (include-book "file-length-dollar"))
(local (include-book "open-input-channel"))
(local (include-book "channels"))
(local (include-book "read-char-dollar"))
(local (include-book "kestrel/lists-light/cons" :dir :system))

(local (in-theory (disable assoc-equal
                           channel-contents
                           open-input-channels
                           open-input-channel-p
                           open-input-channel-p1
                           state-p
                           update-nth
                           nth
                           member-equal
                           open-input-channel-any-p1
                           )))

;; A stobj with a single field, which is a character array.
(defstobj character-array-stobj
  (characters :type (array character (0)) ; initially empty
              :initially #\_ ; initial value of each character (TODO: What is best here?)
              :resizable t))

;; Names generated by defstobj:
(in-theory (disable character-array-stobjp characters-length resize-characters charactersi update-charactersi))

;; Returns (mv character-array-stobj state).
(defund read-file-into-character-array-stobj-aux (channel next-index character-array-stobj state)
  (declare (xargs :guard (and (symbolp channel)
                              (natp next-index)
                              (open-input-channel-p channel :character state))
                  :stobjs (character-array-stobj state)
                  :measure (len (cddr (assoc-equal channel (open-input-channels state))) ;;(channel-contents channel state)
                                )
                  :hints (("Goal" :in-theory (enable channel-contents)))
                  :guard-hints (("Goal" :in-theory (enable open-input-channel-p
                                                           )))))
  (if (not (mbt (and (open-input-channel-p channel :character state) ; for termination
                     (state-p state))))
      (mv character-array-stobj state)
    (mv-let (maybe-character state)
      (read-char$ channel state)
      (if (not maybe-character) ; no more characters
          (if (= (characters-length character-array-stobj) next-index)
              (mv character-array-stobj state)
            (prog2$ (er hard? 'read-file-into-character-array-stobj-aux "Too few characters in file.") ; should not happen
                    (mv character-array-stobj state)))
        ;; at least one more character:
        (if (<= (characters-length character-array-stobj) next-index)
            (prog2$ (er hard? 'read-file-into-character-array-stobj-aux "Too many characters in file.") ; should not happen
                    (mv character-array-stobj state))
          (let ((character-array-stobj (update-charactersi next-index maybe-character character-array-stobj)))
            (read-file-into-character-array-stobj-aux channel
                                                      (+ 1 next-index)
                                                      character-array-stobj
                                                      state)))))))

(defthm state-p1-of-mv-nth-1-of-read-file-into-character-array-stobj-aux
  (implies (and (symbolp channel)
                ;; (open-input-channel-p channel :character state)
                (state-p1 state))
           (state-p1 (mv-nth 1 (read-file-into-character-array-stobj-aux channel next-index character-array-stobj state))))
  :hints (("Goal" :in-theory (enable read-file-into-character-array-stobj-aux
                                     open-input-channel-p
                                     open-input-channel-p1))))

(defthm open-input-channel-p1-of-mv-nth-1-of-read-file-into-character-array-stobj-aux
  (implies (and (symbolp channel)
                (open-input-channel-p1 channel typ state)
                (state-p1 state)
                )
           (open-input-channel-p1 channel typ (mv-nth 1 (read-file-into-character-array-stobj-aux
                                                         channel ; gen to channel2?
                                                         next-index character-array-stobj state))))
  :hints (("Goal" :in-theory (enable read-file-into-character-array-stobj-aux))))

(defthm open-input-channel-any-p1-of-mv-nth-1-of-read-file-into-character-array-stobj-aux
  (implies (and (symbolp channel)
                (open-input-channel-any-p1 channel state)
                (state-p1 state))
           (open-input-channel-any-p1 channel (mv-nth 1 (read-file-into-character-array-stobj-aux
                                                         channel ; gen to channel2?
                                                         next-index character-array-stobj state))))
  :hints (("Goal" :in-theory (enable open-input-channel-any-p1))))

;; Returns (mv erp character-array-stobj state) where either ERP is non-nil (meaning an error
;; occurred) or else the characters field of CHARACTER-ARRAY-STOBJ contains the contents of FILENAME.
(defund read-file-into-character-array-stobj (filename character-array-stobj state)
  (declare (xargs :guard (stringp filename)
                  :stobjs (character-array-stobj state)))
  (mv-let (file-length state)
    (file-length$ filename state)
    (if (not file-length)
        (mv `(:failed-to-get-file-length ,filename) character-array-stobj state)
      (mv-let (channel state)
        (open-input-channel filename :character state)
        (if (not channel)
            ;; Error:
            (mv `(:could-not-open-channel ,filename) character-array-stobj state)
          (let ( ;; make the array the right size:
                (character-array-stobj (resize-characters file-length character-array-stobj)))
            (mv-let (character-array-stobj state)
              (read-file-into-character-array-stobj-aux channel 0 character-array-stobj state)
              (let ((state (close-input-channel channel state)))
                (mv nil ; no error
                    character-array-stobj
                    state)))))))))
