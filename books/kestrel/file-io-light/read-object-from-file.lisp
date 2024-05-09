; A lightweight function to read an object from a file
;
; Copyright (C) 2021-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "open-input-channel"))
(local (include-book "close-input-channel"))
(local (include-book "read-object"))
(local (include-book "channels"))
(local (include-book "kestrel/utilities/state" :dir :system))

(local (in-theory (disable open-input-channel-any-p1)))

;; Returns (mv erp object state) where either ERP is non-nil (meaning an error
;; occurred) or else OBJECT is the first ACL2 object in the file.
;; TODO: Add option to set the package of the symbols read in? (See read-objects-from-file-with-pkg).
(defund read-object-from-file (filename state)
  (declare (xargs :guard (stringp filename)
                  :stobjs state))
  (mv-let (channel state)
    (open-input-channel filename :object state)
    (if (not channel)
        ;; Error:
        (mv `(:could-not-open-channel ,filename) nil state)
      (mv-let (eof maybe-object state)
        (read-object channel state)
        (let ((state (close-input-channel channel state)))
          (if eof
              ;; Error (no objects in file):
              (mv `(:end-of-file ,filename) nil state)
            (mv nil ; no error
                maybe-object
                state)))))))

(defthm state-p1-of-mv-nth-2-of-read-object-from-file
  (implies (and (stringp filename)
                (state-p1 state))
           (state-p1 (mv-nth 2 (read-object-from-file filename state))))
  :hints (("Goal" :in-theory (enable read-object-from-file))))

(defthm state-p-of-mv-nth-2-of-read-object-from-file
  (implies (and (stringp filename)
                (state-p state))
           (state-p (mv-nth 2 (read-object-from-file filename state))))
  :hints (("Goal" :in-theory (enable read-object-from-file))))
