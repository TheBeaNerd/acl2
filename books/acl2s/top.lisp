#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "portcullis")
(begin-book t :ttags :all);$ACL2s-Preamble$|#

#|

We don't use ever include top.lisp when building acl2s, although due
to a query by Eric Smith, we updated the file so that including it
doesn't cause ACL2 to hang.

If you're interested in building acl2s, there is a repo with scripts
for doing that here:
https://gitlab.com/acl2s/external-tool-support/scripts. That's useful
for the emacs version. For the eclipse version see
https://www.cs.utexas.edu/users/moore/acl2/manuals/latest/index.html?topic=ACL2S____ACL2S-INSTALLATION.

If you're interested in using acl2 to certify books developed with
acl2s, you can use a cert.acl2 file that contains the following forms
as well as any forms you might want for controlling other parameters
such as timeouts.

(include-book "acl2s/ccg/ccg" :dir :system :ttags :all)
(include-book "acl2s/custom" :dir :system :ttags :all)
(acl2s-common-settings)
; cert-flags: ? t :ttags :all :skip-proofs-okp t
(in-package "ACL2S")

|#


(in-package "ACL2S")

(include-book "acl2s/acl2s-size" :dir :system :ttags :all)
(include-book "acl2s/ccg/ccg" :uncertified-okp nil :dir :system :ttags
              ((:ccg)) :load-compiled-file nil)
(include-book "acl2s/base-theory" :dir :system :ttags :all)
(include-book "acl2s/custom" :dir :system :ttags :all)
(include-book "acl2s/acl2s-sigs" :dir :system :ttags :all)
;(include-book "projects/smtlink/top" :dir :system :ttags :all)
;(include-book "projects/smtlink/examples/basictypes" :dir :system :ttags :all)
(include-book "acl2s/sorting/sorting" :dir :system :ttags :all)
(include-book "acl2s/match" :dir :system :ttags :all)
(include-book "acl2s/installation" :dir :system :ttags :all)
(include-book "acl2s/extra-doc" :dir :system :ttags :all)
(include-book "acl2s/interface/top" :dir :system)
(include-book "acl2s/interface/acl2s-utils/top" :dir :system)
(acl2::acl2s-common-settings)

#|

; Hack for cert.pl ;

(include-book "acl2s/mode-acl2s-dependencies" :dir :system :ttags :all)
(include-book "acl2s/defdata-testing" :dir :system :ttags :all)
(include-book "acl2s/cgen/cgen-no-thms" :dir :system)
(include-book "acl2s/cgen/defthm-support-for-on-failure" :dir :system)
(include-book "acl2s/cgen/defthm-support-for-on-failure-local" :dir :system)

(include-book "acl2s/defunc-testing" :dir :system)
(include-book "acl2s/match-testing" :dir :system)
(include-book "acl2s/cgen-testing" :dir :system)

(include-book "acl2s/distribution/acl2s-hooks/acl2s-book-support" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/acl2s" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/canonical-print" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/categorize-input" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/interaction-hooks" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/markup-hooks" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/protection-hooks" :dir :system)
(include-book "acl2s/distribution/acl2s-hooks/super-history" :dir :system)

|#
