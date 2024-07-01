; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; Tested with Z3 4.8.7 and 4.12.1

; ATTENTION: Continuing multi-line statements must be indented with at least
;            one tab or two spaces. All other lines must not start with tabs
;            or more than one space.

; Currently, print-success MUST come first, because it guarantees that every query to Z3, including
; setting options, is answered by a success (or error) reply from Z3. Silicon currently relies on
; these replies when it interacts with Z3 via stdio.
(set-option :print-success true) ; Boogie: false
(set-option :global-decls true) ; Necessary for push pop mode

; These options are taken from Dafny 4.0.0 and proven to work decently well with up-to-date Z3 (currently 4.12.1),
; unlike the options used previously.
(set-option :auto_config false)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :type_check true)
(set-option :smt.mbqi false)
(set-option :pp.bv_literals false)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.arith.solver 2)
(set-option :model.v2 true)
(set-option :model.partial true)

; We want unlimited multipatterns
(set-option :smt.qi.max_multi_patterns 1000)
