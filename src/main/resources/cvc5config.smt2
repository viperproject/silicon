; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; Requires CVC5 >= 0.0.4
(set-option :print-success true)

(set-logic ALL)
(set-option :random-seed 0)
(set-option :seed 0)
;(set-option :timeout 100) ; needed in preamble rather than as in Z3 where it's declared later.

; default options as used by boogie
(set-option :incremental true) ; required for push and pop
(set-option :condense-function-values false)
(set-option :strict-parsing false)

; Translated from z3config
(set-option :global-declarations true)
