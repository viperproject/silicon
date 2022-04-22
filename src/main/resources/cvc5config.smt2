; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; Requires CVC5 >= 1.0.0
(set-option :print-success true)

(set-logic ALL)
(set-option :seed 0)
(set-option :sat-random-seed 0)

; default options as used by boogie
(set-option :incremental true) ; required for push and pop
(set-option :condense-function-values false)
(set-option :strict-parsing false)
(set-option :produce-models true) ; enabled to support proverStdIO. retrieveAndSaveModel

; Translated from z3config
(set-option :global-declarations true)
(set-option :type-checking true)
