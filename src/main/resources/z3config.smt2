; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; Requires Z3 >= 4.3.2

; ATTENTION: Continuing multi-line statements must be indented with at least
;            one tab or two spaces. All other lines must not start with tabs
;            or more than one space.

; Currently, print-success MUST come first, because it guarantees that every query to Z3, including
; setting options, is answered by a success (or error) reply from Z3. Silicon currently relies on
; these replies when it interacts with Z3 via stdio.
(set-option :print-success true) ; Boogie: false

(set-option :global-decls true) ; Boogie: default
(set-option :auto_config false) ; Usually a good idea

; Syntax for 4.3.0 <= Z3 < 4.3.2
;(set-option :mbqi false)
;(set-option :model-v2 true)
;(set-option :phase_selection 0)
;(set-option :restart_strategy 0)
;(set-option :restart_factor |1.5|)
;(set-option :arith-random_initial_value true)
;(set-option :case_split 3)
;(set-option :delay_units true)
;(set-option :delay_units_threshold 16)
;(set-option :nnf-sk_hack true)
;(set-option :qi-eager_threshold 100)
;(set-option :qi-cost |"(+ weight generation)"|)
;(set-option :type_check true)
;(set-option :bv-reflect true)
;;(set-option :qi_profile true)
;;(set-option :default_qid true)
;;(set-option :macro_finder true)

; Syntax for Z3 >= 4.3.2
(set-option :smt.mbqi false)
; (set-option :sat.random_seed 0)
; (set-option :produce-models true)
;(set-option :model false)
(set-option :model.v2 true)
; (set-option :model.compact true)
(set-option :smt.phase_selection 0)
(set-option :smt.restart_strategy 0)
(set-option :smt.restart_factor |1.5|)
(set-option :smt.arith.random_initial_value true)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :smt.delay_units_threshold 16)
(set-option :nnf.sk_hack true)
(set-option :smt.qi.eager_threshold 100)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :type_check true)
(set-option :smt.bv.reflect true)
;(set-option :smt.qi.profile true)
;(set-option :smt.qi.profile_freq 100000)
;(set-option :smt.macro_finder true)
;(set-option :combined_solver.solver2_timeout 500)
;(set-option :combined_solver.solver2_unknown 2)
;(set-option :smt.arith.nl false)
; (set-option :smt.arith.nl.gb false)
    ; See http://stackoverflow.com/questions/28210673
