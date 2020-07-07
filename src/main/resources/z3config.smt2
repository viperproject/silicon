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

(set-option :smt.restart_strategy 0)
(set-option :smt.restart_factor |1.5|)
(set-option :smt.case_split 3)
(set-option :smt.delay_units true)
(set-option :smt.delay_units_threshold 16)
(set-option :nnf.sk_hack true)
(set-option :type_check true)
(set-option :smt.bv.reflect true)

(set-option :smt.mbqi false)
(set-option :smt.qi.eager_threshold 100)
; (set-option :smt.qi.lazy_threshold 1000000000)
(set-option :smt.qi.cost "(+ weight generation)")
(set-option :smt.qi.max_multi_patterns 1000)
; (set-option :smt.qi.profile true)
; (set-option :smt.qi.profile_freq 100000)

;; [2019-07-31 Malte] The next block of options are all randomness-related options that I could
;; find in the description Z3 -pd emits. If not stated otherwise, the options are merely explicitly
;; set to their default values.
(set-option :smt.phase_selection 0) ; default: 3, Boogie: 0
(set-option :sat.phase caching)
(set-option :sat.random_seed 0)
(set-option :nlsat.randomize true)
(set-option :nlsat.seed 0)
(set-option :nlsat.shuffle_vars false)
(set-option :fp.spacer.order_children 0) ; Not available with Z3 4.5
(set-option :fp.spacer.random_seed 0) ; Not available with Z3 4.5
(set-option :smt.arith.random_initial_value true) ; Boogie: true
(set-option :smt.random_seed 0)
(set-option :sls.random_offset true)
(set-option :sls.random_seed 0)
(set-option :sls.restart_init false)
(set-option :sls.walksat_ucb true)

; (set-option :smt.macro_finder true)
; (set-option :combined_solver.solver2_timeout 500)
; (set-option :combined_solver.solver2_unknown 2)
; (set-option :smt.arith.nl false)
; (set-option :smt.arith.nl.gb false)
    ; See http://stackoverflow.com/questions/28210673

; (set-option :produce-models true)
; (set-option :model false)
(set-option :model.v2 true)
; (set-option :model.compact true)
