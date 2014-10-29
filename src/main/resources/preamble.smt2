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
(set-option :model.v2 true)
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
(set-option :smt.bv.reflect true)
;(set-option :smt.qi_profile true)
;(set-option :smt.default_qid true) ; Not supported in Z3 4.3.2?
;(set-option :smt.macro_finder true)

; --- Snapshots ---

(declare-datatypes () ((
    $Snap $Snap.unit
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))

; --- References ---

(declare-sort $Ref)
(declare-const $Ref.null $Ref)

; --- Permissions ---

(define-sort $Perm () Real)

(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)

(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))

(define-fun $Perm.isReadVar ((p $Perm) (ub $Perm)) Bool
    (and ($Perm.isValidVar p)
         (not (= p $Perm.No))
         (< p $Perm.Write)))

; min function for permissions
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))

; --- Sort wrappers ---

; Sort wrappers are no longer part of the static preamble. Instead, they are
; emitted as part of the program-specific preamble.

; --- Math ---

;function Math#min(a: int, b: int): int;
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))

;function Math#clip(a: int): int;
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) 0 a))

; --- End static preamble ---

; (get-proof "stdout")
; (get-info :all-statistics)

; (push)
; (check-sat)
; (pop)
