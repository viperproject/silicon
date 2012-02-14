; Tested with Z3 3.2
;
; ATTENTION: Continuing multi-line statements must be indented with at least
;            one tab or two spaces. All other lines must not start with tabs
;            or more than one space.

; --- Z3 configurations ---	

(set-option :print-success true) ; Boogie: false
; (set-option :print-warning false) ; Boogie: default
(set-option :global-decls true) ; Boogie: default

(set-option :AUTO_CONFIG false)
(set-option :MODEL_HIDE_UNUSED_PARTITIONS false)
(set-option :MODEL_V2 true)
(set-option :ASYNC_COMMANDS false)
(set-option :PHASE_SELECTION 0)
(set-option :RESTART_STRATEGY 0)
(set-option :RESTART_FACTOR |1.5|)
(set-option :ARITH_RANDOM_INITIAL_VALUE true)
(set-option :CASE_SPLIT 3)
(set-option :DELAY_UNITS true)
(set-option :DELAY_UNITS_THRESHOLD 16)
(set-option :NNF_SK_HACK true)
(set-option :MBQI false)
(set-option :QI_EAGER_THRESHOLD 100)
(set-option :QI_COST |"(+ weight generation)"|)
(set-option :TYPE_CHECK true)
(set-option :BV_REFLECT true)
; (set-option :QI_PROFILE true)
; (set-option :DEFAULT_QID true)

; (set-info :smt-lib-version 2.0)
; (set-info :category "industrial")

; (set-option :SOFT_TIMEOUT 5000)
; (set-option :soft-timeout 5000)

; --- Misc ---

(declare-sort $Ref)

; --- Permissions ---

; (declare-sort $Perms)
; (declare-const $Perms.Write $Perms)
(declare-const $Perms.Write Int)
(declare-const $Perms.Zero Int)

(assert (< $Perms.Zero $Perms.Write))

; (get-proof "stdout")
; (get-info statistics)

; (push)
; (check-sat)
; (pop)