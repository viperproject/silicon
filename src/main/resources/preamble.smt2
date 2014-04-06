; Requires Z3 4.3.0

; ATTENTION: Continuing multi-line statements must be indented with at least
;            one tab or two spaces. All other lines must not start with tabs
;            or more than one space.

; Currently, print-success MUST come first, because it guarantees that every query to Z3, including
; setting options, is answered by a success (or error) reply from Z3. Silicon currently relies on
; these replies when it interacts with Z3 via stdio.
(set-option :print-success true) ; Boogie: false

(set-option :global-decls true) ; Boogie: default
(set-option :AUTO_CONFIG false) ; Usually a good idea

; Don't try to find models. Z3 would otherwise try to find models for uninterpreted (limited)
; functions that come from the program.
(set-option :MBQI false)

; [Malte] The remaining options were taken from the Boogie preamble when I compared Syxc and
; VCG-Chalice for the VSTTE12 paper. I have no clue what these options do and how important
; they are.
(set-option :MODEL-V2 true)
(set-option :PHASE_SELECTION 0)
(set-option :RESTART_STRATEGY 0)
(set-option :RESTART_FACTOR |1.5|)
(set-option :ARITH-RANDOM_INITIAL_VALUE true)
(set-option :CASE_SPLIT 3) ; Unsupported in Z3 4.3.2-nightlies?
(set-option :DELAY_UNITS true)
(set-option :DELAY_UNITS_THRESHOLD 16)
(set-option :NNF-SK_HACK true)
(set-option :QI-EAGER_THRESHOLD 100)
(set-option :QI-COST |"(+ weight generation)"|) ; Unsupported in Z3 4.3.2-nightlies?
(set-option :TYPE_CHECK true)
(set-option :BV-REFLECT true)

; (set-option :QI_PROFILE true)
; (set-option :DEFAULT_QID true)

; --- Snapshots ---

(declare-datatypes () ((
    $Snap $Snap.unit
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))

; --- References ---

(declare-sort $Ref)
(declare-const $Ref.null $Ref)
(declare-const x $Ref)
(declare-fun $Ref.nullTrigger ($Ref) Bool)

; --- Permissions ---

(define-sort $Perm () Real)

(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)

(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))

(define-fun $Perm.isReadVar ((p $Perm) (ub $Perm)) Bool
  (and ($Perm.isValidVar p)
	     (not (= p $Perm.No))
       (< (* 1000.0 p) $Perm.Write)))

; min function for permissions
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))

; --- Sort wrappers ---

; Sort wrappers are no longer part of the static preamble. Instead, they are
; emitted as part of the program-specific preamble.

; --- Arrays ---

(define-sort Array$Ref$Ref () (Array $Ref $Ref))
(define-sort Array$RefInt () (Array $Ref Int))

; --- Math ---

;function Math#min(a: int, b: int): int;
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))

;function Math#clip(a: int): int;
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) (- a) a))

; --- End static preamble ---

; (get-proof "stdout")
; (get-info :all-statistics)

; (push)
; (check-sat)
; (pop)
