; Started: 2014-09-17 17:38:54
; Silicon.buildVersion: 0.1-SNAPSHOT 84a1fa82a743+ default 2014/09/17 17:28:59
; ------------------------------------------------------------
; Preamble start
; 
; ; /preamble.smt2
(set-option :print-success true) ; Boogie: false
(set-option :global-decls true) ; Boogie: default
(set-option :AUTO_CONFIG false) ; Usually a good idea
(set-option :MBQI false)
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

(set-option :QI_PROFILE true)
(set-option :DEFAULT_QID true)
(set-option :QI_PROFILE_FREQ  10000)

(declare-sort $Ref)
(declare-const $Ref.null $Ref)
(declare-sort $Set<$Ref>)
(declare-fun $Set.in ($Ref $Set<$Ref>) Bool)

; Declaring program functions

; ---------- goo ----------
(declare-const x $Ref)
(declare-const xs $Set<$Ref>)

(declare-fun inv1 ($Ref) $Ref)
(declare-fun inv2 ($Ref) $Ref)

(assert (forall ((x $Ref)) (!
  (implies
    ($Set.in (inv1 x) xs)
    (not (= x $Ref.null))
    )
  ; :pattern (($Set.in x xs))
  :pattern (($Set.in (inv1 x) xs)))))

(assert (forall ((x $Ref)) (!
  (implies
    ($Set.in (inv2 x) xs)
    (not (= x $Ref.null)))
  ; :pattern (($Set.in x xs))
  :pattern (($Set.in (inv2 x) xs)))))

(push) ; 5
(assert (not ($Set.in x xs)))
(check-sat)
(pop) ; 5
