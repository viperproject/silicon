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

; --- Snapshots ---

(declare-sort $Snap)

(declare-const $unit $Snap)

(declare-fun $combine ($Snap $Snap) $Snap)
(declare-fun $snapEq ($Snap $Snap) Bool)

(assert (forall ((x1 $Snap) (x2 $Snap) (y1 $Snap) (y2 $Snap)) (!
	(implies
		($snapEq ($combine x1 y1) ($combine x2 y2))
		(and (= x1 x2) (= y1 y2)))
	:qid |Combine|
	:pattern (($snapEq ($combine x1 y1) ($combine x2 y2)))
	)))
	
(assert (forall ((x $Snap) (y $Snap)) (!
	(implies
		($snapEq x y)
		(and (= x y)))
	:qid |SnapEq|
	:pattern (($snapEq x y))
	)))

; --- References ---

(declare-sort $Ref)

(declare-const $null $Ref)

; --- Permissions ---

(define-sort $Perms () Int)
(declare-const $Perms.Write $Perms)
(declare-const $Perms.Zero $Perms)

(assert (= $Perms.Zero 0))
(assert (< $Perms.Zero $Perms.Write))

; --- Sort wrappers ---

(declare-fun $sorts.$SnapToInt ($Snap) Int)
(declare-fun $sorts.IntTo$Snap (Int) $Snap)

(assert (forall ((x Int))
	(= x ($sorts.$SnapToInt($sorts.IntTo$Snap x)))))

(assert (forall ((x $Snap))
	(= x ($sorts.IntTo$Snap($sorts.$SnapToInt x)))))

(declare-fun $sorts.$SnapTo$Ref ($Snap) $Ref)
(declare-fun $sorts.$RefTo$Snap ($Ref) $Snap)

(assert (forall ((x $Ref))
	(= x ($sorts.$SnapTo$Ref($sorts.$RefTo$Snap x)))))

(assert (forall ((x $Snap))
	(= x ($sorts.$RefTo$Snap($sorts.$SnapTo$Ref x)))))

; --- Domains ---

(declare-sort Pair<$Ref~Int>)

(declare-fun Pair<$Ref~Int>.create ($Ref Int) Pair<$Ref~Int>)
(declare-fun Pair<$Ref~Int>.getFirst (Pair<$Ref~Int>) $Ref)
(declare-fun Pair<$Ref~Int>.getSecond (Pair<$Ref~Int>) Int)

(assert (forall ((r $Ref) (i Int)) (!
  (= (Pair<$Ref~Int>.getFirst (Pair<$Ref~Int>.create r i)) r)
  :qid |Pair<$Ref~Int>.getFirst|)))

(assert (forall ((r $Ref) (i Int)) (!
  (= (Pair<$Ref~Int>.getSecond (Pair<$Ref~Int>.create r i)) i)
  :qid |Pair<$Ref~Int>.getSecond|)))

(assert (forall ((r1 $Ref) (i1 Int) (r2 $Ref) (i2 Int)) (!
  (iff
    (and (= r1 r2) (= i1 i2))
    (= (Pair<$Ref~Int>.create r1 i1) (Pair<$Ref~Int>.create r2 i2)))
  :qid |Pair<$Ref~Int>.equality|)))
  

  
(declare-sort Map<Pair<$Ref~Int>~$Perms>)

(declare-const Map<Pair<$Ref~Int>~$Perms>.empty Map<Pair<$Ref~Int>~$Perms>)

(declare-fun Map<Pair<$Ref~Int>~$Perms>.get (Map<Pair<$Ref~Int>~$Perms> Pair<$Ref~Int>) $Perms)

(declare-fun Map<Pair<$Ref~Int>~$Perms>.has (Map<Pair<$Ref~Int>~$Perms> Pair<$Ref~Int>) Bool)

(declare-fun Map<Pair<$Ref~Int>~$Perms>.update (Map<Pair<$Ref~Int>~$Perms> Pair<$Ref~Int> $Perms) Map<Pair<$Ref~Int>~$Perms>)

(assert (forall ((p Pair<$Ref~Int>)) (!
  (not
    (Map<Pair<$Ref~Int>~$Perms>.has Map<Pair<$Ref~Int>~$Perms>.empty p))
  :qid |Map<Pair<$Ref~Int>~$Perms>.empty_has_no_entries|)))

(assert (forall ((m Map<Pair<$Ref~Int>~$Perms>) (p1 Pair<$Ref~Int>) (p2 Pair<$Ref~Int>) (p $Perms)) (!
  (ite
    (= p1 p2)
    (=
      (Map<Pair<$Ref~Int>~$Perms>.get (Map<Pair<$Ref~Int>~$Perms>.update m p1 p) p2)
      (Map<Pair<$Ref~Int>~$Perms>.get m p2))
    (=
      (Map<Pair<$Ref~Int>~$Perms>.get (Map<Pair<$Ref~Int>~$Perms>.update m p1 p) p2)
      p))
  :qid |Map<Pair<$Ref~Int>~$Perms>.get_update|)))

; (get-proof "stdout")
; (get-info statistics)

; (push)
; (check-sat)
; (pop)