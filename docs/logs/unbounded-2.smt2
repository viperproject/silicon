(get-info :version)
; (:version "4.3")
; Started: 2014-09-02 17:02:46
; Silicon.buildVersion: 0.1-SNAPSHOT bfc2f234dc3c default 2014/09/01 12:49:07
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
(declare-datatypes () ((
    $Snap $Snap.unit
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
(declare-sort $Ref)
(declare-const $Ref.null $Ref)
(declare-const x $Ref)
(declare-fun $Ref.nullTrigger ($Ref) Bool)
(define-sort $Perm () Real)
(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)
(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))
(define-fun $Perm.isReadVar ((p $Perm) (ub $Perm)) Bool
    (and ($Perm.isValidVar p)
         (not (= p $Perm.No))
         (< p $Perm.Write)))
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) (- a) a))
(declare-sort $Set<Int>)
(declare-sort $Set<$Ref>)
(declare-sort NonNull)
(declare-sort $FVF<Int>)
; /sets_declarations_dafny.smt2 [Int]
(declare-fun $Set.in (Int $Set<Int>) Bool)
(declare-fun $Set.card ($Set<Int>) Int)
(declare-fun $Set.empty<Int> () $Set<Int>)
(declare-fun $Set.singleton (Int) $Set<Int>)
(declare-fun $Set.add ($Set<Int> Int) $Set<Int>)
(declare-fun $Set.union ($Set<Int> $Set<Int>) $Set<Int>)
(declare-fun $Set.intersection ($Set<Int> $Set<Int>) $Set<Int>)
(declare-fun $Set.difference ($Set<Int> $Set<Int>) $Set<Int>)
(declare-fun $Set.subset ($Set<Int> $Set<Int>) Bool)
(declare-fun $Set.eq ($Set<Int> $Set<Int>) Bool)
(declare-fun $Set.disjoint ($Set<Int> $Set<Int>) Bool)
; /sets_declarations_dafny.smt2 [Ref]
(declare-fun $Set.in ($Ref $Set<$Ref>) Bool)
(declare-fun $Set.card ($Set<$Ref>) Int)
(declare-fun $Set.empty<$Ref> () $Set<$Ref>)
(declare-fun $Set.singleton ($Ref) $Set<$Ref>)
(declare-fun $Set.add ($Set<$Ref> $Ref) $Set<$Ref>)
(declare-fun $Set.union ($Set<$Ref> $Set<$Ref>) $Set<$Ref>)
(declare-fun $Set.intersection ($Set<$Ref> $Set<$Ref>) $Set<$Ref>)
(declare-fun $Set.difference ($Set<$Ref> $Set<$Ref>) $Set<$Ref>)
(declare-fun $Set.subset ($Set<$Ref> $Set<$Ref>) Bool)
(declare-fun $Set.eq ($Set<$Ref> $Set<$Ref>) Bool)
(declare-fun $Set.disjoint ($Set<$Ref> $Set<$Ref>) Bool)
(declare-fun NN<Ref~Bool> ($Ref) Bool)
(assert true)
; /field_value_functions_declarations.smt2 [f: Int]
(declare-fun $FVF.domain_f ($FVF<Int>) $Set<$Ref>)
(declare-fun $FVF.lookup_f ($FVF<Int> $Ref) Int)
(declare-fun $FVF.lookup_f_inv (Int) $Ref)
; /sets_axioms_dafny.smt2 [Int]
(assert (forall ((xs $Set<Int>)) (!
	(<= 0 ($Set.card xs))
	:pattern (($Set.card xs))
	)))
(assert (forall ((x Int)) (!
	(not ($Set.in x $Set.empty<Int>))
	:pattern (($Set.in x $Set.empty<Int>))
	)))
(assert (forall ((xs $Set<Int>)) (!
	(and
		(iff
			(= ($Set.card xs) 0)
			(= xs $Set.empty<Int>))
		(iff
			(not (= ($Set.card xs) 0))
			(exists ((x Int)) (!
				($Set.in x xs)
				:pattern (($Set.in x xs))
				))))
	:pattern (($Set.card xs))
	)))
(assert (forall ((x Int)) (!
	($Set.in x ($Set.singleton x))
	:pattern (($Set.in x ($Set.singleton x)))
	)))
(assert (forall ((x Int) (y Int)) (!
	(iff
		($Set.in y ($Set.singleton x))
		(= x y))
	:pattern (($Set.in y ($Set.singleton x)))
	)))
(assert (forall ((x Int)) (!
	(= ($Set.card ($Set.singleton x)) 1)
	:pattern (($Set.card ($Set.singleton x)))
	)))
(assert (forall ((xs $Set<Int>) (x Int) (y Int)) (!
	(iff
		($Set.in y ($Set.add xs x))
		(or
			(= x y)
			($Set.in y xs)))
	:pattern (($Set.in y ($Set.add xs x)))
	)))
(assert (forall ((xs $Set<Int>) (x Int)) (!
	($Set.in x ($Set.add xs x))
	:pattern (($Set.in x ($Set.add xs x)))
	)))
(assert (forall ((xs $Set<Int>) (x Int) (y Int)) (!
	(implies
		($Set.in y xs)
		($Set.in y ($Set.add xs x)))
	:pattern (($Set.in y xs) ($Set.in y ($Set.add xs x)))
	)))
(assert (forall ((xs $Set<Int>) (x Int)) (!
	(implies
		($Set.in x xs)
		(= ($Set.card ($Set.add xs x)) ($Set.card xs)))
	:pattern (($Set.card ($Set.add xs x)))
	)))
(assert (forall ((xs $Set<Int>) (x Int)) (!
	(implies
		(not ($Set.in x xs))
		(= ($Set.card ($Set.add xs x)) (+ ($Set.card xs) 1)))
	:pattern (($Set.card ($Set.add xs x)))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>) (x Int)) (!
	(iff
		($Set.in x ($Set.union xs ys))
		(or
			($Set.in x xs)
			($Set.in x ys)))
	:pattern (($Set.in x ($Set.union xs ys)))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>) (x Int)) (!
	(implies
		($Set.in x xs)
		($Set.in x ($Set.union xs ys)))
	:pattern (($Set.in x ($Set.union xs ys)) ($Set.in x xs))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>) (x Int)) (!
	(implies
		($Set.in x ys)
		($Set.in x ($Set.union xs ys)))
	:pattern (($Set.in x ($Set.union xs ys)) ($Set.in x ys))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>)) (!
	(implies
		($Set.disjoint xs ys)
		(and
			(= ($Set.difference ($Set.union xs ys) xs) ys)
			(= ($Set.difference ($Set.union xs ys) ys) xs)))
	:pattern (($Set.union xs ys))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>) (x Int)) (!
	(iff
		($Set.in x ($Set.intersection xs ys))
		(and
			($Set.in x xs)
			($Set.in x ys)))
	:pattern (($Set.in x ($Set.intersection xs ys)))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>)) (!
	(=
		($Set.union ($Set.union xs ys) ys)
		($Set.union xs ys))
	:pattern (($Set.union ($Set.union xs ys) ys))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>)) (!
	(=
		($Set.union xs ($Set.union xs ys))
		($Set.union xs ys))
	:pattern (($Set.union xs ($Set.union xs ys)))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>)) (!
	(=
		($Set.intersection ($Set.intersection xs ys) ys)
		($Set.intersection xs ys))
	:pattern (($Set.intersection ($Set.intersection xs ys) ys))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>)) (!
	(=
		($Set.intersection xs ($Set.intersection xs ys))
		($Set.intersection xs ys))
	:pattern (($Set.intersection xs ($Set.intersection xs ys)))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>)) (!
	(=
		(+
			($Set.card ($Set.union xs ys))
			($Set.card ($Set.intersection xs ys)))
		(+
			($Set.card xs)
			($Set.card ys)))
	:pattern (($Set.card ($Set.union xs ys)))
	:pattern (($Set.card ($Set.intersection xs ys)))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>) (x Int)) (!
	(iff
		($Set.in x ($Set.difference xs ys))
		(and
			($Set.in x xs)
			(not ($Set.in x ys))))
	:pattern (($Set.in x ($Set.difference xs ys)))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>) (x Int)) (!
	(implies
		($Set.in x ys)
		(not ($Set.in x ($Set.difference xs ys))))
	:pattern (($Set.in x ($Set.difference xs ys)) ($Set.in x ys))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>)) (!
	(iff
		($Set.subset xs ys)
		(forall ((x Int)) (!
			(implies
				($Set.in x xs)
				($Set.in x ys))
			:pattern (($Set.in x xs))
			:pattern (($Set.in x ys))
			)))
	:pattern (($Set.subset xs ys))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>)) (!
	(iff
		($Set.eq xs ys)
		(forall ((x Int)) (!
			(iff
				($Set.in x xs)
				($Set.in x ys))
			:pattern (($Set.in x xs))
			:pattern (($Set.in x ys))
			)))
	:pattern (($Set.eq xs ys))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>)) (!
	(implies
		($Set.eq xs ys)
		(= xs ys))
	:pattern (($Set.eq xs ys))
	)))
(assert (forall ((xs $Set<Int>) (ys $Set<Int>)) (!
	(iff
		($Set.disjoint xs ys)
		(forall ((x Int)) (!
			(or
				(not ($Set.in x xs))
				(not ($Set.in x ys)))
			:pattern (($Set.in x xs))
			:pattern (($Set.in x ys))
			)))
	:pattern (($Set.disjoint xs ys))
	)))
; /sets_axioms_dafny.smt2 [Ref]
(assert (forall ((xs $Set<$Ref>)) (!
	(<= 0 ($Set.card xs))
	:pattern (($Set.card xs))
	)))
(assert (forall ((x $Ref)) (!
	(not ($Set.in x $Set.empty<$Ref>))
	:pattern (($Set.in x $Set.empty<$Ref>))
	)))
(assert (forall ((xs $Set<$Ref>)) (!
	(and
		(iff
			(= ($Set.card xs) 0)
			(= xs $Set.empty<$Ref>))
		(iff
			(not (= ($Set.card xs) 0))
			(exists ((x $Ref)) (!
				($Set.in x xs)
				:pattern (($Set.in x xs))
				))))
	:pattern (($Set.card xs))
	)))
(assert (forall ((x $Ref)) (!
	($Set.in x ($Set.singleton x))
	:pattern (($Set.in x ($Set.singleton x)))
	)))
(assert (forall ((x $Ref) (y $Ref)) (!
	(iff
		($Set.in y ($Set.singleton x))
		(= x y))
	:pattern (($Set.in y ($Set.singleton x)))
	)))
(assert (forall ((x $Ref)) (!
	(= ($Set.card ($Set.singleton x)) 1)
	:pattern (($Set.card ($Set.singleton x)))
	)))
(assert (forall ((xs $Set<$Ref>) (x $Ref) (y $Ref)) (!
	(iff
		($Set.in y ($Set.add xs x))
		(or
			(= x y)
			($Set.in y xs)))
	:pattern (($Set.in y ($Set.add xs x)))
	)))
(assert (forall ((xs $Set<$Ref>) (x $Ref)) (!
	($Set.in x ($Set.add xs x))
	:pattern (($Set.in x ($Set.add xs x)))
	)))
(assert (forall ((xs $Set<$Ref>) (x $Ref) (y $Ref)) (!
	(implies
		($Set.in y xs)
		($Set.in y ($Set.add xs x)))
	:pattern (($Set.in y xs) ($Set.in y ($Set.add xs x)))
	)))
(assert (forall ((xs $Set<$Ref>) (x $Ref)) (!
	(implies
		($Set.in x xs)
		(= ($Set.card ($Set.add xs x)) ($Set.card xs)))
	:pattern (($Set.card ($Set.add xs x)))
	)))
(assert (forall ((xs $Set<$Ref>) (x $Ref)) (!
	(implies
		(not ($Set.in x xs))
		(= ($Set.card ($Set.add xs x)) (+ ($Set.card xs) 1)))
	:pattern (($Set.card ($Set.add xs x)))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>) (x $Ref)) (!
	(iff
		($Set.in x ($Set.union xs ys))
		(or
			($Set.in x xs)
			($Set.in x ys)))
	:pattern (($Set.in x ($Set.union xs ys)))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>) (x $Ref)) (!
	(implies
		($Set.in x xs)
		($Set.in x ($Set.union xs ys)))
	:pattern (($Set.in x ($Set.union xs ys)) ($Set.in x xs))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>) (x $Ref)) (!
	(implies
		($Set.in x ys)
		($Set.in x ($Set.union xs ys)))
	:pattern (($Set.in x ($Set.union xs ys)) ($Set.in x ys))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>)) (!
	(implies
		($Set.disjoint xs ys)
		(and
			(= ($Set.difference ($Set.union xs ys) xs) ys)
			(= ($Set.difference ($Set.union xs ys) ys) xs)))
	:pattern (($Set.union xs ys))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>) (x $Ref)) (!
	(iff
		($Set.in x ($Set.intersection xs ys))
		(and
			($Set.in x xs)
			($Set.in x ys)))
	:pattern (($Set.in x ($Set.intersection xs ys)))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>)) (!
	(=
		($Set.union ($Set.union xs ys) ys)
		($Set.union xs ys))
	:pattern (($Set.union ($Set.union xs ys) ys))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>)) (!
	(=
		($Set.union xs ($Set.union xs ys))
		($Set.union xs ys))
	:pattern (($Set.union xs ($Set.union xs ys)))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>)) (!
	(=
		($Set.intersection ($Set.intersection xs ys) ys)
		($Set.intersection xs ys))
	:pattern (($Set.intersection ($Set.intersection xs ys) ys))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>)) (!
	(=
		($Set.intersection xs ($Set.intersection xs ys))
		($Set.intersection xs ys))
	:pattern (($Set.intersection xs ($Set.intersection xs ys)))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>)) (!
	(=
		(+
			($Set.card ($Set.union xs ys))
			($Set.card ($Set.intersection xs ys)))
		(+
			($Set.card xs)
			($Set.card ys)))
	:pattern (($Set.card ($Set.union xs ys)))
	:pattern (($Set.card ($Set.intersection xs ys)))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>) (x $Ref)) (!
	(iff
		($Set.in x ($Set.difference xs ys))
		(and
			($Set.in x xs)
			(not ($Set.in x ys))))
	:pattern (($Set.in x ($Set.difference xs ys)))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>) (x $Ref)) (!
	(implies
		($Set.in x ys)
		(not ($Set.in x ($Set.difference xs ys))))
	:pattern (($Set.in x ($Set.difference xs ys)) ($Set.in x ys))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>)) (!
	(iff
		($Set.subset xs ys)
		(forall ((x $Ref)) (!
			(implies
				($Set.in x xs)
				($Set.in x ys))
			:pattern (($Set.in x xs))
			:pattern (($Set.in x ys))
			)))
	:pattern (($Set.subset xs ys))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>)) (!
	(iff
		($Set.eq xs ys)
		(forall ((x $Ref)) (!
			(iff
				($Set.in x xs)
				($Set.in x ys))
			:pattern (($Set.in x xs))
			:pattern (($Set.in x ys))
			)))
	:pattern (($Set.eq xs ys))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>)) (!
	(implies
		($Set.eq xs ys)
		(= xs ys))
	:pattern (($Set.eq xs ys))
	)))
(assert (forall ((xs $Set<$Ref>) (ys $Set<$Ref>)) (!
	(iff
		($Set.disjoint xs ys)
		(forall ((x $Ref)) (!
			(or
				(not ($Set.in x xs))
				(not ($Set.in x ys)))
			:pattern (($Set.in x xs))
			:pattern (($Set.in x ys))
			)))
	:pattern (($Set.disjoint xs ys))
	)))
(assert (forall ((x $Ref)) (! (= (NN<Ref~Bool> x) (not (= x $Ref.null))) :pattern ((NN<Ref~Bool> x)))))
; /field_value_functions_axioms.smt2 [f]
(assert (forall ((vs $FVF<Int>) (ws $FVF<Int>)) (!
    (implies
      (and
        ($Set.eq ($FVF.domain_f vs) ($FVF.domain_f ws))
        (forall ((x $Ref)) (!
          (implies
            ($Set.in x ($FVF.domain_f vs))
            (= ($FVF.lookup_f vs x) ($FVF.lookup_f ws x)))
          :pattern (($FVF.lookup_f vs x) ($FVF.lookup_f ws x)))))
      (= vs ws))
    :pattern (($FVF.domain_f vs) ($FVF.domain_f ws)))))
(assert (forall ((vs $FVF<Int>) (x $Ref)) (!
    (= ($FVF.lookup_f_inv ($FVF.lookup_f vs x)) x)
    :pattern (($FVF.lookup_f_inv ($FVF.lookup_f vs x)))
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$PermTo$Snap ($Perm) $Snap)
(declare-fun $SortWrappers.$SnapTo$Perm ($Snap) $Perm)
(assert (forall ((x $Perm)) (!
    (= x ($SortWrappers.$SnapTo$Perm($SortWrappers.$PermTo$Snap x)))
    :pattern (($SortWrappers.$PermTo$Snap x))
    )))
(declare-fun $SortWrappers.$RefTo$Snap ($Ref) $Snap)
(declare-fun $SortWrappers.$SnapTo$Ref ($Snap) $Ref)
(assert (forall ((x $Ref)) (!
    (= x ($SortWrappers.$SnapTo$Ref($SortWrappers.$RefTo$Snap x)))
    :pattern (($SortWrappers.$RefTo$Snap x))
    )))
(declare-fun $SortWrappers.BoolTo$Snap (Bool) $Snap)
(declare-fun $SortWrappers.$SnapToBool ($Snap) Bool)
(assert (forall ((x Bool)) (!
    (= x ($SortWrappers.$SnapToBool($SortWrappers.BoolTo$Snap x)))
    :pattern (($SortWrappers.BoolTo$Snap x))
    )))
(declare-fun $SortWrappers.IntTo$Snap (Int) $Snap)
(declare-fun $SortWrappers.$SnapToInt ($Snap) Int)
(assert (forall ((x Int)) (!
    (= x ($SortWrappers.$SnapToInt($SortWrappers.IntTo$Snap x)))
    :pattern (($SortWrappers.IntTo$Snap x))
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$Set<$Ref>To$Snap ($Set<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Set<$Ref> ($Snap) $Set<$Ref>)
(assert (forall ((x $Set<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$Set<$Ref>($SortWrappers.$Set<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$Set<$Ref>To$Snap x))
    )))
(declare-fun $SortWrappers.$Set<Int>To$Snap ($Set<Int>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Set<Int> ($Snap) $Set<Int>)
(assert (forall ((x $Set<Int>)) (!
    (= x ($SortWrappers.$SnapTo$Set<Int>($SortWrappers.$Set<Int>To$Snap x)))
    :pattern (($SortWrappers.$Set<Int>To$Snap x))
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.NonNullTo$Snap (NonNull) $Snap)
(declare-fun $SortWrappers.$SnapToNonNull ($Snap) NonNull)
(assert (forall ((x NonNull)) (!
    (= x ($SortWrappers.$SnapToNonNull($SortWrappers.NonNullTo$Snap x)))
    :pattern (($SortWrappers.NonNullTo$Snap x))
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$FVF<Int>To$Snap ($FVF<Int>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<Int> ($Snap) $FVF<Int>)
(assert (forall ((x $FVF<Int>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<Int>($SortWrappers.$FVF<Int>To$Snap x)))
    :pattern (($SortWrappers.$FVF<Int>To$Snap x))
    )))
; Preamble end
; ------------------------------------------------------------
; ------------------------------------------------------------
; Declaring program functions
; ---------- test ----------
(declare-const y@1 $Ref)
(declare-const z@2 $Ref)

; [exec]
; inhale (forall x: Ref :: true ==> acc(x.f, write))
(declare-const x@3 $Ref)
(declare-const $t@4 $FVF<Int>)
(assert (forall ((x@3 $Ref)) (! (not (= x@3 $Ref.null)) )))
(assert (forall ((x@3 $Ref)) (! ($Set.in x@3 ($FVF.domain_f $t@4)) :pattern (($FVF.lookup_f $t@4 x@3)))))

; [exec]
; inhale (forall x: Ref :: true ==> NN(x) && (x.f == 0))
; [eval] (forall x: Ref :: true ==> NN(x) && (x.f == 0))
(declare-const x@5 $Ref)
(declare-const fvf@6 $FVF<Int>)

(assert (forall ((x@5 $Ref)) (!
  (and
    (forall ((x@5 $Ref)) (!
      (= ($FVF.lookup_f fvf@6 x@5) ($FVF.lookup_f $t@4 x@5))
      :pattern (($FVF.lookup_f fvf@6 x@5))
      :pattern (($FVF.lookup_f $t@4 x@5))
    ))
    ($Set.eq ($FVF.domain_f fvf@6) ($FVF.domain_f $t@4)))
  :pattern ((NN<Ref~Bool> x@5))
  :pattern (($FVF.lookup_f fvf@6 x@5)) ; ADDED this trigger
  :pattern (($FVF.lookup_f $t@4 x@5)) ; ADDED this trigger
)))

(assert (forall ((x@5 $Ref)) (!
  (and
    (NN<Ref~Bool> x@5)
    (= ($FVF.lookup_f fvf@6 x@5) 0))
  :pattern ((NN<Ref~Bool> x@5))
  :pattern (($FVF.lookup_f fvf@6 x@5)) ; ADDED this trigger
)))

; [exec]
; z := new()
(declare-const z@7 $Ref)
(assert (not (= z@7 $Ref.null)))
(assert (not (= y@1 z@7)))

; [exec]
; assert z.f == 0
; [eval] z.f == 0
(declare-const fvf@8 $FVF<Int>)
(assert (= ($FVF.lookup_f fvf@8 z@7) ($FVF.lookup_f $t@4 z@7)))
(assert ($Set.eq ($FVF.domain_f fvf@8) ($FVF.domain_f $t@4)))

(push) ; 4
(assert (not (= ($FVF.lookup_f fvf@8 z@7) 0)))
(check-sat)
; unknown
(pop) ; 4
