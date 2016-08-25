(get-info :version)
; (:version "4.3")
; Started: 2014-09-24 08:00:21
; Silicon.buildVersion: 0.1-SNAPSHOT 9e4f6e0522be default 2014/09/24 07:53:26
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
(declare-sort $Seq<$Ref>)
(declare-sort $Seq<Int>)
(declare-sort $Set<$Ref>)
(declare-sort $Set<Int>)
(declare-sort $Multiset<$Ref>)
(declare-sort $Multiset<Int>)
(declare-sort $FVF<$Ref>)
(declare-sort $FVF<Int>)
; /dafny_axioms/sets_declarations_dafny.smt2 [Ref]
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
; /dafny_axioms/sets_declarations_dafny.smt2 [Int]
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
; /dafny_axioms/multisets_declarations_dafny.smt2 [Ref]
(declare-fun $Multiset.count ($Multiset<$Ref> $Ref) Int)
(declare-fun $Multiset.card ($Multiset<$Ref>) Int)
(declare-fun $Multiset.empty<$Ref> () $Multiset<$Ref>)
(declare-fun $Multiset.singleton ($Ref) $Multiset<$Ref>)
(declare-fun $Multiset.add ($Multiset<$Ref> $Ref) $Multiset<$Ref>)
(declare-fun $Multiset.union ($Multiset<$Ref> $Multiset<$Ref>) $Multiset<$Ref>)
(declare-fun $Multiset.intersection ($Multiset<$Ref> $Multiset<$Ref>) $Multiset<$Ref>)
(declare-fun $Multiset.difference ($Multiset<$Ref> $Multiset<$Ref>) $Multiset<$Ref>)
(declare-fun $Multiset.subset ($Multiset<$Ref> $Multiset<$Ref>) Bool)
(declare-fun $Multiset.eq ($Multiset<$Ref> $Multiset<$Ref>) Bool)
(declare-fun $Multiset.disjoint ($Multiset<$Ref> $Multiset<$Ref>) Bool)
; /dafny_axioms/multisets_declarations_dafny.smt2 [Int]
(declare-fun $Multiset.count ($Multiset<Int> Int) Int)
(declare-fun $Multiset.card ($Multiset<Int>) Int)
(declare-fun $Multiset.empty<Int> () $Multiset<Int>)
(declare-fun $Multiset.singleton (Int) $Multiset<Int>)
(declare-fun $Multiset.add ($Multiset<Int> Int) $Multiset<Int>)
(declare-fun $Multiset.union ($Multiset<Int> $Multiset<Int>) $Multiset<Int>)
(declare-fun $Multiset.intersection ($Multiset<Int> $Multiset<Int>) $Multiset<Int>)
(declare-fun $Multiset.difference ($Multiset<Int> $Multiset<Int>) $Multiset<Int>)
(declare-fun $Multiset.subset ($Multiset<Int> $Multiset<Int>) Bool)
(declare-fun $Multiset.eq ($Multiset<Int> $Multiset<Int>) Bool)
(declare-fun $Multiset.disjoint ($Multiset<Int> $Multiset<Int>) Bool)
; /dafny_axioms/sequences_declarations_dafny.smt2 [Ref]
(declare-fun $Seq.nil<$Ref> () $Seq<$Ref>)
(declare-fun $Seq.len ($Seq<$Ref>) Int)
(declare-fun $Seq.elem ($Ref) $Seq<$Ref>)
(declare-fun $Seq.build ($Seq<$Ref> Int $Ref Int) $Seq<$Ref>)
(declare-fun $Seq.con ($Seq<$Ref> $Seq<$Ref>) $Seq<$Ref>)
(declare-fun $Seq.at ($Seq<$Ref> Int) $Ref)
(declare-fun $Seq.in ($Seq<$Ref> $Ref) Bool)
(declare-fun $Seq.eq ($Seq<$Ref> $Seq<$Ref>) Bool)
(declare-fun $Seq.sameUntil ($Seq<$Ref> $Seq<$Ref> Int) Bool)
(declare-fun $Seq.take ($Seq<$Ref> Int) $Seq<$Ref>)
(declare-fun $Seq.drop ($Seq<$Ref> Int) $Seq<$Ref>)
(declare-fun $Seq.update ($Seq<$Ref> Int $Ref) $Seq<$Ref>)
; /dafny_axioms/sequences_declarations_dafny.smt2 [Int]
(declare-fun $Seq.nil<Int> () $Seq<Int>)
(declare-fun $Seq.len ($Seq<Int>) Int)
(declare-fun $Seq.elem (Int) $Seq<Int>)
(declare-fun $Seq.build ($Seq<Int> Int Int Int) $Seq<Int>)
(declare-fun $Seq.con ($Seq<Int> $Seq<Int>) $Seq<Int>)
(declare-fun $Seq.at ($Seq<Int> Int) Int)
(declare-fun $Seq.in ($Seq<Int> Int) Bool)
(declare-fun $Seq.eq ($Seq<Int> $Seq<Int>) Bool)
(declare-fun $Seq.sameUntil ($Seq<Int> $Seq<Int> Int) Bool)
(declare-fun $Seq.take ($Seq<Int> Int) $Seq<Int>)
(declare-fun $Seq.drop ($Seq<Int> Int) $Seq<Int>)
(declare-fun $Seq.update ($Seq<Int> Int Int) $Seq<Int>)
; /dafny_axioms/sequences_int_declarations_dafny.smt2
(declare-fun $Seq.rng (Int Int) $Seq<Int>)
(assert true)
; /field_value_functions_declarations.smt2 [f: Int]
(declare-fun $FVF.domain_f ($FVF<Int>) $Set<$Ref>)
(declare-fun $FVF.lookup_f ($FVF<Int> $Ref) Int)
; /dafny_axioms/sequences_axioms_dafny.smt2 [Ref]
(assert (forall ((xs $Seq<$Ref>)) (!
	(<= 0 ($Seq.len xs))
	:pattern (($Seq.len xs))
	)))
(assert (= ($Seq.len $Seq.nil<$Ref>) 0))
(assert (forall ((xs $Seq<$Ref>)) (!
	(implies
		(= ($Seq.len xs) 0)
		(= xs $Seq.nil<$Ref>))
	:pattern (($Seq.len xs))
	)))
(assert (forall ((x $Ref)) (!
	(= ($Seq.len ($Seq.elem x)) 1)
	:pattern (($Seq.len ($Seq.elem x)))
	)))
(assert (forall ((xs $Seq<$Ref>) (i Int) (x $Ref) (n Int)) (!
	(implies
		(<= 0 n)
		(= ($Seq.len ($Seq.build xs i x n)) n))
	:pattern (($Seq.len ($Seq.build xs i x n)))
	)))
(assert (forall ((xs $Seq<$Ref>) (ys $Seq<$Ref>)) (!
	(=
		($Seq.len ($Seq.con xs ys))
		(+ ($Seq.len xs) ($Seq.len ys)))
	:pattern (($Seq.len ($Seq.con xs ys)))
	)))
(assert (forall ((x $Ref)) (!
	(= ($Seq.at ($Seq.elem x) 0) x)
	:pattern (($Seq.at ($Seq.elem x) 0))
	)))
(assert (forall ((xs $Seq<$Ref>) (ys $Seq<$Ref>) (i Int)) (!
	(and
		(implies
			(< i ($Seq.len xs))
			(=
				($Seq.at ($Seq.con xs ys) i)
				($Seq.at xs i)))
		(implies
			(<= ($Seq.len xs) i)
			(=
				($Seq.at ($Seq.con xs ys) i)
				($Seq.at ys (- i ($Seq.len xs))))))
	:pattern (($Seq.at ($Seq.con xs ys) i))
	)))
(assert (forall ((xs $Seq<$Ref>) (i Int) (x $Ref) (n Int) (j Int)) (!
	(implies
		(and
			(<= 0 j)
			(< j n))
		(and
			(implies
				(= i j)
				(= ($Seq.at ($Seq.build xs i x n) j) x))
			(implies
				(not (= i j))
				(= ($Seq.at ($Seq.build xs i x n) j) ($Seq.at xs j)))))
	:pattern (($Seq.at ($Seq.build xs i x n) j))
	)))
(assert (forall ((x $Ref)) (!
	($Seq.in ($Seq.elem x) x)
	:pattern (($Seq.in ($Seq.elem x) x))
	)))
(assert (forall ((xs $Seq<$Ref>) (x $Ref)) (!
	(iff
		($Seq.in xs x)
		(exists ((i Int)) (!
			(and
				(<= 0 i)
				(< i ($Seq.len xs))
				(= ($Seq.at xs i) x))
			:pattern (($Seq.at xs i))
			)))
	:pattern (($Seq.in xs x))
	)))
(assert (forall ((x $Ref)) (!
	(not ($Seq.in $Seq.nil<$Ref> x))
	:pattern (($Seq.in $Seq.nil<$Ref> x))
	)))
(assert (forall ((xs $Seq<$Ref>) (ys $Seq<$Ref>) (x $Ref)) (!
	(iff
		($Seq.in ($Seq.con xs ys) x)
		(or
			($Seq.in xs x)
			($Seq.in ys x)))
	:pattern (($Seq.in ($Seq.con xs ys) x))
	)))
(assert (forall ((xs $Seq<$Ref>) (i Int) (x $Ref) (n Int) (y $Ref)) (!
	(iff
		($Seq.in ($Seq.build xs i x n) y)
		(or
			(and
				(<= 0 i)
				(< i n)
				(= y x))
			(exists ((j Int)) (!
				(and
					(<= 0 j)
					(< j ($Seq.len xs))
					(< j n)
					(not (= j i))
					(= ($Seq.at xs j) y))
				:pattern (($Seq.at xs j))
				))))
	:pattern (($Seq.in ($Seq.build xs i x n) y))
	)))
(assert (forall ((xs $Seq<$Ref>) (k Int) (x $Ref)) (!
	(iff
		($Seq.in ($Seq.take xs k) x)
		(exists ((i Int)) (!
			(and
				(<= 0 i)
				(< i k)
				(< i ($Seq.len xs))
				(= ($Seq.at xs i) x))
			:pattern (($Seq.at xs i))
			)))
	:pattern (($Seq.in ($Seq.take xs k) x))
	)))
(assert (forall ((xs $Seq<$Ref>) (k Int) (x $Ref)) (!
	(iff
		($Seq.in ($Seq.drop xs k) x)
		(exists ((i Int)) (!
			(and
				(<= 0 k)
				(<= k i)
				(< i ($Seq.len xs))
				(= ($Seq.at xs i) x))
			:pattern (($Seq.at xs i))
			)))
	:pattern (($Seq.in ($Seq.drop xs k) x))
	)))
(assert (forall ((xs $Seq<$Ref>) (ys $Seq<$Ref>)) (!
	(iff
		($Seq.eq xs ys)
		(and
			(= ($Seq.len xs) ($Seq.len ys))
			(forall ((i Int)) (!
				(implies
					(and
						(<= 0 i)
						(< i ($Seq.len xs)))
					(= ($Seq.at xs i) ($Seq.at ys i)))
				:pattern (($Seq.at xs i) ($Seq.at ys i))
				))))
	:pattern (($Seq.eq xs ys))
	)))
(assert (forall ((xs $Seq<$Ref>) (ys $Seq<$Ref>)) (!
	(implies
		($Seq.eq xs ys)
		(= xs ys))
	:pattern (($Seq.eq xs ys))
	)))
(assert (forall ((x $Ref) (y $Ref)) (!
	(iff
		($Seq.in ($Seq.elem x) y)
		(= x y))
	:pattern (($Seq.in ($Seq.elem x) y)))))
(assert (forall ((xs $Seq<$Ref>) (ys $Seq<$Ref>) (i Int)) (!
	(iff
		($Seq.sameUntil xs ys i)
		(forall ((j Int)) (!
			(implies
				(and
					(<= 0 j)
					(< j i))
				(= ($Seq.at xs j) ($Seq.at ys j)))
			:pattern (($Seq.at xs j) ($Seq.at ys j))
			)))
	:pattern (($Seq.sameUntil xs ys i))
	)))
(assert (forall ((xs $Seq<$Ref>) (k Int)) (!
	(implies
		(<= 0 k)
		(and
			(implies
				(<= k ($Seq.len xs))
				(= ($Seq.len ($Seq.take xs k)) k))
			(implies
				(< ($Seq.len xs) k)
				(= ($Seq.len ($Seq.take xs k)) ($Seq.len xs)))))
	:pattern (($Seq.len ($Seq.take xs k)))
	)))
(assert (forall ((xs $Seq<$Ref>) (k Int) (i Int)) (!
	(implies
		(and
			(<= 0 i)
			(< i k)
			(< i ($Seq.len xs)))
		(= ($Seq.at ($Seq.take xs k) i) ($Seq.at xs i)))
	:weight 25
	:pattern (($Seq.at ($Seq.take xs k) i))
	)))
(assert (forall ((xs $Seq<$Ref>) (k Int)) (!
	(implies
		(<= 0 k)
		(and
			(implies
				(<= k ($Seq.len xs))
				(= ($Seq.len ($Seq.drop xs k)) (- ($Seq.len xs) k)))
			(implies
				(< ($Seq.len xs) k)
				(= ($Seq.len ($Seq.drop xs k)) 0))))
	:pattern (($Seq.len ($Seq.drop xs k)))
	)))
(assert (forall ((xs $Seq<$Ref>) (k Int) (i Int)) (!
	(implies
		(and
			(<= 0 k)
			(<= 0 i)
			(< i (- ($Seq.len xs) k)))
		(= ($Seq.at ($Seq.drop xs k) i) ($Seq.at xs (+ i k))))
	:weight 25
	:pattern (($Seq.at ($Seq.drop xs k) i))
	)))
(assert (forall ((xs $Seq<$Ref>) (ys $Seq<$Ref>)) (!
	(and
		(= ($Seq.take ($Seq.con xs ys) ($Seq.len xs)) xs)
		(= ($Seq.drop ($Seq.con xs ys) ($Seq.len xs)) ys))
	:pattern (($Seq.con xs ys))
	)))
(assert (forall ((xs $Seq<$Ref>) (i Int) (x $Ref)) (!
  (implies
    (and
      (<= 0 i)
      (< i ($Seq.len xs)))
    (=
      ($Seq.len ($Seq.update xs i x))
      ($Seq.len xs)))
  :pattern (($Seq.len ($Seq.update xs i x)))
  )))
(assert (forall ((xs $Seq<$Ref>) (i Int) (x $Ref) (j Int)) (!
  (implies
    (and
      (<= 0 j)
      (< j ($Seq.len xs)))
    (and
      (implies
        (= i j)
        (= ($Seq.at ($Seq.update xs i x) j) x))
      (implies
        (not (= i j))
        (= ($Seq.at ($Seq.update xs i x) j) ($Seq.at xs j)))))
  :pattern (($Seq.at ($Seq.update xs i x) j))
  )))
(assert (forall ((xs $Seq<$Ref>) (i Int) (x $Ref) (j Int)) (!
  (implies
    (and
      (<= 0 i)
      (< i j)
      (<= j ($Seq.len xs)))
    (=
      ($Seq.take ($Seq.update xs i x) j)
      ($Seq.update ($Seq.take xs j) i x)))
  :pattern (($Seq.take ($Seq.update xs i x) j))
  )))
(assert (forall ((xs $Seq<$Ref>) (i Int) (x $Ref) (j Int)) (!
  (implies
    (and
      (<= j i)
      (< i ($Seq.len xs)))
    (=
      ($Seq.take ($Seq.update xs i x) j)
      ($Seq.take xs j)))
  :pattern (($Seq.take ($Seq.update xs i x) j))
  )))
(assert (forall ((xs $Seq<$Ref>) (i Int) (x $Ref) (j Int)) (!
  (implies
    (and
      (<= 0 j)
      (<= j i)
      (< i ($Seq.len xs)))
    (=
      ($Seq.drop ($Seq.update xs i x) j)
      ($Seq.update ($Seq.drop xs j) (- i j) x)))
  :pattern (($Seq.drop ($Seq.update xs i x) j))
  )))
(assert (forall ((xs $Seq<$Ref>) (i Int) (x $Ref) (j Int)) (!
  (implies
    (and
      (<= 0 i)
      (<= i j)
      (< j ($Seq.len xs)))
    (=
      ($Seq.drop ($Seq.update xs i x) j)
      ($Seq.drop xs j)))
  :pattern (($Seq.drop ($Seq.update xs i x) j))
  )))
; /dafny_axioms/sequences_axioms_dafny.smt2 [Int]
(assert (forall ((xs $Seq<Int>)) (!
	(<= 0 ($Seq.len xs))
	:pattern (($Seq.len xs))
	)))
(assert (= ($Seq.len $Seq.nil<Int>) 0))
(assert (forall ((xs $Seq<Int>)) (!
	(implies
		(= ($Seq.len xs) 0)
		(= xs $Seq.nil<Int>))
	:pattern (($Seq.len xs))
	)))
(assert (forall ((x Int)) (!
	(= ($Seq.len ($Seq.elem x)) 1)
	:pattern (($Seq.len ($Seq.elem x)))
	)))
(assert (forall ((xs $Seq<Int>) (i Int) (x Int) (n Int)) (!
	(implies
		(<= 0 n)
		(= ($Seq.len ($Seq.build xs i x n)) n))
	:pattern (($Seq.len ($Seq.build xs i x n)))
	)))
(assert (forall ((xs $Seq<Int>) (ys $Seq<Int>)) (!
	(=
		($Seq.len ($Seq.con xs ys))
		(+ ($Seq.len xs) ($Seq.len ys)))
	:pattern (($Seq.len ($Seq.con xs ys)))
	)))
(assert (forall ((x Int)) (!
	(= ($Seq.at ($Seq.elem x) 0) x)
	:pattern (($Seq.at ($Seq.elem x) 0))
	)))
(assert (forall ((xs $Seq<Int>) (ys $Seq<Int>) (i Int)) (!
	(and
		(implies
			(< i ($Seq.len xs))
			(=
				($Seq.at ($Seq.con xs ys) i)
				($Seq.at xs i)))
		(implies
			(<= ($Seq.len xs) i)
			(=
				($Seq.at ($Seq.con xs ys) i)
				($Seq.at ys (- i ($Seq.len xs))))))
	:pattern (($Seq.at ($Seq.con xs ys) i))
	)))
(assert (forall ((xs $Seq<Int>) (i Int) (x Int) (n Int) (j Int)) (!
	(implies
		(and
			(<= 0 j)
			(< j n))
		(and
			(implies
				(= i j)
				(= ($Seq.at ($Seq.build xs i x n) j) x))
			(implies
				(not (= i j))
				(= ($Seq.at ($Seq.build xs i x n) j) ($Seq.at xs j)))))
	:pattern (($Seq.at ($Seq.build xs i x n) j))
	)))
(assert (forall ((x Int)) (!
	($Seq.in ($Seq.elem x) x)
	:pattern (($Seq.in ($Seq.elem x) x))
	)))
(assert (forall ((xs $Seq<Int>) (x Int)) (!
	(iff
		($Seq.in xs x)
		(exists ((i Int)) (!
			(and
				(<= 0 i)
				(< i ($Seq.len xs))
				(= ($Seq.at xs i) x))
			:pattern (($Seq.at xs i))
			)))
	:pattern (($Seq.in xs x))
	)))
(assert (forall ((x Int)) (!
	(not ($Seq.in $Seq.nil<Int> x))
	:pattern (($Seq.in $Seq.nil<Int> x))
	)))
(assert (forall ((xs $Seq<Int>) (ys $Seq<Int>) (x Int)) (!
	(iff
		($Seq.in ($Seq.con xs ys) x)
		(or
			($Seq.in xs x)
			($Seq.in ys x)))
	:pattern (($Seq.in ($Seq.con xs ys) x))
	)))
(assert (forall ((xs $Seq<Int>) (i Int) (x Int) (n Int) (y Int)) (!
	(iff
		($Seq.in ($Seq.build xs i x n) y)
		(or
			(and
				(<= 0 i)
				(< i n)
				(= y x))
			(exists ((j Int)) (!
				(and
					(<= 0 j)
					(< j ($Seq.len xs))
					(< j n)
					(not (= j i))
					(= ($Seq.at xs j) y))
				:pattern (($Seq.at xs j))
				))))
	:pattern (($Seq.in ($Seq.build xs i x n) y))
	)))
(assert (forall ((xs $Seq<Int>) (k Int) (x Int)) (!
	(iff
		($Seq.in ($Seq.take xs k) x)
		(exists ((i Int)) (!
			(and
				(<= 0 i)
				(< i k)
				(< i ($Seq.len xs))
				(= ($Seq.at xs i) x))
			:pattern (($Seq.at xs i))
			)))
	:pattern (($Seq.in ($Seq.take xs k) x))
	)))
(assert (forall ((xs $Seq<Int>) (k Int) (x Int)) (!
	(iff
		($Seq.in ($Seq.drop xs k) x)
		(exists ((i Int)) (!
			(and
				(<= 0 k)
				(<= k i)
				(< i ($Seq.len xs))
				(= ($Seq.at xs i) x))
			:pattern (($Seq.at xs i))
			)))
	:pattern (($Seq.in ($Seq.drop xs k) x))
	)))
(assert (forall ((xs $Seq<Int>) (ys $Seq<Int>)) (!
	(iff
		($Seq.eq xs ys)
		(and
			(= ($Seq.len xs) ($Seq.len ys))
			(forall ((i Int)) (!
				(implies
					(and
						(<= 0 i)
						(< i ($Seq.len xs)))
					(= ($Seq.at xs i) ($Seq.at ys i)))
				:pattern (($Seq.at xs i) ($Seq.at ys i))
				))))
	:pattern (($Seq.eq xs ys))
	)))
(assert (forall ((xs $Seq<Int>) (ys $Seq<Int>)) (!
	(implies
		($Seq.eq xs ys)
		(= xs ys))
	:pattern (($Seq.eq xs ys))
	)))
(assert (forall ((x Int) (y Int)) (!
	(iff
		($Seq.in ($Seq.elem x) y)
		(= x y))
	:pattern (($Seq.in ($Seq.elem x) y)))))
(assert (forall ((xs $Seq<Int>) (ys $Seq<Int>) (i Int)) (!
	(iff
		($Seq.sameUntil xs ys i)
		(forall ((j Int)) (!
			(implies
				(and
					(<= 0 j)
					(< j i))
				(= ($Seq.at xs j) ($Seq.at ys j)))
			:pattern (($Seq.at xs j) ($Seq.at ys j))
			)))
	:pattern (($Seq.sameUntil xs ys i))
	)))
(assert (forall ((xs $Seq<Int>) (k Int)) (!
	(implies
		(<= 0 k)
		(and
			(implies
				(<= k ($Seq.len xs))
				(= ($Seq.len ($Seq.take xs k)) k))
			(implies
				(< ($Seq.len xs) k)
				(= ($Seq.len ($Seq.take xs k)) ($Seq.len xs)))))
	:pattern (($Seq.len ($Seq.take xs k)))
	)))
(assert (forall ((xs $Seq<Int>) (k Int) (i Int)) (!
	(implies
		(and
			(<= 0 i)
			(< i k)
			(< i ($Seq.len xs)))
		(= ($Seq.at ($Seq.take xs k) i) ($Seq.at xs i)))
	:weight 25
	:pattern (($Seq.at ($Seq.take xs k) i))
	)))
(assert (forall ((xs $Seq<Int>) (k Int)) (!
	(implies
		(<= 0 k)
		(and
			(implies
				(<= k ($Seq.len xs))
				(= ($Seq.len ($Seq.drop xs k)) (- ($Seq.len xs) k)))
			(implies
				(< ($Seq.len xs) k)
				(= ($Seq.len ($Seq.drop xs k)) 0))))
	:pattern (($Seq.len ($Seq.drop xs k)))
	)))
(assert (forall ((xs $Seq<Int>) (k Int) (i Int)) (!
	(implies
		(and
			(<= 0 k)
			(<= 0 i)
			(< i (- ($Seq.len xs) k)))
		(= ($Seq.at ($Seq.drop xs k) i) ($Seq.at xs (+ i k))))
	:weight 25
	:pattern (($Seq.at ($Seq.drop xs k) i))
	)))
(assert (forall ((xs $Seq<Int>) (ys $Seq<Int>)) (!
	(and
		(= ($Seq.take ($Seq.con xs ys) ($Seq.len xs)) xs)
		(= ($Seq.drop ($Seq.con xs ys) ($Seq.len xs)) ys))
	:pattern (($Seq.con xs ys))
	)))
(assert (forall ((xs $Seq<Int>) (i Int) (x Int)) (!
  (implies
    (and
      (<= 0 i)
      (< i ($Seq.len xs)))
    (=
      ($Seq.len ($Seq.update xs i x))
      ($Seq.len xs)))
  :pattern (($Seq.len ($Seq.update xs i x)))
  )))
(assert (forall ((xs $Seq<Int>) (i Int) (x Int) (j Int)) (!
  (implies
    (and
      (<= 0 j)
      (< j ($Seq.len xs)))
    (and
      (implies
        (= i j)
        (= ($Seq.at ($Seq.update xs i x) j) x))
      (implies
        (not (= i j))
        (= ($Seq.at ($Seq.update xs i x) j) ($Seq.at xs j)))))
  :pattern (($Seq.at ($Seq.update xs i x) j))
  )))
(assert (forall ((xs $Seq<Int>) (i Int) (x Int) (j Int)) (!
  (implies
    (and
      (<= 0 i)
      (< i j)
      (<= j ($Seq.len xs)))
    (=
      ($Seq.take ($Seq.update xs i x) j)
      ($Seq.update ($Seq.take xs j) i x)))
  :pattern (($Seq.take ($Seq.update xs i x) j))
  )))
(assert (forall ((xs $Seq<Int>) (i Int) (x Int) (j Int)) (!
  (implies
    (and
      (<= j i)
      (< i ($Seq.len xs)))
    (=
      ($Seq.take ($Seq.update xs i x) j)
      ($Seq.take xs j)))
  :pattern (($Seq.take ($Seq.update xs i x) j))
  )))
(assert (forall ((xs $Seq<Int>) (i Int) (x Int) (j Int)) (!
  (implies
    (and
      (<= 0 j)
      (<= j i)
      (< i ($Seq.len xs)))
    (=
      ($Seq.drop ($Seq.update xs i x) j)
      ($Seq.update ($Seq.drop xs j) (- i j) x)))
  :pattern (($Seq.drop ($Seq.update xs i x) j))
  )))
(assert (forall ((xs $Seq<Int>) (i Int) (x Int) (j Int)) (!
  (implies
    (and
      (<= 0 i)
      (<= i j)
      (< j ($Seq.len xs)))
    (=
      ($Seq.drop ($Seq.update xs i x) j)
      ($Seq.drop xs j)))
  :pattern (($Seq.drop ($Seq.update xs i x) j))
  )))
; /dafny_axioms/sequences_int_axioms_dafny.smt2
(assert (forall ((i Int) (j Int)) (!
	(and
		(implies
			(< i j)
			(= ($Seq.len ($Seq.rng i j)) (- j i)))
		(implies
			(<= j i)
			(= ($Seq.len ($Seq.rng i j)) 0)))
	:pattern (($Seq.len ($Seq.rng i j)))
	)))
(assert (forall ((i Int) (j Int) (k Int)) (!
	(implies
		(and
			(<= 0 k)
			(< k (- j i)))
		(= ($Seq.at ($Seq.rng i j) k) (+ i k)))
	:pattern (($Seq.at ($Seq.rng i j) k))
	)))
(assert (forall ((i Int) (j Int) (k Int)) (!
    (iff
      ($Seq.in ($Seq.rng i j) k)
		  (and
			  (<= i k)
			  (< k j)))
	  :pattern (($Seq.in ($Seq.rng i j) k)))))
; /dafny_axioms/sets_axioms_dafny.smt2 [Ref]
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
; /dafny_axioms/sets_axioms_dafny.smt2 [Int]
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
; /dafny_axioms/multisets_axioms_dafny.smt2 [Ref]
(assert (forall ((xs $Multiset<$Ref>)) (!
  (< 0 ($Multiset.card xs))
	:pattern (($Multiset.card xs))
	)))
(assert (forall ((x $Ref)) (!
  (= ($Multiset.count $Multiset.empty<$Ref> x) 0)
	:pattern (($Multiset.count $Multiset.empty<$Ref> x))
	)))
(assert (forall ((xs $Multiset<$Ref>)) (!
  (and
    (iff
      (= ($Multiset.card xs) 0)
      (= xs $Multiset.empty<$Ref>))
    (implies
      (not (= ($Multiset.card xs) 0))
      (exists ((x $Ref)) (!
        (< 0 ($Multiset.count xs x))
        :pattern (($Multiset.count xs x))
        ))))
	:pattern (($Multiset.card xs))
	)))
(assert (forall ((x $Ref) (y $Ref)) (!
  (and
    (iff
      (= 1 ($Multiset.count ($Multiset.singleton x) y))
      (= x y))
    (iff
      (= 0 ($Multiset.count ($Multiset.singleton x) y))
      (not (= x y))))
	:pattern (($Multiset.count ($Multiset.singleton x) y))
	)))
(assert (forall ((x $Ref)) (!
  (=
    ($Multiset.singleton x)
    ($Multiset.add $Multiset.empty<$Ref> x))
	:pattern (($Multiset.singleton x))
	:pattern (($Multiset.add $Multiset.empty<$Ref> x))
	)))
(assert (forall ((xs $Multiset<$Ref>) (x $Ref) (y $Ref)) (!
  (iff
    (< 0 ($Multiset.count ($Multiset.add xs x) y))
    (or
      (= x y)
      (< 0 ($Multiset.count xs y))))
	:pattern (($Multiset.count ($Multiset.add xs x) y))
	)))
(assert (forall ((xs $Multiset<$Ref>) (x $Ref)) (!
  (=
    ($Multiset.count ($Multiset.add xs x) x)
    (+ ($Multiset.count xs x) 1))
	:pattern (($Multiset.count ($Multiset.add xs x) x))
	)))
(assert (forall ((xs $Multiset<$Ref>) (x $Ref) (y $Ref)) (!
  (implies
    (< 0 ($Multiset.count xs x))
    (< 0 ($Multiset.count ($Multiset.add xs y) x)))
	:pattern (($Multiset.add xs y) ($Multiset.count xs x))
	)))
(assert (forall ((xs $Multiset<$Ref>) (x $Ref) (y $Ref)) (!
  (implies
    (not (= x y))
    (< ($Multiset.count ($Multiset.add xs x) y) ($Multiset.count xs y)))
	:pattern (($Multiset.add xs x) ($Multiset.count xs y))
	)))
(assert (forall ((xs $Multiset<$Ref>) (x $Ref)) (!
  (=
    ($Multiset.card ($Multiset.add xs x))
    (+ ($Multiset.card xs) 1))
	:pattern (($Multiset.card ($Multiset.add xs x)))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>) (x $Ref)) (!
  (=
    ($Multiset.count ($Multiset.union xs ys) x)
    (+ ($Multiset.count xs x) ($Multiset.count ys x)))
	:pattern (($Multiset.count ($Multiset.union xs ys) x))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>)) (!
  (=
    ($Multiset.card ($Multiset.union xs ys))
    (+ ($Multiset.card  xs) ($Multiset.card  ys)))
	:pattern (($Multiset.card ($Multiset.union xs ys)))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>) (x $Ref)) (!
  (implies
    (< 0 ($Multiset.count xs x))
    (< 0 ($Multiset.count ($Multiset.union xs ys) x)))
	:pattern (($Multiset.union xs ys) ($Multiset.count xs x))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>) (x $Ref)) (!
  (implies
    (< 0 ($Multiset.count ys x))
    (< 0 ($Multiset.count ($Multiset.union xs ys) x)))
	:pattern (($Multiset.union xs ys) ($Multiset.count ys x))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>)) (!
  (and
    (=
      ($Multiset.difference ($Multiset.union xs ys) xs)
      ys)
    (=
      ($Multiset.difference ($Multiset.union xs ys) ys)
      xs))
	:pattern (($Multiset.difference ($Multiset.union xs ys) xs))
	:pattern (($Multiset.difference ($Multiset.union xs ys) ys))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>) (x $Ref)) (!
  (=
    ($Multiset.count ($Multiset.intersection xs ys) x)
    ($Math.min ($Multiset.count xs x) ($Multiset.count ys x)))
	:pattern (($Multiset.count ($Multiset.intersection xs ys) x))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>)) (!
  (=
    ($Multiset.intersection ($Multiset.intersection xs ys) ys)
    ($Multiset.intersection xs ys))
	:pattern (($Multiset.intersection ($Multiset.intersection xs ys) ys))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>)) (!
  (=
    ($Multiset.intersection xs ($Multiset.intersection xs ys))
    ($Multiset.intersection xs ys))
	:pattern (($Multiset.intersection xs ($Multiset.intersection xs ys)))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>) (x $Ref)) (!
  (=
    ($Multiset.count ($Multiset.difference xs ys) x)
    ($Math.clip (- ($Multiset.count xs x) ($Multiset.count ys x))))
	:pattern (($Multiset.count ($Multiset.difference xs ys) x))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>) (x $Ref)) (!
  (implies
    (<= ($Multiset.count xs x) ($Multiset.count ys x))
    (=
      ($Multiset.count ($Multiset.difference xs ys) x)
      0))
	:pattern (($Multiset.count xs x) ($Multiset.count ys x) ($Multiset.count ($Multiset.difference xs ys) x))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>)) (!
  (iff
    ($Multiset.subset xs ys)
    (forall ((x $Ref)) (!
      (<= ($Multiset.count xs x) ($Multiset.count ys x))
	    :pattern (($Multiset.count xs x) ($Multiset.count ys x)))))
	:pattern (($Multiset.subset xs ys))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>)) (!
  (iff
    ($Multiset.eq xs ys)
    (forall ((x $Ref)) (!
      (= ($Multiset.count xs x) ($Multiset.count ys x))
      :pattern (($Multiset.count xs x) ($Multiset.count ys x)))))
	:pattern (($Multiset.eq xs ys))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>)) (!
  (implies
    ($Multiset.eq xs ys)
    (= xs ys))
	:pattern (($Multiset.eq xs ys))
	)))
(assert (forall ((xs $Multiset<$Ref>) (ys $Multiset<$Ref>)) (!
  (iff
    ($Multiset.disjoint xs ys)
    (forall ((x $Ref)) (!
      (or
        (= ($Multiset.count xs x) 0)
        (= ($Multiset.count ys x) 0))
      :pattern (($Multiset.count xs x) ($Multiset.count ys x)))))
	:pattern (($Multiset.disjoint xs ys))
	)))
; /dafny_axioms/multisets_axioms_dafny.smt2 [Int]
(assert (forall ((xs $Multiset<Int>)) (!
  (< 0 ($Multiset.card xs))
	:pattern (($Multiset.card xs))
	)))
(assert (forall ((x Int)) (!
  (= ($Multiset.count $Multiset.empty<Int> x) 0)
	:pattern (($Multiset.count $Multiset.empty<Int> x))
	)))
(assert (forall ((xs $Multiset<Int>)) (!
  (and
    (iff
      (= ($Multiset.card xs) 0)
      (= xs $Multiset.empty<Int>))
    (implies
      (not (= ($Multiset.card xs) 0))
      (exists ((x Int)) (!
        (< 0 ($Multiset.count xs x))
        :pattern (($Multiset.count xs x))
        ))))
	:pattern (($Multiset.card xs))
	)))
(assert (forall ((x Int) (y Int)) (!
  (and
    (iff
      (= 1 ($Multiset.count ($Multiset.singleton x) y))
      (= x y))
    (iff
      (= 0 ($Multiset.count ($Multiset.singleton x) y))
      (not (= x y))))
	:pattern (($Multiset.count ($Multiset.singleton x) y))
	)))
(assert (forall ((x Int)) (!
  (=
    ($Multiset.singleton x)
    ($Multiset.add $Multiset.empty<Int> x))
	:pattern (($Multiset.singleton x))
	:pattern (($Multiset.add $Multiset.empty<Int> x))
	)))
(assert (forall ((xs $Multiset<Int>) (x Int) (y Int)) (!
  (iff
    (< 0 ($Multiset.count ($Multiset.add xs x) y))
    (or
      (= x y)
      (< 0 ($Multiset.count xs y))))
	:pattern (($Multiset.count ($Multiset.add xs x) y))
	)))
(assert (forall ((xs $Multiset<Int>) (x Int)) (!
  (=
    ($Multiset.count ($Multiset.add xs x) x)
    (+ ($Multiset.count xs x) 1))
	:pattern (($Multiset.count ($Multiset.add xs x) x))
	)))
(assert (forall ((xs $Multiset<Int>) (x Int) (y Int)) (!
  (implies
    (< 0 ($Multiset.count xs x))
    (< 0 ($Multiset.count ($Multiset.add xs y) x)))
	:pattern (($Multiset.add xs y) ($Multiset.count xs x))
	)))
(assert (forall ((xs $Multiset<Int>) (x Int) (y Int)) (!
  (implies
    (not (= x y))
    (< ($Multiset.count ($Multiset.add xs x) y) ($Multiset.count xs y)))
	:pattern (($Multiset.add xs x) ($Multiset.count xs y))
	)))
(assert (forall ((xs $Multiset<Int>) (x Int)) (!
  (=
    ($Multiset.card ($Multiset.add xs x))
    (+ ($Multiset.card xs) 1))
	:pattern (($Multiset.card ($Multiset.add xs x)))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>) (x Int)) (!
  (=
    ($Multiset.count ($Multiset.union xs ys) x)
    (+ ($Multiset.count xs x) ($Multiset.count ys x)))
	:pattern (($Multiset.count ($Multiset.union xs ys) x))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>)) (!
  (=
    ($Multiset.card ($Multiset.union xs ys))
    (+ ($Multiset.card  xs) ($Multiset.card  ys)))
	:pattern (($Multiset.card ($Multiset.union xs ys)))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>) (x Int)) (!
  (implies
    (< 0 ($Multiset.count xs x))
    (< 0 ($Multiset.count ($Multiset.union xs ys) x)))
	:pattern (($Multiset.union xs ys) ($Multiset.count xs x))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>) (x Int)) (!
  (implies
    (< 0 ($Multiset.count ys x))
    (< 0 ($Multiset.count ($Multiset.union xs ys) x)))
	:pattern (($Multiset.union xs ys) ($Multiset.count ys x))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>)) (!
  (and
    (=
      ($Multiset.difference ($Multiset.union xs ys) xs)
      ys)
    (=
      ($Multiset.difference ($Multiset.union xs ys) ys)
      xs))
	:pattern (($Multiset.difference ($Multiset.union xs ys) xs))
	:pattern (($Multiset.difference ($Multiset.union xs ys) ys))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>) (x Int)) (!
  (=
    ($Multiset.count ($Multiset.intersection xs ys) x)
    ($Math.min ($Multiset.count xs x) ($Multiset.count ys x)))
	:pattern (($Multiset.count ($Multiset.intersection xs ys) x))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>)) (!
  (=
    ($Multiset.intersection ($Multiset.intersection xs ys) ys)
    ($Multiset.intersection xs ys))
	:pattern (($Multiset.intersection ($Multiset.intersection xs ys) ys))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>)) (!
  (=
    ($Multiset.intersection xs ($Multiset.intersection xs ys))
    ($Multiset.intersection xs ys))
	:pattern (($Multiset.intersection xs ($Multiset.intersection xs ys)))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>) (x Int)) (!
  (=
    ($Multiset.count ($Multiset.difference xs ys) x)
    ($Math.clip (- ($Multiset.count xs x) ($Multiset.count ys x))))
	:pattern (($Multiset.count ($Multiset.difference xs ys) x))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>) (x Int)) (!
  (implies
    (<= ($Multiset.count xs x) ($Multiset.count ys x))
    (=
      ($Multiset.count ($Multiset.difference xs ys) x)
      0))
	:pattern (($Multiset.count xs x) ($Multiset.count ys x) ($Multiset.count ($Multiset.difference xs ys) x))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>)) (!
  (iff
    ($Multiset.subset xs ys)
    (forall ((x Int)) (!
      (<= ($Multiset.count xs x) ($Multiset.count ys x))
	    :pattern (($Multiset.count xs x) ($Multiset.count ys x)))))
	:pattern (($Multiset.subset xs ys))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>)) (!
  (iff
    ($Multiset.eq xs ys)
    (forall ((x Int)) (!
      (= ($Multiset.count xs x) ($Multiset.count ys x))
      :pattern (($Multiset.count xs x) ($Multiset.count ys x)))))
	:pattern (($Multiset.eq xs ys))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>)) (!
  (implies
    ($Multiset.eq xs ys)
    (= xs ys))
	:pattern (($Multiset.eq xs ys))
	)))
(assert (forall ((xs $Multiset<Int>) (ys $Multiset<Int>)) (!
  (iff
    ($Multiset.disjoint xs ys)
    (forall ((x Int)) (!
      (or
        (= ($Multiset.count xs x) 0)
        (= ($Multiset.count ys x) 0))
      :pattern (($Multiset.count xs x) ($Multiset.count ys x)))))
	:pattern (($Multiset.disjoint xs ys))
	)))
; /field_value_functions_axioms.smt2 [f: Int]
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
(declare-fun $SortWrappers.$Seq<Int>To$Snap ($Seq<Int>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Seq<Int> ($Snap) $Seq<Int>)
(assert (forall ((x $Seq<Int>)) (!
    (= x ($SortWrappers.$SnapTo$Seq<Int>($SortWrappers.$Seq<Int>To$Snap x)))
    :pattern (($SortWrappers.$Seq<Int>To$Snap x))
    )))
(declare-fun $SortWrappers.$Seq<$Ref>To$Snap ($Seq<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Seq<$Ref> ($Snap) $Seq<$Ref>)
(assert (forall ((x $Seq<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$Seq<$Ref>($SortWrappers.$Seq<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$Seq<$Ref>To$Snap x))
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$Set<Int>To$Snap ($Set<Int>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Set<Int> ($Snap) $Set<Int>)
(assert (forall ((x $Set<Int>)) (!
    (= x ($SortWrappers.$SnapTo$Set<Int>($SortWrappers.$Set<Int>To$Snap x)))
    :pattern (($SortWrappers.$Set<Int>To$Snap x))
    )))
(declare-fun $SortWrappers.$Set<$Ref>To$Snap ($Set<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Set<$Ref> ($Snap) $Set<$Ref>)
(assert (forall ((x $Set<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$Set<$Ref>($SortWrappers.$Set<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$Set<$Ref>To$Snap x))
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$Multiset<Int>To$Snap ($Multiset<Int>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Multiset<Int> ($Snap) $Multiset<Int>)
(assert (forall ((x $Multiset<Int>)) (!
    (= x ($SortWrappers.$SnapTo$Multiset<Int>($SortWrappers.$Multiset<Int>To$Snap x)))
    :pattern (($SortWrappers.$Multiset<Int>To$Snap x))
    )))
(declare-fun $SortWrappers.$Multiset<$Ref>To$Snap ($Multiset<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$Multiset<$Ref> ($Snap) $Multiset<$Ref>)
(assert (forall ((x $Multiset<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$Multiset<$Ref>($SortWrappers.$Multiset<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$Multiset<$Ref>To$Snap x))
    )))
; Declaring additional sort wrappers
(declare-fun $SortWrappers.$FVF<Int>To$Snap ($FVF<Int>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<Int> ($Snap) $FVF<Int>)
(assert (forall ((x $FVF<Int>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<Int>($SortWrappers.$FVF<Int>To$Snap x)))
    :pattern (($SortWrappers.$FVF<Int>To$Snap x))
    )))
(declare-fun $SortWrappers.$FVF<$Ref>To$Snap ($FVF<$Ref>) $Snap)
(declare-fun $SortWrappers.$SnapTo$FVF<$Ref> ($Snap) $FVF<$Ref>)
(assert (forall ((x $FVF<$Ref>)) (!
    (= x ($SortWrappers.$SnapTo$FVF<$Ref>($SortWrappers.$FVF<$Ref>To$Snap x)))
    :pattern (($SortWrappers.$FVF<$Ref>To$Snap x))
    )))
; Preamble end
; ------------------------------------------------------------
; ------------------------------------------------------------
; Declaring program functions
; ---------- find_var ----------
(declare-const S@1 $Seq<$Ref>)
(declare-const i@7 Int)
(declare-const $t@8 $FVF<Int>)
(declare-fun inv@9 ($Ref) Int)

(assert (forall ((r $Ref)) (!
  (implies
    ($Seq.in ($Seq.rng 0 ($Seq.len S@1)) i@7)
    (= ($Seq.at S@1 (inv@9 r)) r))
  :pattern (($Seq.at S@1 (inv@9 r)))
)))

(assert (forall ((i@7 Int)) (! (implies ($Seq.in ($Seq.rng 0 ($Seq.len S@1)) i@7) (= (inv@9 ($Seq.at S@1 i@7)) i@7)) :pattern (($Seq.in ($Seq.rng 0 ($Seq.len S@1)) i@7)) :pattern ((inv@9 ($Seq.at S@1 i@7))))))

(assert (forall ((x Int) (y Int)) (!
  (implies
    (and (and ($Seq.in ($Seq.rng 0 ($Seq.len S@1)) x) ($Seq.in ($Seq.rng 0 ($Seq.len S@1)) y)) (= ($Seq.at S@1 x) ($Seq.at S@1 y)))
    (= x y))
  :pattern (($Seq.in ($Seq.rng 0 ($Seq.len S@1)) x) ($Seq.in ($Seq.rng 0 ($Seq.len S@1)) y))
  :pattern (($Seq.in ($Seq.rng 0 ($Seq.len S@1)) x) ($Seq.at S@1 y))
  :pattern (($Seq.in ($Seq.rng 0 ($Seq.len S@1)) y) ($Seq.at S@1 x))
  :pattern (($Seq.at S@1 x) ($Seq.at S@1 y))
)))

(assert (forall ((i@7 Int)) (!
  (implies
    ($Seq.in ($Seq.rng 0 ($Seq.len S@1)) (inv@9 ($Seq.at S@1 i@7)))
    (not (= ($Seq.at S@1 i@7) $Ref.null)))
  :pattern (($Seq.in ($Seq.rng 0 ($Seq.len S@1)) (inv@9 ($Seq.at S@1 i@7))))
  :qid |non-null|
)))

(assert (forall ((i@7 Int)) (!
  (iff
    ($Set.in ($Seq.at S@1 i@7) ($FVF.domain_f $t@8))
    ($Seq.in ($Seq.rng 0 ($Seq.len S@1)) i@7))
  :pattern (($FVF.lookup_f $t@8 ($Seq.at S@1 i@7)))
)))

(assert (= ($Seq.len S@1) 1))

(push) ; 6
(assert (not (not (= ($Seq.at S@1 0) $Ref.null))))
  ; Cannot be proven because the non-null axiom won't be triggered.
(check-sat)
; unknown
; 0.00s
(pop) ; 6
