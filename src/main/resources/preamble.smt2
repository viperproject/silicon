; Tested with Z3 3.1

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

; ATTENTION: Continuing multi-line statements must be indented with at least
;            one tab or two spaces. All other lines must not start with tabs
;            or more than one space.

(declare-fun $unit () Int)

(declare-fun $null () Int)
(declare-fun $combine (Int Int) Int)
(declare-fun $snapEq (Int Int) Bool)

; (assert (forall (x1 Int) (x2 Int) (y1 Int) (y2 Int)
	; (implies
		; (= ($combine x1 y1) ($combine x2 y2))
		; (and (= x1 x2) (= y1 y2)))))
		
(assert (forall ((x1 Int) (x2 Int) (y1 Int) (y2 Int)) (!
	(implies
		($snapEq ($combine x1 y1) ($combine x2 y2))
		(and (= x1 x2) (= y1 y2)))
	:qid |Combine|
	:pattern (($snapEq ($combine x1 y1) ($combine x2 y2)))
	)))
	
(assert (forall ((x Int) (y Int)) (!
	(implies
		($snapEq x y)
		(and (= x y)))
	:qid |SnapEq|
	:pattern (($snapEq x y))
	)))
	
; (declare-datatypes (($Snap ($combine ($combine.first Int) ($combine.second Int)))))

(declare-fun $boolToInt (Bool) Int)
(declare-fun $intToBool (Int) Bool)

(assert (forall ((x Int))
	(= x ($boolToInt($intToBool x)))))

(assert (forall ((x Bool))
	(= x ($intToBool($boolToInt x)))))

; Notice that seqToInt, intToSeq aren't declared since sequences are Z3-encoded
; as integers.

; --- General math ---

(declare-fun $Math.abs (Int) Int)

(assert (forall ((i Int))
	(and
		(implies (< i 0) (= ($Math.abs i) (- 0 i)))
		(implies (>= i 0) (= ($Math.abs i) i)))
	))

; --- Credits ---	
	
(declare-fun $Credits.credits (Int Int) Int)

; Macros
	
; (define ($Credits.allZero (x Int) (v Int))
	; (forall (r Int)
		; (= ($Credits.credits r v) 0)
	; ; :pat {($Credits.credits r v)})))
	; ))

; (define ($Credits.credits.updated (x Int) (v Int))
(define-fun $Credits.credits.updated ((x Int) (v Int)) Bool
	(forall ((r Int))
		(implies
			(not (= r x))
			(= ($Credits.credits r v) ($Credits.credits r (- v 1))))
	; :pat {($Credits.credits r v) ($Credits.credits r (- v 1))})))
	))
	
; --- Lock modes ---

(declare-datatypes ()
	(($Locks.mode $Locks.mode.none $Locks.mode.read $Locks.mode.write)))

; ; --- Locks ---

(declare-fun $Locks.bottom () Int)
(declare-fun $Locks.holds (Int Int) $Locks.mode)
(declare-fun $Locks.mu (Int Int) Int)
(declare-fun $Locks.less (Int Int) Bool)

; Macros

; (define ($Locks.holds.updated (x Int) (v Int))
(define-fun $Locks.holds.updated ((x Int) (v Int)) Bool
	(forall ((r Int))
		(implies
			(not (= r x))
			(= ($Locks.holds r v) ($Locks.holds r (- v 1))))
	; :pat {($Locks.holds x v p) ($Locks.holds r (- v 1))})))
	))
		
; (define ($Locks.mu.updated (x Int) (v Int))
(define-fun $Locks.mu.updated ((x Int) (v Int)) Bool
	(forall ((r Int))
		(implies
			(not (= r x))
			(= ($Locks.mu r v) ($Locks.mu r (- v 1))))
	; :pat {($Locks.mu r v) ($Locks.mu r (- v 1))})))
	))

; (define ($Locks.maxlock.less (m Int) (v Int) (w Int) (c Int))
(define-fun $Locks.maxlock.less ((m Int) (v Int) (w Int) (c Int)) Bool
	(forall ((r Int))
		(implies
			; (not (= ($Locks.holds r v) $Locks.mode.none))
			(or
				(not (= ($Locks.holds r v) $Locks.mode.none))
				(< ($Credits.credits r c) 0))
			($Locks.less ($Locks.mu r w) m))))

; (define ($Locks.maxlock.atMost (m Int) (v Int) (w Int) (c Int))
(define-fun $Locks.maxlock.atMost ((m Int) (v Int) (w Int) (c Int)) Bool
  (forall ((r Int))
    (implies
			(or
				(not (= ($Locks.holds r v) $Locks.mode.none))
				(< ($Credits.credits r c) 0))
      (or
        ($Locks.less ($Locks.mu r w) m)
        (= ($Locks.mu r w) m)))))

; Axioms

(assert (forall ((t1 Int) (t2 Int)) (!
  (implies
    ($Locks.less t1 t2)
    (not (= t2 $Locks.bottom)))
  :pattern (($Locks.less t1 t2)))))
  ; ))

(assert (forall ((m Int)) (!
	(implies
		(not (= $Locks.bottom m))
		($Locks.less $Locks.bottom m))
	:pattern (($Locks.less $Locks.bottom m)))))
	; ))

(assert (forall ((t1 Int) (t2 Int)) (!
  (not (and ($Locks.less t1 t2) ($Locks.less t2 t1)))
  :pattern (($Locks.less t1 t2) ($Locks.less t2 t1)))))
  ; ))

(assert (forall ((m1 Int) (m2 Int) (m3 Int)) (!
	(implies
		(and ($Locks.less m1 m2) ($Locks.less m2 m3))
		($Locks.less m1 m3))
	:pattern (($Locks.less m1 m2) ($Locks.less m2 m3) ($Locks.less m1 m3)))))
	; ))
	
(assert (forall ((t1 Int) (t2 Int) (v Int) (w Int))
	(implies
		(and (not (= t1 t2))
		(and (not (= ($Locks.holds t1 v) $Locks.mode.none))
				 (not (= ($Locks.holds t2 v) $Locks.mode.none))))
		(not (= ($Locks.mu t1 w) ($Locks.mu t2 w))))
	; :pat {($Locks.holds t1 v) ($Locks.holds t2 v) ($Locks.mu t1) ($Locks.mu t2)}
	))
	
; --- Sequences	---
	
(declare-fun $Seq.nil () Int)
(declare-fun $Seq.len (Int) Int)
(declare-fun $Seq.elem (Int) Int)
; function Seq#Build<T>(s: Seq T, index: int, val: T, newLength: int) returns (Seq T);
(declare-fun $Seq.build (Int Int Int Int) Int)
; function Seq#Append<T>(Seq T, Seq T) returns (Seq T);
(declare-fun $Seq.con (Int Int) Int)
; function Seq#Index<T>(Seq T, int) returns (T);
(declare-fun $Seq.at (Int Int) Int)
; function Seq#Contains<T>(Seq T, T) returns (bool);
(declare-fun $Seq.in (Int Int) Bool)
; function Seq#Equal<T>(Seq T, Seq T) returns (bool);
(declare-fun $Seq.eq (Int Int) Bool)
; function Seq#SameUntil<T>(Seq T, Seq T, int) returns (bool);
(declare-fun $Seq.sameUntil (Int Int Int) Bool)
; function Seq#Take<T>(s: Seq T, howMany: int) returns (Seq T);
(declare-fun $Seq.take (Int Int) Int)
; function Seq#Drop<T>(s: Seq T, howMany: int) returns (Seq T);
(declare-fun $Seq.drop (Int Int) Int)
; function Seq#Range(min: int, max: int) returns (Seq int);
(declare-fun $Seq.rng (Int Int) Int)

; axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));
(assert (forall ((xs Int)) (!
	(<= 0 ($Seq.len xs))
	:pattern (($Seq.len xs))
	)))


; axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
(assert (= ($Seq.len $Seq.nil) 0))

; axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());
(assert (forall ((xs Int)) (!
	(implies
		(= ($Seq.len xs) 0)
		(= xs $Seq.nil))
	:pattern (($Seq.len xs))
	)))

; axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);
(assert (forall ((x Int)) (!
	(= ($Seq.len ($Seq.elem x)) 1)
	:pattern (($Seq.len ($Seq.elem x)))
	)))


; axiom (forall<T> s: Seq T, i: int, v: T, len: int :: { Seq#Length(Seq#Build(s,i,v,len)) }
  ; 0 <= len ==> Seq#Length(Seq#Build(s,i,v,len)) == len);
(assert (forall ((xs Int) (i Int) (x Int) (n Int)) (!
	(implies
		(<= 0 n)
		(= ($Seq.len ($Seq.build xs i x n)) n))
	:pattern (($Seq.len ($Seq.build xs i x n)))
	)))
	

; axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
  ; Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));
(assert (forall ((xs Int) (ys Int)) (!
	(=
		($Seq.len ($Seq.con xs ys))
		(+ ($Seq.len xs) ($Seq.len ys)))
	:pattern (($Seq.len ($Seq.con xs ys)))
	)))


; axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
(assert (forall ((x Int)) (!
	(= ($Seq.at ($Seq.elem x) 0) x)
	:pattern (($Seq.at ($Seq.elem x) 0))
	)))

; axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  ; (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  ; (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
(assert (forall ((xs Int) (ys Int) (i Int)) (!
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
	
; axiom (forall<T> s: Seq T, i: int, v: T, len: int, n: int :: { Seq#Index(Seq#Build(s,i,v,len),n) }
  ; 0 <= n && n < len ==>
    ; (i == n ==> Seq#Index(Seq#Build(s,i,v,len),n) == v) &&
    ; (i != n ==> Seq#Index(Seq#Build(s,i,v,len),n) == Seq#Index(s,n)));
(assert (forall ((xs Int) (i Int) (x Int) (n Int) (j Int)) (!
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


; axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
  ; Seq#Contains(s,x) <==>
    ; (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
(assert (forall ((xs Int) (x Int)) (!
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
		
; axiom (forall x: ref ::
  ; { Seq#Contains(Seq#Empty(), x) }
  ; !Seq#Contains(Seq#Empty(), x));
(assert (forall ((x Int)) (!
	(not ($Seq.in $Seq.nil x))
	:pattern (($Seq.in $Seq.nil x))
	)))
	
; axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  ; { Seq#Contains(Seq#Append(s0, s1), x) }
  ; Seq#Contains(Seq#Append(s0, s1), x) <==>
    ; Seq#Contains(s0, x) || Seq#Contains(s1, x));
(assert (forall ((xs Int) (ys Int) (x Int)) (!
	(iff
		($Seq.in ($Seq.con xs ys) x)
		(or
			($Seq.in xs x)
			($Seq.in ys x)))
	:pattern (($Seq.in ($Seq.con xs ys) x))
	)))
		
; axiom (forall<T> s: Seq T, i: int, v: T, len: int, x: T ::
  ; { Seq#Contains(Seq#Build(s, i, v, len), x) }
  ; Seq#Contains(Seq#Build(s, i, v, len), x) <==>
    ; (0 <= i && i < len && x == v)  ||  
    ; (exists j: int :: { Seq#Index(s,j) } 0 <= j && j < Seq#Length(s) && j < len && j!=i && Seq#Index(s,j) == x));
(assert (forall ((xs Int) (i Int) (x Int) (n Int) (y Int)) (!
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
		
; axiom (forall<T> s: Seq T, n: int, x: T ::
  ; { Seq#Contains(Seq#Take(s, n), x) }
  ; Seq#Contains(Seq#Take(s, n), x) <==>
    ; (exists i: int :: { Seq#Index(s, i) }
      ; 0 <= i && i < n && i < Seq#Length(s) && Seq#Index(s, i) == x));
(assert (forall ((xs Int) (k Int) (x Int)) (!
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
			
; axiom (forall<T> s: Seq T, n: int, x: T ::
  ; { Seq#Contains(Seq#Drop(s, n), x) }
  ; Seq#Contains(Seq#Drop(s, n), x) <==>
    ; (exists i: int :: { Seq#Index(s, i) }
      ; 0 <= n && n <= i && i < Seq#Length(s) && Seq#Index(s, i) == x));
(assert (forall ((xs Int) (k Int) (x Int)) (!
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


; axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Equal(s0,s1) }
  ; Seq#Equal(s0,s1) <==>
    ; Seq#Length(s0) == Seq#Length(s1) &&
    ; (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        ; 0 <= j && j < Seq#Length(s0) ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
(assert (forall ((xs Int) (ys Int)) (!
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
				
; axiom(forall<T> a: Seq T, b: Seq T :: { Seq#Equal(a,b) }  // extensionality axiom for sequences
  ; Seq#Equal(a,b) ==> a == b);
(assert (forall ((xs Int) (ys Int)) (!
	(implies
		($Seq.eq xs ys)
		(= xs ys))
	:pattern (($Seq.eq xs ys))
	)))


; axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
  ; Seq#SameUntil(s0,s1,n) <==>
    ; (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        ; 0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
(assert (forall ((xs Int) (ys Int) (i Int)) (!
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
				

; axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Take(s,n)) }
  ; 0 <= n ==>
    ; (n <= Seq#Length(s) ==> Seq#Length(Seq#Take(s,n)) == n) &&
    ; (Seq#Length(s) < n ==> Seq#Length(Seq#Take(s,n)) == Seq#Length(s)));
(assert (forall ((xs Int) (k Int)) (!
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
		
; axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Take(s,n), j) } {:weight 25}
  ; 0 <= j && j < n && j < Seq#Length(s) ==>
    ; Seq#Index(Seq#Take(s,n), j) == Seq#Index(s, j));
(assert (forall ((xs Int) (k Int) (i Int)) (!
	(implies
		(and
			(<= 0 i)
			(< i k)
			(< i ($Seq.len xs)))
		(= ($Seq.at ($Seq.take xs k) i) ($Seq.at xs i)))
	:weight 25
	:pattern (($Seq.at ($Seq.take xs k) i))
	)))

; axiom (forall<T> s: Seq T, n: int :: { Seq#Length(Seq#Drop(s,n)) }
  ; 0 <= n ==>
    ; (n <= Seq#Length(s) ==> Seq#Length(Seq#Drop(s,n)) == Seq#Length(s) - n) &&
    ; (Seq#Length(s) < n ==> Seq#Length(Seq#Drop(s,n)) == 0));
(assert (forall ((xs Int) (k Int)) (!
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
		
; axiom (forall<T> s: Seq T, n: int, j: int :: { Seq#Index(Seq#Drop(s,n), j) } {:weight 25}
  ; 0 <= n && 0 <= j && j < Seq#Length(s)-n ==>
    ; Seq#Index(Seq#Drop(s,n), j) == Seq#Index(s, j+n));
(assert (forall ((xs Int) (k Int) (i Int)) (!
	(implies
		(and
			(<= 0 k)
			(<= 0 i)
			(< i (- ($Seq.len xs) k)))
		(= ($Seq.at ($Seq.drop xs k) i) ($Seq.at xs (+ i k))))
	:weight 25
	:pattern (($Seq.at ($Seq.drop xs k) i))
	)))

; axiom (forall<T> s, t: Seq T ::
  ; { Seq#Append(s, t) }
  ; Seq#Take(Seq#Append(s, t), Seq#Length(s)) == s &&
  ; Seq#Drop(Seq#Append(s, t), Seq#Length(s)) == t);
(assert (forall ((xs Int) (ys Int)) (!
	(and
		(= ($Seq.take ($Seq.con xs ys) ($Seq.len xs)) xs)
		(= ($Seq.drop ($Seq.con xs ys) ($Seq.len xs)) ys))
	:pattern (($Seq.con xs ys))
	)))

; axiom (forall min: int, max: int :: { Seq#Length(Seq#Range(min, max)) } (min < max ==> Seq#Length(Seq#Range(min, max)) == max-min) && (max <= min ==> Seq#Length(Seq#Range(min, max)) == 0));
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

; axiom (forall min: int, max: int, j: int :: { Seq#Index(Seq#Range(min, max), j) } 0<=j && j<max-min ==> Seq#Index(Seq#Range(min, max), j) == min + j);
(assert (forall ((i Int) (j Int) (k Int)) (!
	(implies
		(and
			(<= 0 k)
			(< k (- j i)))
		(= ($Seq.at ($Seq.rng i j) k) (+ i k)))
	:pattern (($Seq.at ($Seq.rng i j) k))
	)))
	
; --- Setup	---

(assert (forall ((r Int))
		(= ($Credits.credits r 0) 0)
	; :pat {($Credits.credits r v)})))
	))

; (get-proof "stdout")
; (get-info statistics)

; (push)
; (check-sat)
; (pop)