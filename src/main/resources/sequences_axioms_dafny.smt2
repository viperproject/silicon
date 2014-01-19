; General sequence axioms

; axiom (forall<T> s: Seq T :: { Seq#Length(s) } 0 <= Seq#Length(s));
(assert (forall ((xs $Seq<$S$>)) (!
	(<= 0 ($Seq.len xs))
	:pattern (($Seq.len xs))
	)))

; axiom (forall<T> :: Seq#Length(Seq#Empty(): Seq T) == 0);
(assert (= ($Seq.len $Seq.nil<$S$>) 0))

; axiom (forall<T> s: Seq T :: { Seq#Length(s) } Seq#Length(s) == 0 ==> s == Seq#Empty());
(assert (forall ((xs $Seq<$S$>)) (!
	(implies
		(= ($Seq.len xs) 0)
		(= xs $Seq.nil<$S$>))
	:pattern (($Seq.len xs))
	)))

; axiom (forall<T> t: T :: { Seq#Length(Seq#Singleton(t)) } Seq#Length(Seq#Singleton(t)) == 1);
(assert (forall ((x $S$)) (!
	(= ($Seq.len ($Seq.elem x)) 1)
	:pattern (($Seq.len ($Seq.elem x)))
	)))


; axiom (forall<T> s: Seq T, i: int, v: T, len: int :: { Seq#Length(Seq#Build(s,i,v,len)) }
  ; 0 <= len ==> Seq#Length(Seq#Build(s,i,v,len)) == len);
(assert (forall ((xs $Seq<$S$>) (i Int) (x $S$) (n Int)) (!
	(implies
		(<= 0 n)
		(= ($Seq.len ($Seq.build xs i x n)) n))
	:pattern (($Seq.len ($Seq.build xs i x n)))
	)))


; axiom (forall<T> s0: Seq T, s1: Seq T :: { Seq#Length(Seq#Append(s0,s1)) }
  ; Seq#Length(Seq#Append(s0,s1)) == Seq#Length(s0) + Seq#Length(s1));
(assert (forall ((xs $Seq<$S$>) (ys $Seq<$S$>)) (!
	(=
		($Seq.len ($Seq.con xs ys))
		(+ ($Seq.len xs) ($Seq.len ys)))
	:pattern (($Seq.len ($Seq.con xs ys)))
	)))


; axiom (forall<T> t: T :: { Seq#Index(Seq#Singleton(t), 0) } Seq#Index(Seq#Singleton(t), 0) == t);
(assert (forall ((x $S$)) (!
	(= ($Seq.at ($Seq.elem x) 0) x)
	:pattern (($Seq.at ($Seq.elem x) 0))
	)))

; axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#Index(Seq#Append(s0,s1), n) }
  ; (n < Seq#Length(s0) ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s0, n)) &&
  ; (Seq#Length(s0) <= n ==> Seq#Index(Seq#Append(s0,s1), n) == Seq#Index(s1, n - Seq#Length(s0))));
(assert (forall ((xs $Seq<$S$>) (ys $Seq<$S$>) (i Int)) (!
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
(assert (forall ((xs $Seq<$S$>) (i Int) (x $S$) (n Int) (j Int)) (!
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

(assert (forall ((x $S$)) (!
	($Seq.in ($Seq.elem x) x)
	:pattern (($Seq.in ($Seq.elem x) x))
	)))

; axiom (forall<T> s: Seq T, x: T :: { Seq#Contains(s,x) }
  ; Seq#Contains(s,x) <==>
    ; (exists i: int :: { Seq#Index(s,i) } 0 <= i && i < Seq#Length(s) && Seq#Index(s,i) == x));
(assert (forall ((xs $Seq<$S$>) (x $S$)) (!
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
(assert (forall ((x $S$)) (!
	(not ($Seq.in $Seq.nil<$S$> x))
	:pattern (($Seq.in $Seq.nil<$S$> x))
	)))

; axiom (forall<T> s0: Seq T, s1: Seq T, x: T ::
  ; { Seq#Contains(Seq#Append(s0, s1), x) }
  ; Seq#Contains(Seq#Append(s0, s1), x) <==>
    ; Seq#Contains(s0, x) || Seq#Contains(s1, x));
(assert (forall ((xs $Seq<$S$>) (ys $Seq<$S$>) (x $S$)) (!
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
(assert (forall ((xs $Seq<$S$>) (i Int) (x $S$) (n Int) (y $S$)) (!
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
(assert (forall ((xs $Seq<$S$>) (k Int) (x $S$)) (!
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
(assert (forall ((xs $Seq<$S$>) (k Int) (x $S$)) (!
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
(assert (forall ((xs $Seq<$S$>) (ys $Seq<$S$>)) (!
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
(assert (forall ((xs $Seq<$S$>) (ys $Seq<$S$>)) (!
	(implies
		($Seq.eq xs ys)
		(= xs ys))
	:pattern (($Seq.eq xs ys))
	)))

; [2012-07-10 Malte]
;   Added because
;     assert [x] == [y]  ==>  x == y
;   used to fail. The reason for the previous failure could be, that the
;   left-hand side [x] == [y] triggers the extensionality axiom for sequence,
;   where $Seq.eq(xs, ys) implies xs == ys.
;   However, here we have xs ≡ $Seq.elem(x) and ys ≡ $Seq.elem(y),
;   but Z3 does not know that  $Seq.elem(x) == $Seq.elem(y) implies x == y.
(assert (forall ((x $S$) (y $S$)) (!
	(implies
		($Seq.eq ($Seq.elem x) ($Seq.elem y))
		(= x y))
	:pattern (($Seq.eq ($Seq.elem x) ($Seq.elem y)))
	)))


; axiom (forall<T> s0: Seq T, s1: Seq T, n: int :: { Seq#SameUntil(s0,s1,n) }
  ; Seq#SameUntil(s0,s1,n) <==>
    ; (forall j: int :: { Seq#Index(s0,j) } { Seq#Index(s1,j) }
        ; 0 <= j && j < n ==> Seq#Index(s0,j) == Seq#Index(s1,j)));
(assert (forall ((xs $Seq<$S$>) (ys $Seq<$S$>) (i Int)) (!
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
(assert (forall ((xs $Seq<$S$>) (k Int)) (!
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
(assert (forall ((xs $Seq<$S$>) (k Int) (i Int)) (!
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
(assert (forall ((xs $Seq<$S$>) (k Int)) (!
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
(assert (forall ((xs $Seq<$S$>) (k Int) (i Int)) (!
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
(assert (forall ((xs $Seq<$S$>) (ys $Seq<$S$>)) (!
	(and
		(= ($Seq.take ($Seq.con xs ys) ($Seq.len xs)) xs)
		(= ($Seq.drop ($Seq.con xs ys) ($Seq.len xs)) ys))
	:pattern (($Seq.con xs ys))
	)))

;axiom (forall<T> s: Seq_ T, i: int, v: T :: { Seq#Length(Seq#Update(s,i,v)) }
;  0 <= i && i < Seq#Length(s) ==> Seq#Length(Seq#Update(s,i,v)) == Seq#Length(s));
(assert (forall ((xs $Seq<$S$>) (i Int) (x $S$)) (!
  (implies
    (and
      (<= 0 i)
      (< i ($Seq.len xs)))
    (=
      ($Seq.len ($Seq.update xs i x))
      ($Seq.len xs)))
  :pattern (($Seq.len ($Seq.update xs i x)))
  )))

;axiom (forall<T> s: Seq_ T, i: int, v: T, n: int :: { Seq#Index(Seq#Update(s,i,v),n) }
;  0 <= n && n < Seq#Length(s) ==>
;       (i == n ==> Seq#Index(Seq#Update(s,i,v),n) == v)
;    && (i != n ==> Seq#Index(Seq#Update(s,i,v),n) == Seq#Index(s,n)));
(assert (forall ((xs $Seq<$S$>) (i Int) (x $S$) (j Int)) (!
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

; Commutativity of Take and Drop with Update.

;axiom (forall<T> s: Seq_ T, i: int, v: T, n: int :: { Seq#Take(Seq#Update(s, i, v), n) }
;  0 <= i && i < n && n <= Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Update(Seq#Take(s, n), i, v));
(assert (forall ((xs $Seq<$S$>) (i Int) (x $S$) (j Int)) (!
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

;axiom (forall<T> s: Seq_ T, i: int, v: T, n: int :: { Seq#Take(Seq#Update(s, i, v), n) }
;  n <= i && i < Seq#Length(s) ==> Seq#Take(Seq#Update(s, i, v), n) == Seq#Take(s, n));
(assert (forall ((xs $Seq<$S$>) (i Int) (x $S$) (j Int)) (!
  (implies
    (and
      (<= j i)
      (< i ($Seq.len xs)))
    (=
      ($Seq.take ($Seq.update xs i x) j)
      ($Seq.take xs j)))
  :pattern (($Seq.take ($Seq.update xs i x) j))
  )))

;axiom (forall<T> s: Seq_ T, i: int, v: T, n: int :: { Seq#Drop(Seq#Update(s, i, v), n) }
;  0 <= n && n <= i && i < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Update(Seq#Drop(s, n), i-n, v) );
(assert (forall ((xs $Seq<$S$>) (i Int) (x $S$) (j Int)) (!
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

;axiom (forall<T> s: Seq_ T, i: int, v: T, n: int :: { Seq#Drop(Seq#Update(s, i, v), n) }
;  0 <= i && i < n && n < Seq#Length(s) ==> Seq#Drop(Seq#Update(s, i, v), n) == Seq#Drop(s, n));
(assert (forall ((xs $Seq<$S$>) (i Int) (x $S$) (j Int)) (!
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
;axiom (forall<T> s: Seq T, v: T :: { MultiSet#FromSeq(Seq#Build(s, v)) } MultiSet#FromSeq(Seq#Build(s, v)) == MultiSet#UnionOne(MultiSet#FromSeq(s), v));
;(assert (forall ((xs $Seq<$S$>) (x $S$)) (!
;    (=
;        ($Multiset<$S$>.fromSeq ($Seq<$S$>.build xs x))
;        ($Multiset<$S$>.union (Multiset<$S$>.fromSeq(xs)) (Multiset<$S$>.singleton x)))
;    :pattern (($Multiset<$S$>.fromSeq ($Seq<$S$>.build xs x)))
;    )))

;axiom (forall<T> :: MultiSet#FromSeq(Seq#Empty(): Seq T) == MultiSet#Empty(): MultiSet T);
(assert (= ($Multiset.fromSeq $Seq.nil<$S$>) $Multiset.empty<$S$>))

;axiom (forall<T> a: Seq T, b: Seq T :: { MultiSet#FromSeq(Seq#Append(a, b)) } MultiSet#FromSeq(Seq#Append(a, b)) == MultiSet#Union(MultiSet#FromSeq(a), MultiSet#FromSeq(b)));
;(assert (forall ((a $Seq<$S$>) (b $Seq<$S$>)) (!
;    (=
;        ($Multiset.fromSeq ($Seq.con a b))
;        ($Multiset.union ($Multiset.fromSeq a) ($Multiset.fromSeq b)))
;    :pattern (($Multiset.fromSeq ($Seq.con a b)))
;)))

;axiom (forall<T> s: Seq T, i: int, v: T, x: T :: { MultiSet#FromSeq(Seq#Update(s, i, v))[x] } 0 <= i && i < Seq#Length(s) ==> MultiSet#FromSeq(Seq#Update(s, i, v))[x] == MultiSet#Union(MultiSet#Difference(MultiSet#FromSeq(s), MultiSet#Singleton(Seq#Index(s, i))), MultiSet#Singleton(v))[x]);


;axiom (forall<T> s: Seq T, x: T :: { MultiSet#FromSeq(s)[x] } (exists i: int :: { Seq#Index(s, i) } 0 <= i && i < Seq#Length(s) && x == Seq#Index(s, i)) <==> 0 < MultiSet#FromSeq(s)[x]);
;(assert (forall ((s $Seq<$S$>) (x $S$)) (!
;    (iff
 ;       (exists ((i Int)) (!
 ;           (and
 ;               (<= 0 i)
 ;               (< i ($Seq.len s))
 ;               (= x ($Seq.at s i)))
  ;     :pattern (($Seq.at s i))))
  ;      (< 0 ($Multiset.count ($Multiset.fromSeq s) x)))
  ;  :pattern (($Multiset.count ($Multiset.fromSeq s) x))
  ;  )))

;additional axioms to support counting for splitted sequences
; count if we know two different indices
; bit of a special case
; TODO: pattern
(assert (forall ((s $Seq<$S$>) (x $S$)) (!
    (iff
        (exists ((i Int) (j Int))
            (and
                (not (= i j))
                (<= 0 i)
                (<= 0 j)
                (< i ($Seq.len s))
                (< j ($Seq.len s))
                (= ($Seq.at s i) x)
                (= ($Seq.at s j) x)
            )
         )
        (>= ($Multiset.count ($Multiset.fromSeq s) x) 2)
    )
    )))


; trigger functions for these axioms
(declare-fun $Seq.split($Seq<$S$> $S$ Int Int Int) Bool)
(declare-fun $Seq.countP ($Seq<$S$> $S$) Int)
(assert (forall ((s $Seq<$S$>) (x $S$) (a Int) (b Int) (c Int) (d Int) (e Int) (f Int)) (!
    (and
        ($Seq.split s x d e b)
        ($Seq.split s x a c b)
        ($Seq.split s x a f b)
        ($Seq.split s x a c d)
    )
    :pattern (($Multiset.count ($Multiset.fromSeq ($Seq.drop ($Seq.take s b) a)) x)
              ($Multiset.count ($Multiset.fromSeq ($Seq.drop ($Seq.take s d) c)) x)
              ($Multiset.count ($Multiset.fromSeq ($Seq.drop ($Seq.take s f) e)) x))
    )))
(assert (forall ((s $Seq<$S$>) (x $S$)) (!
        (= ($Multiset.count ($Multiset.fromSeq s) x) ($Seq.countP s x))
    :pattern (($Multiset.count ($Multiset.fromSeq s) x))
    )))
(assert (forall ((s $Seq<$S$>) (x $S$)) (!
        (<= 0 ($Seq.countP s x))
    :pattern (($Seq.countP s x))
    )))
(assert (forall ((s $Seq<$S$>) (x $S$) (start Int) (end Int) (k Int)) (!
        (implies
            (and (<= start k) (<= k end))
            (= ($Seq.countP  ($Seq.drop ($Seq.take s end) start) x)
                (+ ($Seq.countP ($Seq.drop ($Seq.take s k) start) x)
                    ($Seq.countP  ($Seq.drop ($Seq.take s end) k) x)
            )
            )
        )
        :pattern (($Seq.split s x start k end))
    )))
(assert (forall ((S $Seq<$S$>) (start Int) (end  Int) (i Int)) (!
    (iff
        (and
            (<= 0 start)
            (<= end ($Seq.len S))
            (<= start i)
            (< i end)
        )
        (< 0 ($Multiset.count ($Multiset.fromSeq ($Seq.drop ($Seq.take S end) start)) ($Seq.at S i)))
    )
   :pattern (($Multiset.count ($Multiset.fromSeq ($Seq.drop ($Seq.take S end) start)) ($Seq.at S i)))
   )))

