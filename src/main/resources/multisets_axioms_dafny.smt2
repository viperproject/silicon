; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; These axioms correspond to Dafny's multiset axiomatisation from 2013-06-27.
; They depend on the set axiomatisation due to the fromSet-function.

;
; Multiset axioms
;

;type MultiSet T = [T]int;


; 2013-07-24 Malte: Ignored for now. Not sure when it should be used.
;// ints are non-negative, used after havocing, and for conversion from sequences to multisets.
;axiom (forall<T> ms: MultiSet T :: { $IsGoodMultiSet(ms) }
;  $IsGoodMultiSet(ms) <==> (forall bx: T :: { ms[bx] } 0 <= ms[bx]));


;axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) } 0 <= MultiSet#Card(s));
(assert (forall ((xs $Multiset<$S$>)) (!
  (< 0 ($Multiset.card xs))
	:pattern (($Multiset.card xs))
	)))

;axiom (forall<T> s: MultiSet T, x: T, n: int :: { MultiSet#Card(s[x := n]) }
;  0 <= n ==> MultiSet#Card(s[x := n]) == MultiSet#Card(s) - s[x] + n);
(assert (forall ((xs $Multiset<$S$>) (x $S$) (n Int)) (!
  (< 0 ($Multiset.card xs))
	:pattern (($Multiset.card xs))
	)))


;axiom (forall<T> o: T :: { MultiSet#Empty()[o] } MultiSet#Empty()[o] == 0);
(assert (forall ((x $S$)) (!
  (= ($Multiset.count $Multiset.empty<$S$> x) 0)
	:pattern (($Multiset.count $Multiset.empty<$S$> x))
	)))

;axiom (forall<T> s: MultiSet T :: { MultiSet#Card(s) }
;  (MultiSet#Card(s) == 0 <==> s == MultiSet#Empty()) &&
;  (MultiSet#Card(s) != 0 ==> (exists x: T :: 0 < s[x])));
(assert (forall ((xs $Multiset<$S$>)) (!
  (and
    (iff
      (= ($Multiset.card xs) 0)
      (= xs $Multiset.empty<$S$>))
    (implies
      (not (= ($Multiset.card xs) 0))
      (exists ((x $S$)) (!
        (< 0 ($Multiset.count xs x))
        :pattern (($Multiset.count xs x))
        ))))
	:pattern (($Multiset.card xs))
	)))


;axiom (forall<T> r: T, o: T :: { MultiSet#Singleton(r)[o] }
;  (MultiSet#Singleton(r)[o] == 1 <==> r == o) &&
;  (MultiSet#Singleton(r)[o] == 0 <==> r != o));
(assert (forall ((x $S$) (y $S$)) (!
  (and
    (iff
      (= 1 ($Multiset.count ($Multiset.singleton x) y))
      (= x y))
    (iff
      (= 0 ($Multiset.count ($Multiset.singleton x) y))
      (not (= x y))))
	:pattern (($Multiset.count ($Multiset.singleton x) y))
	)))

;axiom (forall<T> r: T :: { MultiSet#Singleton(r) } MultiSet#Singleton(r) == MultiSet#UnionOne(MultiSet#Empty(), r));
(assert (forall ((x $S$)) (!
  (=
    ($Multiset.singleton x)
    ($Multiset.add $Multiset.empty<$S$> x))
	:pattern (($Multiset.singleton x))
	:pattern (($Multiset.add $Multiset.empty<$S$> x))
	)))

;// pure containment axiom (in the original multiset or is the added element)
;axiom (forall<T> a: MultiSet T, x: T, o: T :: { MultiSet#UnionOne(a,x)[o] }
;  0 < MultiSet#UnionOne(a,x)[o] <==> o == x || 0 < a[o]);
(assert (forall ((xs $Multiset<$S$>) (x $S$) (y $S$)) (!
  (iff
    (< 0 ($Multiset.count ($Multiset.add xs x) y))
    (or
      (= x y)
      (< 0 ($Multiset.count xs y))))
	:pattern (($Multiset.count ($Multiset.add xs x) y))
;	:pattern (($Multiset.count xs y))
	)))

;// union-ing increases count by one
;axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#UnionOne(a, x) }
;  MultiSet#UnionOne(a, x)[x] == a[x] + 1);
(assert (forall ((xs $Multiset<$S$>) (x $S$)) (!
  (=
    ($Multiset.count ($Multiset.add xs x) x)
    (+ ($Multiset.count xs x) 1))
	:pattern (($Multiset.count ($Multiset.add xs x) x))
	)))

;// non-decreasing
;axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#UnionOne(a, x), a[y] }
;  0 < a[y] ==> 0 < MultiSet#UnionOne(a, x)[y]);
(assert (forall ((xs $Multiset<$S$>) (x $S$) (y $S$)) (!
  (implies
    (< 0 ($Multiset.count xs x))
    (< 0 ($Multiset.count ($Multiset.add xs y) x)))
	:pattern (($Multiset.add xs y) ($Multiset.count xs y))
	)))

;// other elements unchanged
;axiom (forall<T> a: MultiSet T, x: T, y: T :: { MultiSet#UnionOne(a, x), a[y] }
;  x != y ==> a[y] == MultiSet#UnionOne(a, x)[y]);
(assert (forall ((xs $Multiset<$S$>) (x $S$) (y $S$)) (!
  (implies
    (not (= x y))
    (< ($Multiset.count ($Multiset.add xs x) y) ($Multiset.count xs y)))
	:pattern (($Multiset.add xs x) ($Multiset.count xs y))
	)))

;axiom (forall<T> a: MultiSet T, x: T :: { MultiSet#Card(MultiSet#UnionOne(a, x)) }
;  MultiSet#Card(MultiSet#UnionOne(a, x)) == MultiSet#Card(a) + 1);
(assert (forall ((xs $Multiset<$S$>) (x $S$)) (!
  (=
    ($Multiset.card ($Multiset.add xs x))
    (+ ($Multiset.card xs) 1))
	:pattern (($Multiset.card ($Multiset.add xs x)))
	)))


;// union-ing is the sum of the contents
;axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Union(a,b)[o] }
;  MultiSet#Union(a,b)[o] == a[o] + b[o]);
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>) (x $S$)) (!
  (=
    ($Multiset.count ($Multiset.union xs ys) x)
    (+ ($Multiset.count xs x) ($Multiset.count ys x)))
	:pattern (($Multiset.count ($Multiset.union xs ys) x))
;	:pattern (($Multiset.count xs x) ($Multiset.count ys x))
	)))

;axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Card(MultiSet#Union(a,b)) }
;  MultiSet#Card(MultiSet#Union(a,b)) == MultiSet#Card(a) + MultiSet#Card(b));
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>)) (!
  (=
    ($Multiset.card ($Multiset.union xs ys))
    (+ ($Multiset.card  xs) ($Multiset.card  ys)))
	:pattern (($Multiset.card ($Multiset.union xs ys)))
;	:pattern (($Multiset.card  xs) ($Multiset.card  ys))
	)))

;// two containment axioms
;axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Union(a, b), a[y] }
;  0 < a[y] ==> 0 < MultiSet#Union(a, b)[y]);
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>) (x $S$)) (!
  (implies
    (< 0 ($Multiset.count xs x))
    (< 0 ($Multiset.count ($Multiset.union xs ys) x)))
	:pattern (($Multiset.union xs ys) ($Multiset.count xs x))
	)))

;axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Union(a, b), b[y] }
;  0 < b[y] ==> 0 < MultiSet#Union(a, b)[y]);
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>) (x $S$)) (!
  (implies
    (< 0 ($Multiset.count ys x))
    (< 0 ($Multiset.count ($Multiset.union xs ys) x)))
	:pattern (($Multiset.union xs ys) ($Multiset.count ys x))
	)))

;// symmetry axiom
;axiom (forall<T> a, b: MultiSet T :: { MultiSet#Union(a, b) }
;  MultiSet#Difference(MultiSet#Union(a, b), a) == b &&
;  MultiSet#Difference(MultiSet#Union(a, b), b) == a);
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>)) (!
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


;axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Intersection(a,b)[o] }
;  MultiSet#Intersection(a,b)[o] == Math#min(a[o],  b[o]));
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>) (x $S$)) (!
  (=
    ($Multiset.count ($Multiset.intersection xs ys) x)
    ($Math.min ($Multiset.count xs x) ($Multiset.count ys x)))
	:pattern (($Multiset.count ($Multiset.intersection xs ys) x))
	)))

;// left and right pseudo-idempotence
;axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(MultiSet#Intersection(a, b), b) }
;  MultiSet#Intersection(MultiSet#Intersection(a, b), b) == MultiSet#Intersection(a, b));
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>)) (!
  (=
    ($Multiset.intersection ($Multiset.intersection xs ys) ys)
    ($Multiset.intersection xs ys))
	:pattern (($Multiset.intersection ($Multiset.intersection xs ys) ys))
	)))

;axiom (forall<T> a, b: MultiSet T :: { MultiSet#Intersection(a, MultiSet#Intersection(a, b)) }
;  MultiSet#Intersection(a, MultiSet#Intersection(a, b)) == MultiSet#Intersection(a, b));
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>)) (!
  (=
    ($Multiset.intersection xs ($Multiset.intersection xs ys))
    ($Multiset.intersection xs ys))
	:pattern (($Multiset.intersection xs ($Multiset.intersection xs ys)))
	)))

;// multiset difference, a - b. clip() makes it positive.
;axiom (forall<T> a: MultiSet T, b: MultiSet T, o: T :: { MultiSet#Difference(a,b)[o] }
;  MultiSet#Difference(a,b)[o] == Math#clip(a[o] - b[o]));
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>) (x $S$)) (!
  (=
    ($Multiset.count ($Multiset.difference xs ys) x)
    ($Math.clip (- ($Multiset.count xs x) ($Multiset.count ys x))))
	:pattern (($Multiset.count ($Multiset.difference xs ys) x))
	)))

;axiom (forall<T> a, b: MultiSet T, y: T :: { MultiSet#Difference(a, b), b[y], a[y] }
;  a[y] <= b[y] ==> MultiSet#Difference(a, b)[y] == 0 );
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>) (x $S$)) (!
  (implies
    (<= ($Multiset.count xs x) ($Multiset.count ys x))
    (=
      ($Multiset.count ($Multiset.difference xs ys) x)
      0))
	:pattern (($Multiset.count xs x) ($Multiset.count ys x) ($Multiset.count ($Multiset.difference xs ys) x))
	)))

;// multiset subset means a must have at most as many of each element as b
;axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Subset(a,b) }
;  MultiSet#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <= b[o]));
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>)) (!
  (iff
    ($Multiset.subset xs ys)
    (forall ((x $S$)) (!
      (<= ($Multiset.count xs x) ($Multiset.count ys x))
	    :pattern (($Multiset.count xs x) ($Multiset.count ys x)))))
	:pattern (($Multiset.subset xs ys))
	)))

;axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
;  MultiSet#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == b[o]));
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>)) (!
  (iff
    ($Multiset.eq xs ys)
    (forall ((x $S$)) (!
      (= ($Multiset.count xs x) ($Multiset.count ys x))
      :pattern (($Multiset.count xs x) ($Multiset.count ys x)))))
	:pattern (($Multiset.eq xs ys))
	)))

;// extensionality axiom for multisets
;axiom(forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Equal(a,b) }
;  MultiSet#Equal(a,b) ==> a == b);
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>)) (!
  (implies
    ($Multiset.eq xs ys)
    (= xs ys))
	:pattern (($Multiset.eq xs ys))
	)))


;axiom (forall<T> a: MultiSet T, b: MultiSet T :: { MultiSet#Disjoint(a,b) }
;  MultiSet#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] == 0 || b[o] == 0));
(assert (forall ((xs $Multiset<$S$>) (ys $Multiset<$S$>)) (!
  (iff
    ($Multiset.disjoint xs ys)
    (forall ((x $S$)) (!
      (or
        (= ($Multiset.count xs x) 0)
        (= ($Multiset.count ys x) 0))
      :pattern (($Multiset.count xs x) ($Multiset.count ys x)))))
	:pattern (($Multiset.disjoint xs ys))
	)))

;// conversion to a multiset. each element in the original set has duplicity 1.
;axiom (forall<T> s: Set T, a: T :: { MultiSet#FromSet(s)[a] }
;  (MultiSet#FromSet(s)[a] == 0 <==> !s[a]) &&
;  (MultiSet#FromSet(s)[a] == 1 <==> s[a]));
(assert (forall ((xs $Set<$S$>) (x $S$)) (!
  (and
    (iff
      (= ($Multiset.count ($Multiset.fromSet xs) x) 0)
      (not ($Set.in x xs)))
    (iff
      (= ($Multiset.count ($Multiset.fromSet xs) x) 1)
      ($Set.in x xs)))
	:pattern (($Multiset.count ($Multiset.fromSet xs) x))
	)))

;axiom (forall<T> s: Set T :: { MultiSet#Card(MultiSet#FromSet(s)) }
;  MultiSet#Card(MultiSet#FromSet(s)) == Set#Card(s));
(assert (forall ((xs $Set<$S$>)) (!
  (=
    ($Multiset.card ($Multiset.fromSet xs))
    ($Set.card xs))
	:pattern (($Multiset.card ($Multiset.fromSet xs)))
	)))

; count is always >= 0
(assert (forall ((s $Multiset<$S$>) (x $S$)) (!
    (>= ($Multiset.count s x) 0)
    :pattern (($Multiset.count s x))
    )))

; Count over a multiset based on a sequence is positive iff the
; underlying sequence contains the counted element.
(assert (forall ((xs $Seq<$S$>) (x $S$)) (!
	(iff
		(> ($Multiset.count ($Multiset.fromSeq xs) x) 0)
		($Seq.in xs x))
	:pattern(($Seq.in xs x))
	:pattern(($Multiset.count ($Multiset.fromSeq xs) x)))))
