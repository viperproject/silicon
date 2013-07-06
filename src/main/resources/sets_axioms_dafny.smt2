; These axioms correspond to Dafny's set axiomatisation from 2013-06-27.

; type Set T = [T]bool;
; $Seq

; axiom (forall<T> s: Set T :: { Set#Card(s) } 0 <= Set#Card(s));
(assert (forall ((xs $Set<$S$>)) (!
	(<= 0 ($Set.card xs))
	:pattern (($Set.card xs))
	)))

; axiom (forall<T> o: T :: { Set#Empty()[o] } !Set#Empty()[o]);
(assert (forall ((x $S$)) (!
	(not ($Set.contains ($Set.empty) x))
	:pattern (($Set.contains ($Set.empty) x))
	)))

; axiom (forall<T> s: Set T :: { Set#Card(s) }
  ; (Set#Card(s) == 0 <==> s == Set#Empty()) &&
  ; (Set#Card(s) != 0 ==> (exists x: T :: s[x])));
(assert (forall ((xs $Set<$S$>)) (!
	(and
		(iff
			(= ($Set.card xs) 0)
			(= xs $Set.empty))
		(iff
			(not (= ($Set.card xs) 0))
			(exists ((x $S$)) (!
				($Set.contains xs x)
				:pattern (($Set.contains xs x))
				))))
	:pattern (($Set.card xs))
	:pattern (($Set.contains xs x))
	)))

; axiom (forall<T> r: T :: { Set#Singleton(r) } Set#Singleton(r)[r]);
(assert (forall ((x $S$)) (!
	($Set.contains ($Set.singleton x) x)
	:pattern (($Set.contains ($Set.singleton x) x))
	)))

; axiom (forall<T> r: T, o: T :: { Set#Singleton(r)[o] } Set#Singleton(r)[o] <==> r == o);
(assert (forall ((x $S$) (y $S$)) (!
	(iff
		($Set.contains ($Set.singleton x) y)
		(= x y))
	:pattern (($Set.contains ($Set.singleton x) y))
	)))

; axiom (forall<T> r: T :: { Set#Card(Set#Singleton(r)) } Set#Card(Set#Singleton(r)) == 1);
(assert (forall ((x $S$)) (!
	(= ($Set.card ($Set.singleton x)) 1)
	:pattern (($Set.card ($Set.singleton x)))
	)))

; axiom (forall<T> a: Set T, x: T, o: T :: { Set#UnionOne(a,x)[o] }
  ; Set#UnionOne(a,x)[o] <==> o == x || a[o]);
(assert (forall ((xs $Set<$S$>) (x $S$) (y $S$)) (!
	(iff
		($Set.contains ($Set.add xs x) y)
		(or
			(= x y)
			($Set.contains xs y)))
	:pattern (($Set.contains ($Set.add xs x) y))
	)))

; axiom (forall<T> a: Set T, x: T :: { Set#UnionOne(a, x) }
  ; Set#UnionOne(a, x)[x]);
(assert (forall ((xs $Set<$S$>) (x $S$)) (!
	($Set.contains ($Set.add xs x) x)
	:pattern (($Set.contains ($Set.add xs x) x))
	)))

; axiom (forall<T> a: Set T, x: T, y: T :: { Set#UnionOne(a, x), a[y] }
  ; a[y] ==> Set#UnionOne(a, x)[y]);
(assert (forall ((xs $Set<$S$>) (x $S$) (y $S$)) (!
	(implies
		($Set.contains xs y)
		($Set.contains ($Set.add xs x) y))
	:pattern (($Set.contains xs y) ($Set.contains ($Set.add xs x) y))
	)))

; axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
  ; a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a));
(assert (forall ((xs $Set<$S$>) (x $S$)) (!
	(implies
		($Set.contains xs x)
		(= ($Set.card ($Set.add xs x)) ($Set.card xs)))
	:pattern (($Set.card ($Set.add xs x)))
	)))

; axiom (forall<T> a: Set T, x: T :: { Set#Card(Set#UnionOne(a, x)) }
  ; !a[x] ==> Set#Card(Set#UnionOne(a, x)) == Set#Card(a) + 1);
(assert (forall ((xs $Set<$S$>) (x $S$)) (!
	(implies
		(not ($Set.contains xs x))
		(= ($Set.card ($Set.add xs x)) (+ ($Set.card xs) 1)))
	:pattern (($Set.card ($Set.add xs x)))
	)))

; axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Union(a,b)[o] }
  ; Set#Union(a,b)[o] <==> a[o] || b[o]);
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>) (x $S$)) (!
	(iff
		($Set.contains ($Set.union xs ys) x)
		(or
			($Set.contains xs x)
			($Set.contains ys x)))
	:pattern (($Set.contains ($Set.union xs ys) x))
	)))

; axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), a[y] }
  ; a[y] ==> Set#Union(a, b)[y]);
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>) (x $S$)) (!
	(implies
		($Set.contains xs x)
		($Set.contains ($Set.union xs ys) x))
	:pattern (($Set.contains ($Set.union xs ys) x) ($Set.contains xs x))
	)))

; axiom (forall<T> a, b: Set T, y: T :: { Set#Union(a, b), b[y] }
  ; b[y] ==> Set#Union(a, b)[y]);
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>) (x $S$)) (!
	(implies
		($Set.contains ys x)
		($Set.contains ($Set.union xs ys) x))
	:pattern (($Set.contains ($Set.union xs ys) x) ($Set.contains ys x))
	)))

; axiom (forall<T> a, b: Set T :: { Set#Union(a, b) }
  ; Set#Disjoint(a, b) ==>
    ; Set#Difference(Set#Union(a, b), a) == b &&
    ; Set#Difference(Set#Union(a, b), b) == a);
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>)) (!
	(implies
		($Set.disjoint xs ys)
		(and
			(= ($Set.difference ($Set.union xs ys) xs) ys)
			(= ($Set.difference ($Set.union xs ys) ys) xs)))
	:pattern (($Set.union xs ys))
	)))
; // Follows from the general union axiom, but might be still worth including, because disjoint union is a common case:
; // axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }
  ; // Set#Disjoint(a, b) ==>
    ; // Set#Card(Set#Union(a, b)) == Set#Card(a) + Set#Card(b));

; axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Intersection(a,b)[o] }
  ; Set#Intersection(a,b)[o] <==> a[o] && b[o]);
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>) (x $S$)) (!
	(implies
		($Set.contains ($Set.intersection xs ys) x)
		(and
			($Set.contains xs x)
			($Set.contains ys x)))
	:pattern (($Set.contains ($Set.intersection xs ys) x))
	)))

; axiom (forall<T> a, b: Set T :: { Set#Union(Set#Union(a, b), b) }
  ; Set#Union(Set#Union(a, b), b) == Set#Union(a, b));
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>)) (!
	(=
		($Set.union ($Set.union xs ys) ys)
		($Set.union xs ys))
	:pattern (($Set.union ($Set.union xs ys) ys))
	)))
	
; axiom (forall<T> a, b: Set T :: { Set#Union(a, Set#Union(a, b)) }
  ; Set#Union(a, Set#Union(a, b)) == Set#Union(a, b));
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>)) (!
	(=
		($Set.union xs ($Set.union xs ys))
		($Set.union xs ys))
	:pattern (($Set.union xs ($Set.union xs ys)))
	)))
	
; axiom (forall<T> a, b: Set T :: { Set#Intersection(Set#Intersection(a, b), b) }
  ; Set#Intersection(Set#Intersection(a, b), b) == Set#Intersection(a, b));
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>)) (!
	(=
		($Set.intersection ($Set.intersection xs ys) ys)
		($Set.intersection xs ys))
	:pattern (($Set.intersection ($Set.intersection xs ys) ys))
	)))
	
; axiom (forall<T> a, b: Set T :: { Set#Intersection(a, Set#Intersection(a, b)) }
  ; Set#Intersection(a, Set#Intersection(a, b)) == Set#Intersection(a, b));
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>)) (!
	(=
		($Set.intersection xs ($Set.intersection xs ys))
		($Set.intersection xs ys))
	:pattern (($Set.intersection xs ($Set.intersection xs ys)))
	)))

; axiom (forall<T> a, b: Set T :: { Set#Card(Set#Union(a, b)) }
;                                 { Set#Card(Set#Intersection(a, b)) }
;     Set#Card(Set#Union(a, b)) + Set#Card(Set#Intersection(a, b))
;	 == Set#Card(a) + Set#Card(b));
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>)) (!
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

; axiom (forall<T> a: Set T, b: Set T, o: T :: { Set#Difference(a,b)[o] }
  ; Set#Difference(a,b)[o] <==> a[o] && !b[o]);
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>) (x $S$)) (!
	(iff
		($Set.contains ($Set.difference xs ys) x)
		(and
			($Set.contains xs x)
			(not ($Set.contains ys x))))
	:pattern (($Set.contains ($Set.difference xs ys) x))
	)))
	
; axiom (forall<T> a, b: Set T, y: T :: { Set#Difference(a, b), b[y] }
  ; b[y] ==> !Set#Difference(a, b)[y] );
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>) (x $S$)) (!
	(implies
		($Set.contains ys x)
		(not ($Set.contains ($Set.difference xs ys) x)))
	:pattern (($Set.contains ($Set.difference xs ys) x) ($Set.contains ys x))
	)))
	

; axiom(forall<T> a: Set T, b: Set T :: { Set#Subset(a,b) }
  ; Set#Subset(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] ==> b[o]));
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>)) (!
	(iff
		($Set.subset xs ys)
		(forall ((x $S$)) (!
			(implies
				($Set.contains xs x)
				($Set.contains ys x))
			:pattern (($Set.contains xs x))
			:pattern (($Set.contains ys x))
			)))
	:pattern (($Set.subset xs ys))
	)))
; //axiom(forall<T> a: Set T, b: Set T ::
; // { Set#Subset(a,b), Set#Card(a), Set#Card(b) }  // very restrictive trigger
; //  Set#Subset(a,b) ==> Set#Card(a) <= Set#Card(b));

; axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }
  ; Set#Equal(a,b) <==> (forall o: T :: {a[o]} {b[o]} a[o] <==> b[o]));
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>)) (!
	(iff
		($Set.eq xs ys)
		(forall ((x $S$)) (!
			(iff
				($Set.contains xs x)
				($Set.contains ys x))
			:pattern (($Set.contains xs x))
			:pattern (($Set.contains ys x))
			)))
	:pattern (($Set.eq xs ys))
	)))
	
; axiom(forall<T> a: Set T, b: Set T :: { Set#Equal(a,b) }  // extensionality axiom for sets
  ; Set#Equal(a,b) ==> a == b);
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>)) (!
	(implies
		($Set.eq xs ys)
		(= xs ys))
	:pattern (($Set.eq xs ys))
	)))

; axiom (forall<T> a: Set T, b: Set T :: { Set#Disjoint(a,b) }
  ; Set#Disjoint(a,b) <==> (forall o: T :: {a[o]} {b[o]} !a[o] || !b[o]));
(assert (forall ((xs $Set<$S$>) (ys $Set<$S$>)) (!
	(iff
		($Set.disjoint xs ys)
		(forall ((x $S$)) (!
			(or
				(not ($Set.contains xs x))
				(not ($Set.contains ys x)))
			:pattern (($Set.contains xs x))
			:pattern (($Set.contains ys x))
			)))
	:pattern (($Set.disjoint xs ys))
	)))