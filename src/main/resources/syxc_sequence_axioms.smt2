; MHS 2011-09-07
; 	These are the sequence axioms I created in the course of my Master's thesis.
; 	They seem to perform all right.

(declare-fun $Seq.nil () Int)
(declare-fun $Seq.elem (Int) Int)
(declare-fun $Seq.rng (Int Int) Int)
(declare-fun $Seq.len (Int) Int)
(declare-fun $Seq.con (Int Int) Int)
(declare-fun $Seq.at (Int Int) Int)
(declare-fun $Seq.seg (Int Int Int) Int)
(declare-fun $Seq.in (Int Int) Bool)
(declare-fun $Seq.eq (Int Int) Bool)

; Equality axioms

(assert (forall ((xs Int) (ys Int)) (!
	(iff
		($Seq.eq xs ys)
		(and
			(= ($Seq.len xs) ($Seq.len ys))
			(forall ((i Int))
				(implies
					(and (<= 0 i) (< i ($Seq.len xs)))
					(= ($Seq.at xs i) ($Seq.at ys i)))
				; :pat {($Seq.at xs i) ($Seq.at ys i)})))
				; Pattern appears to be problematic, the following fails when used:
				;    ensures zs1 == zs2 ==> forall i in [0..|zs1|] :: zs1[i] in zs2
				)))
	:pattern (($Seq.eq xs ys)))))
	; ))

; ; Additional equality axiom. Currently not required by any use case, the above appears to be
; ; sufficient
; (assert (forall (xs Int) (ys Int)
	; (implies
		; ($Seq.eq xs ys)
		; (and
			; (= ($Seq.len xs) ($Seq.len ys))
			; (forall (i Int)
				; (implies
					; (and (<= 0 i) (< i ($Seq.len xs)))
					; (and
						; ($Seq.in ($Seq.at xs i) ys)
						; ($Seq.in ($Seq.at ys i) xs)))
				; ; :pat {($Seq.in ($Seq.at xs i) ys) ($Seq.in ($Seq.at ys i) xs)})))
					; ; Patterns appears to be problematic,  the following fails when used:
					; ;    ensures zs1 == zs2 ==> forall i in [0..|zs1|] :: zs1[i] in zs2
				; ; )))
	; :pat {($Seq.eq xs ys)}))
	; ; ))

; Length axioms

; |[]| = 0
(assert (= ($Seq.len $Seq.nil) 0))

; ∀ xs • |xs| ≥ 0
(assert (forall ((xs Int)) (!
	(>= ($Seq.len xs) 0)
	:pattern (($Seq.len xs)))))
	; ))

; ∀ x • |(x)| = 1
(assert (forall ((x Int)) (!
	(= ($Seq.len ($Seq.elem x)) 1)
	:pattern (($Seq.len ($Seq.elem x))))))
	; ))

; ∀ xs, ys • |xs ++ ys| = |xs| + |ys|
(assert (forall ((xs Int) (ys Int)) (!
	(= ($Seq.len ($Seq.con xs ys)) (+ ($Seq.len xs) ($Seq.len ys)))
	; :pat {($Seq.len ($Seq.con xs ys))}))
		; Using the pattern makes e.g. assert [3..6] == [3,4,5] fail.
	:pattern (($Seq.con xs ys)))))
	; ))

; ; ∀ j > i + 1 • |[i..j]| = abs(j - i)
(assert (forall ((i Int) (j Int)) (!
		(= ($Seq.len ($Seq.rng i j)) ($Math.abs (- j i)))
	:pattern (($Seq.len ($Seq.rng i j))))))

; ∀ xs, i, j • |xs[i..j]| = j - i
(assert (forall ((xs Int) (i Int) (j Int)) (!
	(implies
		(and (< i j) (and (>= i 0) (<= j ($Seq.len xs))))
		(= ($Seq.len ($Seq.seg xs i j)) (- j i)))
	:pattern (($Seq.len ($Seq.seg xs i j))))))
	; ))

; ; Concat axioms

; ∀ xs • xs ++ [] == xs
(assert (forall ((xs Int)) (!
	(= ($Seq.con xs $Seq.nil) xs)
	:pattern (($Seq.con xs $Seq.nil)))))
	; ))

; ∀ xs • [] ++ xs == xs
(assert (forall ((xs Int)) (!
	(= ($Seq.con $Seq.nil xs) xs)
	:pattern (($Seq.con $Seq.nil xs)))))
	; ))

; Using the axiom
;   ∀ xs • [] ++ xs == xs ++ []
; instead of
;   ∀ xs • [] ++ xs == xs
; causes Z3 to instantiate more quantifiers, hence I picked the second.

; At axioms

; ∀ x • (x)[0] == x
(assert (forall ((x Int)) (!
	(= ($Seq.at ($Seq.elem x) 0) x)
	:pattern (($Seq.at ($Seq.elem x) 0)))))
	; ))

; ∀ xs, 0 ≤ i < |xs| • [xs[i]] = xs[i..i+1]
(assert (forall ((xs Int) (i Int)) (!
	(implies
		(and (<= 0 i) (< i ($Seq.len xs)))
		(= ($Seq.elem ($Seq.at xs i)) ($Seq.seg xs i (+ i 1))))
	:pattern (($Seq.elem ($Seq.at xs i))))))
	; ))

; ∀ xs, ys, n •
;		   (n < |xs| ⇒ (xs ++ ys)[n] = xs[n])
;   ∧ (n ≥ |xs| ⇒ (xs ++ ys)[n] = ys[n - |xs|])
(assert (forall ((xs Int) (ys Int) (n Int)) (!
	(implies
		(and (>= n 0) (<= n ($Seq.len ($Seq.con xs ys))))
		(and
			(implies (< n ($Seq.len xs))
				(= ($Seq.at ($Seq.con xs ys) n) ($Seq.at xs n)))
			(implies (>= n ($Seq.len xs))
				(= ($Seq.at ($Seq.con xs ys) n) ($Seq.at ys (- n ($Seq.len xs)))))))
	:pattern (($Seq.at ($Seq.con xs ys) n)))))
	; ))

; ∀ 0 ≤ k < j - i • [i..j][k] = i + k
(assert (forall ((i Int) (j Int) (k Int)) (!
	(implies
		(and (<= 0 k) (< k (- j i)))
		(= ($Seq.at ($Seq.rng i j) k) (+ i k)))
	:pattern (($Seq.at ($Seq.rng i j) k)))))
	; ))

; Segment axioms

; ∀ xs, n • xs[n..n] = []
(assert (forall ((xs Int) (n Int)) (!
	(implies
		(and (>= n 0) (<= n ($Seq.len xs)))
		(= ($Seq.seg xs n n) $Seq.nil))
	:pattern (($Seq.seg xs n n)))))
	; ))

; ∀ xs, ys, i, j •
;		   (j ≤ |xs| ⇒ (xs ++ ys)[i..j] = xs[i..j])
;   ∧ (i ≥ |xs| ⇒ (xs ++ ys)[i..j] = ys[i-|xs|..j-|xs|])
(assert (forall ((xs Int) (ys Int) (i Int) (j Int)) (!
	(let ((lxs ($Seq.len xs)))
	(implies
		(and (<= 0 i) (and (< i j) (<= j ($Seq.len ($Seq.con xs ys)))))
		(and
			(implies (<= j lxs)
				(= ($Seq.seg ($Seq.con xs ys) i j) ($Seq.seg xs i j)))
			(implies (>= i lxs)
				(=
					($Seq.seg ($Seq.con xs ys) i j)
					($Seq.seg ys (- i lxs) (- j lxs)))))))
	:pattern (($Seq.seg ($Seq.con xs ys) i j)))))
	; ))

; ∀ xs • xs[0..|xs|]	 = xs
(assert (forall ((xs Int)) (!
	(= ($Seq.seg xs 0 ($Seq.len xs)) xs)
	; /* Patterns let some assertions fail, e.g. */
	;   assert (xs ++ ys)[|xs|..] == ys
	; :pat {($Seq.len xs) ($Seq.seg xs 0 ($Seq.len xs))}))
	; :pat {($Seq.seg xs 0 ($Seq.len xs))}))
	; /* This seems to work */
	:weight 25
	:pattern (($Seq.len xs)))))
	; /* No pattern (or {($Seq.len xs)} without any weight makes verification
	;  * of Sieve.chalice (from the Chalice suite) very slow, but only if verified
	;  * in one run. To be precise, if NumberStream, Sieve.Counter and
	;  * Sieve.Filter are verified together. Otherwise the verification succeeds
	;  * immediately.
	;  */
	; ))

; ∀ xs, x, j • ([x] ++ xs)[0..j] = [x] ++ xs[0..j-1]
(assert (forall ((xs Int) (x Int) (j Int)) (!
	(implies
		(and (> j 0) (<= j (+ ($Seq.len xs) 1)))
		(=
			($Seq.seg ($Seq.con ($Seq.elem x) xs) 0 j)
			($Seq.con ($Seq.elem x) ($Seq.seg xs 0 (- j 1)))))
	:pattern (($Seq.seg ($Seq.con ($Seq.elem x) xs) 0 j)))))
	; ))

; ∀ xs, i, j, k • xs[i..j] ++ xs[j..k] = xs[i..k]
(assert (forall ((xs Int) (i Int) (j Int) (k Int)) (!
	(implies
		(and (<= 0 i) (and (< i j) (and (< j k) (<= k ($Seq.len xs)))))
		(=
			($Seq.con ($Seq.seg xs i j) ($Seq.seg xs j k))
			($Seq.seg xs i k)))
		:pattern (($Seq.con ($Seq.seg xs i j) ($Seq.seg xs j k))))))
		; ))

; In axioms

; ∀ x • x in [x]
(assert (forall ((x Int)) (!
	($Seq.in x ($Seq.elem x))
	:pattern (($Seq.in x ($Seq.elem x))))))
	; ))

; ∀ x, xs • x in xs ⇔ ∃ 0 ≤ i < |xs| • xs[i] = x
(assert (forall ((x Int) (xs Int)) (!
	(iff
		($Seq.in x xs)
    (exists ((i Int)) (!
			(and (<= 0 i) (and (< i ($Seq.len xs)) (= ($Seq.at xs i) x)))
			:pattern (($Seq.at xs i)))))
			; ))
	:pattern (($Seq.in x xs)))))
	; ))

; ∀ • xs, xs, ys • x in xs ++ ys ⇔ x in xs ∨ x in ys
(assert (forall ((x Int) (xs Int) (ys Int)) (!
	(iff
		($Seq.in x ($Seq.con xs ys))
		(or ($Seq.in x xs) ($Seq.in x ys)))
	:pattern (($Seq.in x ($Seq.con xs ys))))))
	; ))

; ∀ x, xs, 0 ≤ i < j ≤ |xs| • x in xs[i..j] ⇔ ∃ i ≤ k < j • xs[k] = x
(assert (forall ((x Int) (xs Int) (i Int) (j Int)) (!
	(implies
		(and (<= 0 i) (and (< i j) (<= j ($Seq.len xs))))
		(iff
			($Seq.in x ($Seq.seg xs i j))
			(exists ((k Int)) (!
				(and (and (<= i k) (< k j)) (= ($Seq.at xs k) x))
				:pattern (($Seq.at xs k))))))
				; )))
	:pattern (($Seq.in x ($Seq.seg xs i j))))))
	; ))

; Range axioms

; ∀ i • [i..i] = []
(assert (forall ((i Int)) (!
	(= ($Seq.rng i i) $Seq.nil)
	:pattern (($Seq.rng i i)))))
	; ))

; ∀ i • [i..i+1] = [i]
(assert (forall ((i Int)) (!
	(= ($Seq.rng i (+ i 1)) ($Seq.elem i))
	:pattern (($Seq.rng i (+ i 1))))))
	; ))

; ∀ x, i, j • x in [i..j] ⇔ i ≤ x < j ∨ j < x ≤ i
(assert (forall ((x Int) (i Int) (j Int)) (!
	(iff
		($Seq.in x ($Seq.rng i j))
		(or
			(and (<= i x) (< x j))
			(and (< j x) (<= x i))))
	:pattern (($Seq.in x ($Seq.rng i j))))))

; ∀ i, j, r, s • [i..j][r..s] = [i+r..i+s]
(assert (forall ((i Int) (j Int) (r Int) (s Int)) (!
	(implies
		(and (<= i j) (and (<= 0 r) (and (< r s) (<= s (- j i)))))
		(= ($Seq.seg ($Seq.rng i j) r s) ($Seq.rng (+ i r) (+ i s))))
	:pattern (($Seq.seg ($Seq.rng i j) r s)))))
	; ))