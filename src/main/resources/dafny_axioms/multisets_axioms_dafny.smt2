; These axioms are derived from the corresponding axioms of the prelude of
; Microsoft's Dafny tool by translating them from Boogie to SMT-LIB. Visit
; http://dafny.codeplex.com for more information about the Dafny verifier.
;
; A snapshot of the corresponding DafnyPrelude.bpl file including the date
; of the version and its copyright notices can be found in this directory.
;
; This file is subject to the terms of the Microsoft Public License
; (Ms-PL). A copy of the Ms-PL is provided in this directory (LICENCE.TXT)



(assert (forall ((ms $Multiset<$S$>) (bx $S$)) (!
  (and
    (<= 0 ($Multiset.count ms bx))
    (<= ($Multiset.count ms bx) ($Multiset.card ms)))
  :pattern (($Multiset.count ms bx))
  )))

(assert (forall ((s $Multiset<$S$>) ) (! (<= 0 ($Multiset.card s))
  :pattern ( ($Multiset.card s))
  )))
(assert (forall ((o $S$) ) (! (= ($Multiset.count $Multiset.empty<$S$> o) 0)
  :pattern ( ($Multiset.count $Multiset.empty<$S$> o))
  )))
(assert (forall ((s $Multiset<$S$>) ) (! (and
  (=> (= ($Multiset.card s) 0) (= s $Multiset.empty<$S$>))
  (=> (= s $Multiset.empty<$S$>) (= ($Multiset.card s) 0))
  (=> (not (= ($Multiset.card s) 0)) (exists ((x $S$) ) (! (< 0 ($Multiset.count s x))
  ))))
  :pattern ( ($Multiset.card s))
  )))
(assert (forall ((r $S$) (o $S$) ) (! (and
  (=> (= ($Multiset.count ($Multiset.singleton r) o) 1) (= r o))
  (=> (= r o) (= ($Multiset.count ($Multiset.singleton r) o) 1))
  (=> (= ($Multiset.count ($Multiset.singleton r) o) 0) (not (= r o)))
  (=> (not (= r o)) (= ($Multiset.count ($Multiset.singleton r) o) 0)))
  :pattern ( ($Multiset.count ($Multiset.singleton r) o))
  )))
(assert (forall ((r $S$) ) (! (= ($Multiset.singleton r) ($Multiset.unionone $Multiset.empty<$S$> r))
  :pattern ( ($Multiset.singleton r))
  )))
(assert (forall ((a $Multiset<$S$>) (x $S$) (o $S$) ) (! (= ($Multiset.count ($Multiset.unionone a x) o) (ite (= x o) (+ ($Multiset.count a o) 1) ($Multiset.count a o)))
  :pattern ( ($Multiset.count ($Multiset.unionone a x) o))
  )))
(assert (forall ((a $Multiset<$S$>) (x $S$) ) (! (= ($Multiset.card ($Multiset.unionone a x)) (+ ($Multiset.card a) 1))
  :pattern ( ($Multiset.card ($Multiset.unionone a x)))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) (o $S$) ) (! (= ($Multiset.count ($Multiset.union a b) o) (+ ($Multiset.count a o) ($Multiset.count b o)))
  :pattern ( ($Multiset.count ($Multiset.union a b) o))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) ) (! (= ($Multiset.card ($Multiset.union a b)) (+ ($Multiset.card a) ($Multiset.card b)))
  :pattern ( ($Multiset.card ($Multiset.union a b)))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) (o $S$) ) (! (= ($Multiset.count ($Multiset.intersection a b) o) ($Math.min ($Multiset.count a o) ($Multiset.count b o)))
  :pattern ( ($Multiset.count ($Multiset.intersection a b) o))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) ) (! (= ($Multiset.intersection ($Multiset.intersection a b) b) ($Multiset.intersection a b))
  :pattern ( ($Multiset.intersection ($Multiset.intersection a b) b))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) ) (! (= ($Multiset.intersection a ($Multiset.intersection a b)) ($Multiset.intersection a b))
  :pattern ( ($Multiset.intersection a ($Multiset.intersection a b)))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) (o $S$) ) (! (= ($Multiset.count ($Multiset.difference a b) o) ($Math.clip (- ($Multiset.count a o) ($Multiset.count b o))))
  :pattern ( ($Multiset.count ($Multiset.difference a b) o))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) (y $S$) ) (! (=> (<= ($Multiset.count a y) ($Multiset.count b y)) (= ($Multiset.count ($Multiset.difference a b) y) 0))
  :pattern ( ($Multiset.difference a b) ($Multiset.count b y) ($Multiset.count a y))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) ) (! (and
  (= (+ (+ ($Multiset.card ($Multiset.difference a b)) ($Multiset.card ($Multiset.difference b a))) (* 2 ($Multiset.card ($Multiset.intersection a b)))) ($Multiset.card ($Multiset.union a b)))
  (= ($Multiset.card ($Multiset.difference a b)) (- ($Multiset.card a) ($Multiset.card ($Multiset.intersection a b)))))
  :pattern ( ($Multiset.card ($Multiset.difference a b)))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) ) (! (and
  (=> ($Multiset.subset a b) (forall ((o $S$) ) (! (<= ($Multiset.count a o) ($Multiset.count b o))
  :pattern ( ($Multiset.count a o))
  :pattern ( ($Multiset.count b o))
  )))
  (=> (forall ((o $S$) ) (! (<= ($Multiset.count a o) ($Multiset.count b o))
  :pattern ( ($Multiset.count a o))
  :pattern ( ($Multiset.count b o))
  )) ($Multiset.subset a b)))
  :pattern ( ($Multiset.subset a b))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) ) (! (and
  (=> ($Multiset.equal a b) (forall ((o $S$) ) (! (= ($Multiset.count a o) ($Multiset.count b o))
  :pattern ( ($Multiset.count a o))
  :pattern ( ($Multiset.count b o))
  )))
  (=> (forall ((o $S$) ) (! (= ($Multiset.count a o) ($Multiset.count b o))
  :pattern ( ($Multiset.count a o))
  :pattern ( ($Multiset.count b o))
  )) ($Multiset.equal a b)))
  :pattern ( ($Multiset.equal a b))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) ) (! (=> ($Multiset.equal a b) (= a b))
  :pattern ( ($Multiset.equal a b))
  )))
(assert (forall ((a $Multiset<$S$>) (b $Multiset<$S$>) ) (! (and
  (=> ($Multiset.disjoint a b) (forall ((o $S$) ) (! (or
  (= ($Multiset.count a o) 0)
  (= ($Multiset.count b o) 0))
  :pattern ( ($Multiset.count a o))
  :pattern ( ($Multiset.count b o))
  )))
  (=> (forall ((o $S$) ) (! (or
  (= ($Multiset.count a o) 0)
  (= ($Multiset.count b o) 0))
  :pattern ( ($Multiset.count a o))
  :pattern ( ($Multiset.count b o))
  )) ($Multiset.disjoint a b)))
  :pattern ( ($Multiset.disjoint a b))
  )))
