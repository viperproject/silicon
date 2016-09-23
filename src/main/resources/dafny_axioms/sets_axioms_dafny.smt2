; These axioms are derived from the corresponding axioms of the prelude of
; Microsoft's Dafny tool by translating them from Boogie to SMT-LIB. Visit
; http://dafny.codeplex.com for more information about the Dafny verifier.
;
; A snapshot of the corresponding DafnyPrelude.bpl file including the date
; of the version and its copyright notices can be found in this directory.
;
; This file is subject to the terms of the Microsoft Public License
; (Ms-PL). A copy of the Ms-PL is provided in this directory (LICENCE.TXT)



(assert (forall ((s $Set<$S$>)) (!
  (<= 0 ($Set.card s))
  :pattern (($Set.card s))
  )))

(assert (forall ((o $S$)) (!
  (not ($Set.in o $Set.empty<$S$>))
  :pattern (($Set.in o $Set.empty<$S$>))
  )))

(assert (forall ((s $Set<$S$>)) (!
  (and
    (iff
      (= ($Set.card s) 0)
      (= s $Set.empty<$S$>))
    (implies
      (not (= ($Set.card s) 0))
      (exists ((x $S$)) (!
        ($Set.in x s)
        :pattern (($Set.in x s))
      ))))
  :pattern (($Set.card s))
  )))

(assert (forall ((r $S$)) (!
  ($Set.in r ($Set.singleton r))
  :pattern (($Set.singleton r)) ; Dafny
;  :pattern (($Set.in r ($Set.singleton r)))
  )))

(assert (forall ((r $S$) (o $S$)) (!
  (iff
    ($Set.in o ($Set.singleton r))
    (= r o))
  :pattern (($Set.in o ($Set.singleton r)))
  )))

(assert (forall ((r $S$)) (!
  (= ($Set.card ($Set.singleton r)) 1)
  :pattern (($Set.card ($Set.singleton r)))
  )))

(assert (forall ((a $Set<$S$>) (x $S$) (o $S$)) (!
  (iff
    ($Set.in o ($Set.unionone a x))
    (or
      (= o x)
      ($Set.in o a)))
  :pattern (($Set.in o ($Set.unionone a x)))
  )))

(assert (forall ((a $Set<$S$>) (x $S$)) (!
  ($Set.in x ($Set.unionone a x))
  :pattern (($Set.unionone a x)) ; Dafny
;  :pattern (($Set.in x ($Set.unionone a x)))
  )))

(assert (forall ((a $Set<$S$>) (x $S$) (y $S$)) (!
  (=>
    ($Set.in y a)
    ($Set.in y ($Set.unionone a x)))
  :pattern (($Set.in y a) ($Set.unionone a x)) ; Dafny
;  :pattern (($Set.in y a) ($Set.in y ($Set.unionone a x)))
  )))

(assert (forall ((a $Set<$S$>) (x $S$)) (!
  (=>
    ($Set.in x a)
    (= ($Set.card ($Set.unionone a x)) ($Set.card a)))
  :pattern (($Set.card ($Set.unionone a x)))
  )))

(assert (forall ((a $Set<$S$>) (x $S$)) (!
  (=>
    (not ($Set.in x a))
    (= ($Set.card ($Set.unionone a x)) (+ ($Set.card a) 1)))
  :pattern (($Set.card ($Set.unionone a x)))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>) (o $S$)) (!
  (iff
    ($Set.in o ($Set.union a b))
    (or
      ($Set.in o a)
      ($Set.in o b)))
  :pattern (($Set.in o ($Set.union a b)))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>) (y $S$)) (!
  (=>
    ($Set.in y a)
    ($Set.in y ($Set.union a b)))
  :pattern (($Set.union a b) ($Set.in y a)) ; Dafny
;  :pattern (($Set.in y ($Set.union a b)) ($Set.in y a))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>) (y $S$)) (!
  (=>
    ($Set.in y b)
    ($Set.in y ($Set.union a b)))
  :pattern (($Set.union a b) ($Set.in y b)) ; Dafny
;  :pattern (($Set.in y ($Set.union a b)) ($Set.in y b))
  )))

; MS: Commented because the trigger looks too weak
; (assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  ; (=>
    ; ($Set.disjoint a b)
    ; (and
      ; (= ($Set.difference ($Set.union a b) a) b)
      ; (= ($Set.difference ($Set.union a b) b) a)))
  ; :pattern (($Set.union a b))
  ; )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>) (o $S$)) (!
  (iff
    ($Set.in o ($Set.intersection a b))
    (and
      ($Set.in o a)
      ($Set.in o b)))
  :pattern (($Set.in o ($Set.intersection a b)))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  (=
    ($Set.union ($Set.union a b) b)
    ($Set.union a b))
  :pattern (($Set.union ($Set.union a b) b))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  (=
    ($Set.union a ($Set.union a b))
    ($Set.union a b))
    :pattern (($Set.union a ($Set.union a b)))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  (=
    ($Set.intersection ($Set.intersection a b) b)
    ($Set.intersection a b))
  :pattern (($Set.intersection ($Set.intersection a b) b))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  (=
    ($Set.intersection a ($Set.intersection a b))
    ($Set.intersection a b))
  :pattern (($Set.intersection a ($Set.intersection a b)))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  (=
    (+
      ($Set.card ($Set.union a b))
      ($Set.card ($Set.intersection a b)))
    (+
      ($Set.card a)
      ($Set.card b)))
  :pattern (($Set.card ($Set.union a b)))
  :pattern (($Set.card ($Set.intersection a b)))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>) (o $S$)) (!
  (iff
    ($Set.in o ($Set.difference a b))
    (and
      ($Set.in o a)
      (not ($Set.in o b))))
  :pattern (($Set.in o ($Set.difference a b)))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>) (y $S$)) (!
  (=>
    ($Set.in y b)
    (not ($Set.in y ($Set.difference a b))))
  :pattern (($Set.difference a b) ($Set.in y b)) ; Dafny
;  :pattern (($Set.in y ($Set.difference a b)) ($Set.in y b))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  (iff
    ($Set.subset a b)
    (forall ((o $S$)) (!
      (=>
        ($Set.in o a)
        ($Set.in o b))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
    )))
  :pattern (($Set.subset a b))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  (iff
    ($Set.equal a b)
    (forall ((o $S$)) (!
      (iff
        ($Set.in o a)
        ($Set.in o b))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
      :qid |$Set<$S$>.ext-inner|
      )))
  :pattern (($Set.equal a b))
  :qid |$Set<$S$>.ext-outer|
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  (=>
    ($Set.equal a b)
    (= a b))
  :pattern (($Set.equal a b))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  (iff
    ($Set.disjoint a b)
    (forall ((o $S$)) (!
      (or
        (not ($Set.in o a))
        (not ($Set.in o b)))
      :pattern (($Set.in o a))
      :pattern (($Set.in o b))
      )))
  :pattern (($Set.disjoint a b))
  )))

(assert (forall ((a $Set<$S$>) (b $Set<$S$>)) (!
  (and
    (=
      (+
        (+
          ($Set.card ($Set.difference a b))
          ($Set.card ($Set.difference b a)))
        ($Set.card ($Set.intersection a b)))
      ($Set.card ($Set.union a b)))
    (=
      ($Set.card ($Set.difference a b))
      (-
        ($Set.card a)
        ($Set.card ($Set.intersection a b)))))
  :pattern (($Set.card ($Set.difference a b))) ; Dafny
;  :pattern (($Set.card ($Set.difference a b)) ($Set.card ($Set.intersection a b)))
  )))
