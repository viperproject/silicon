; Axioms specific to integer sequences

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

; ; axiom (forall min: int, max: int :: { Seq#Length(Seq#Range(min, max)) } (min < max ==> Seq#Length(Seq#Range(min, max)) == max-min) && (max <= min ==> Seq#Length(Seq#Range(min, max)) == 0));
(assert (forall ((i Int) (j Int)) (!
	; (and
		(implies
			(< i j)
			(= ($Seq.len ($Seq.rng i j)) (- j i)))
		; (implies
			; (<= j i)
			; (= ($Seq.len ($Seq.rng i j)) 0)))
	:pattern (($Seq.len ($Seq.rng i j)))
	)))

; ; axiom (forall min: int, max: int, j: int :: { Seq#Index(Seq#Range(min, max), j) } 0<=j && j<max-min ==> Seq#Index(Seq#Range(min, max), j) == min + j);
; 
(assert (forall ((i Int) (j Int) (k Int)) (!
	(implies
		(and
			(<= 0 k)
			(< k (- j i)))
		(= ($Seq.at ($Seq.rng i j) k) (+ i k)))
	:pattern (($Seq.at ($Seq.rng i j) k))
	)))

;(assert (forall ((i Int) (start Int) (end Int)) (!
;    (implies
;        ($Seq.in ($Seq.rng start end) i)
;        (and (>= i start) (< i end))
;    )
;    :pattern (($Seq.in ($Seq.rng start end) i))
;    )))

(declare-fun $Seq.rngP (Int Int) $Seq<Int>)

(assert (forall ((start Int) (end Int)) (!
    (= ($Seq.rng start end) ($Seq.rngP start end))
    :pattern (($Seq.rng start end))
    )))

(assert (forall ((start Int) (end Int) (k Int)) (!
    (implies
       (and
          (<= start k)
           (<= k end)
       )
       (=
           ($Seq.rngP start end)
           ($Seq.con ($Seq.rngP start k) ($Seq.rngP k end))
       )
     )
    :pattern (($Seq.rng start k) ($Seq.rng k end))
    )))

