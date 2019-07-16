;
; Parametrization:
;   $FLD$ => Field identifier
;   $S$   => Sort corresponding to field type
;

(declare-fun PHeap.lookup_$FLD$ (PHeap $Ref) $S$)
(declare-fun PHeap.dom_$FLD$ (PHeap) Set<$Ref>)

(declare-fun PHeap.singleton_$FLD$ ($Ref $S$) PHeap)
(assert (forall ((x $Ref) (v $S$)) (!
	(= (PHeap.dom_$FLD$ (PHeap.singleton_$FLD$ x v)) (Set_singleton x))
	:pattern (PHeap.dom_$FLD$ (PHeap.singleton_$FLD$ x v)))))

(assert (forall ((x $Ref) (v $S$)) (!
	(= (PHeap.lookup_$FLD$ (PHeap.singleton_$FLD$ x v) x) v)
	:pattern (PHeap.lookup_$FLD$ (PHeap.singleton_$FLD$ x v) x))))

; TODO: move this
(assert (Set_equal
	(PHeap.dom_$FLD$ PHeap.emp)
	(as Set_empty Set<$Ref>)))
