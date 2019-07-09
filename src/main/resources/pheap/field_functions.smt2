;
; Parametrization:
;   $FLD$ => Field identifier
;   $S$   => Sort corresponding to field type
;

(declare-fun lookup_$FLD$ (PHeap $Ref) $S$)
(declare-fun dom_$FLD$ (PHeap) Set<$Ref>)

(declare-fun singleton_$FLD$ ($Ref $S$) PHeap)
(assert (forall ((x $Ref) (v $S$)) (!
	(= (dom_$FLD$ (singleton_$FLD$ x v)) (Set_singleton x))
	:pattern (dom_$FLD$ (singleton_$FLD$ x v)))))

(assert (forall ((x $Ref) (v $S$)) (!
	(= (lookup_$FLD$ (singleton_$FLD$ x v) x) v)
	:pattern (lookup_$FLD$ (singleton_$FLD$ x v) x))))

; TODO: move this
(assert (Set_equal
	(dom_$FLD$ emp)
	Set_empty))
