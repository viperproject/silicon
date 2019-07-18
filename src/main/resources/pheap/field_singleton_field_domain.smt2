;
; Parametrization:
;   $PRD$ => Predicate identifier
;   $FLD$ => Field identifier
;

(assert (forall ((x $Ref) (v $S$)) (!
	(= (PHeap.dom_$FLD2$ (PHeap.singleton_$FLD$ x v)) (as Set_empty Set<$Ref>))
	:pattern (PHeap.dom_$FLD2$ (PHeap.singleton_$FLD$ x v)))))

