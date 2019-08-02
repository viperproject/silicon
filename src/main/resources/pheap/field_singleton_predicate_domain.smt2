;
; Parametrization:
;   $PRD$ => Predicate identifier
;   $FLD$ => Field identifier
;

(assert (forall ((x $Ref) (v $S$)) (!
	(= (PHeap.dom_$PRD$ (PHeap.singleton_$FLD$ x v)) (as Set_empty Set<Loc>))
	:pattern (PHeap.dom_$PRD$ (PHeap.singleton_$FLD$ x v))
	:qid |singleton_$FLD$_dom_$PRD$|)))

