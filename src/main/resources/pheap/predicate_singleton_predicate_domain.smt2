;
; Parametrization:
;   $PRD1$ => Predicate identifier
;   $FLD2$ => Predicate identifier
;

(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(= (PHeap.dom_$PRD2$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h)) (as Set_empty Set<Loc>))
	:pattern (PHeap.dom_$PRD2$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h)))))

