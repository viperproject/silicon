;
; Parametrization:
;   $PRD$ => Predicate identifier
;   $FLD$ => Field identifier
;

(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(= (PHeap.dom_$FLD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h)) (as Set_empty Set<$Ref>))
	:pattern (PHeap.dom_$FLD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h))
	:qid |singleton_$PRD$_dom_$FLD$|)))

