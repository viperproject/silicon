;
; PHeap VI: Predicate domain of 'combine'
; 
; Parametrization:
;   $PRD$ => Predicate identifier
;

(assert (forall ((h1 PHeap) (h2 PHeap)) (!
	(Set_equal
		(PHeap.dom_$PRD$ (PHeap.combine h1 h2))
		(Set_union (PHeap.dom_$PRD$ h1) (PHeap.dom_$PRD$ h2))
	)
	:pattern ((PHeap.dom_$PRD$ (PHeap.combine h1 h2)))
	:qid |pheapVI($PRD$)|)))
