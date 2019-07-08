;
; PHeap VI: Predicate domain of 'combine'
; 
; Parametrization:
;   $PRD$ => Predicate identifier
;

(assert (forall ((h1 PHeap) (h2 PHeap))
	(Set.equal
		(dom_$PRD$ (combine h1 h2))
		(Set.union (dom_$PRD$ h1) (dom_$PRD$ h2))
	)))
