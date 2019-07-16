;
; PHeap IV: Predicate lookup in 'combine'
; 
; Parametrization:
;   $PRD$ 		  	=> Predicate identifier
;   $PRD_ARGS_Q$	=> Space-separated list of sorted predicate arguments, e.g. '(x $Ref) (b Bool)'
;   $PRD_ARGS$ 		=> Space-separated list of predicate argument identifiers introduced by $PRD_ARGS_Q$

(assert (forall ((h1 PHeap) (h2 PHeap) $PRD_ARGS_Q$)
	(!
		(=>
			(Set_in (PHeap.loc_$PRD$ $PRD_ARGS$) (PHeap.dom_$PRD$ h1))
			(=
				(PHeap.lookup_$PRD$ (PHeap.combine h1 h2) (PHeap.loc_$PRD$ $PRD_ARGS$))
				(PHeap.lookup_$PRD$ h1 (PHeap.loc_$PRD$ $PRD_ARGS$))
			)
		)
		:pattern ((PHeap.lookup_$PRD$ (PHeap.combine h1 h2) (PHeap.loc_$PRD$ $PRD_ARGS$))))))
