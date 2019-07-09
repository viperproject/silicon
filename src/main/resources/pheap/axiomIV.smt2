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
			(Set_in (loc_$PRD$ $PRD_ARGS$) (dom_$PRD$ h1))
			(=
				(lookup_$PRD$ (combine h1 h2) (loc_$PRD$ $PRD_ARGS$))
				(lookup_$PRD$ h1 (loc_$PRD$ $PRD_ARGS$))
			)
		)
		:pattern ((lookup_$PRD$ (combine h1 h2) (loc_$PRD$ $PRD_ARGS$))))))
