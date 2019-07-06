(assert (forall ((h1 PHeap) (h2 PHeap) $PRD_ARGS_Q$)
	(!
		(=>
			(Set.in (loc_$PRD$ $PRD_ARGS$) (dom_$PRD$ h1))
			(=
				(lookup_$PRD$ (combine h1 h2) (loc_$PRD$ $PRD_ARGS$))
				(lookup_$PRD$ h1 (loc_$PRD$ $PRD_ARGS$))
			)
		)
		:pattern ((lookup_$PRD$ (combine h1 h2) (loc_$PRD$ $PRD_ARGS$))))))
