(assert (forall ((h1 PHeap) (h2 PHeap) $PRD_ARGS_Q$)
	(!
		(=>
			(Set_in $PRD_LOC$ (PHeap.dom_$PRD$ h1))
			(=
				(PHeap.lookup_$PRD$ (PHeap.combine h1 h2) $PRD_LOC$)
				(PHeap.lookup_$PRD$ h1 $PRD_LOC$)
			)
		)
		:pattern (PHeap.lookup_$PRD$ (PHeap.combine h1 h2) $PRD_LOC$)
		:pattern ((PHeap.lookup_$PRD$ h1 $PRD_LOC$) (PHeap.combine h1 h2))
		:qid |PHeap.pred_lookup_combine[$PRD$]|)))

