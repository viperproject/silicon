(assert (forall ((h1 PHeap) (h2 PHeap) $PRD_ARGS_Q$)
	(!
		(=>
			(Set_in (PHeap.loc_$PRD$ $PRD_ARGS$) (PHeap.dom_$PRD$ h1))
			(=
				(PHeap.lookup_$PRD$ (PHeap.combine h1 h2) (PHeap.loc_$PRD$ $PRD_ARGS$))
				(PHeap.lookup_$PRD$ h1 (PHeap.loc_$PRD$ $PRD_ARGS$))
			)
		)
		:pattern (PHeap.lookup_$PRD$ (PHeap.combine h1 h2) (PHeap.loc_$PRD$ $PRD_ARGS$))
		:qid |PHeap.pred_lookup_combine[$PRD$].trig1|)))

(assert (forall ((h1 PHeap) (h2 PHeap) $PRD_ARGS_Q$)
	(!
		(=>
			(Set_in (PHeap.loc_$PRD$ $PRD_ARGS$) (PHeap.dom_$PRD$ h1))
			(=
				(PHeap.lookup_$PRD$ (PHeap.combine h1 h2) (PHeap.loc_$PRD$ $PRD_ARGS$))
				(PHeap.lookup_$PRD$ h1 (PHeap.loc_$PRD$ $PRD_ARGS$))
			)
		)
		:pattern ((PHeap.lookup_$PRD$ h1 (PHeap.loc_$PRD$ $PRD_ARGS$)) (PHeap.combine h1 h2))
		:qid |PHeap.pred_lookup_combine[$PRD$].trig2|)))
