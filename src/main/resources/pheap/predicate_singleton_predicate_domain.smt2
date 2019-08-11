;
;
(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(= (PHeap.dom_$PRD2$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h)) (as Set_empty Set<Loc>))
	:pattern (PHeap.dom_$PRD2$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h))
	:qid |singleton_$PRD$_dom_$PRD2$|)))

(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(=
		(PHeap.dom_$PRD2$ (PHeap.remove_$PRD$ h $PRD_ARGS$))
		(PHeap.dom_$PRD2$ h)
	)
	:pattern (PHeap.dom_$PRD2$ (PHeap.remove_$PRD$ h $PRD_ARGS$))
	:qid |dom_$PRD2$_remove_$PRD$|)))

(assert (forall ($PRD_ARGS_Q2$ $PRD_ARGS_Q$ (h PHeap)) (!
	(=
		(PHeap.lookup_$PRD2$ (PHeap.remove_$PRD$ h $PRD_ARGS$) (PHeap.loc_$PRD2$ $PRD_ARGS2$))
		(PHeap.lookup_$PRD2$ h (PHeap.loc_$PRD2$ $PRD_ARGS2$))
	)
	:pattern (PHeap.lookup_$PRD2$ (PHeap.remove_$PRD$ h $PRD_ARGS$) (PHeap.loc_$PRD2$ $PRD_ARGS2$))
	:qid |lookup_$PRD2$_remove_$PRD$|)))

