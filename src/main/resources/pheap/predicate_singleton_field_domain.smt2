(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(= (PHeap.dom_$FLD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h)) (as Set_empty Set<$Ref>))
	:pattern (PHeap.dom_$FLD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h))
	:qid |singleton_$PRD$_dom_$FLD$|)))

(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(=
		(PHeap.dom_$FLD$ (PHeap.remove_$PRD$ h $PRD_ARGS$))
		(PHeap.dom_$FLD$ h)
	)
	:pattern (PHeap.dom_$FLD$ (PHeap.remove_$PRD$ h $PRD_ARGS$))
	:qid |dom_$FLD$_remove_$PRD$|)))

(assert (forall ((x $Ref) $PRD_ARGS_Q$ (h PHeap)) (!
	(=
		(PHeap.lookup_$FLD$ (PHeap.remove_$PRD$ h $PRD_ARGS$) x)
		(PHeap.lookup_$FLD$ h x)
	)
	:pattern (PHeap.lookup_$FLD$ (PHeap.remove_$PRD$ h $PRD_ARGS$) x)
	:qid |lookup_$FLD$_remove_$PRD$|)))
