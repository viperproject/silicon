(assert (forall ((h1 PHeap) (h2 PHeap) $FUN_ARGS_Q$) (!
	(=>
		(PHeap_equal h1 h2)
		(= ($FUN$ h1 $FUN_ARGS$) ($FUN$ h2 $FUN_ARGS$))
	)
	: pattern ())))

