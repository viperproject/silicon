(assert (forall ((h1 PHeap) (h2 PHeap)) (!
	(=
		(PHeap_equal h1 h2)
		(= h1 h2)
	)
	:pattern (PHeap_equal h1 h2))))
