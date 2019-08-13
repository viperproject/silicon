(assert (forall ((h1 PHeap) (h2 PHeap)) (!
	(=
		(PHeap.combine h1 h2)
		(PHeap.combine h2 h1)
	)
	:pattern (PHeap.combine h1 h2)
	:qid |PHeap.symmetry_combine|)))

