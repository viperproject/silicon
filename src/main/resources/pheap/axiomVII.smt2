;
; PHeap VII: Equivalence of interpreted equality and 'PHeap_equal'
;

(assert (forall ((h1 PHeap) (h2 PHeap)) (!
	(=
		(PHeap.equal h1 h2)
		(= h1 h2)
	)
	:pattern (PHeap.equal h1 h2)
	:qid |pheapVII|)))
