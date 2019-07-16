;
; PHeap IX: Associativity of 'combine'
;

(assert (forall ((h1 PHeap) (h2 PHeap) (h3 PHeap)) (!
	(=
		(PHeap.combine (PHeap.combine h1 h2) h3)
		(PHeap.combine h1 (PHeap.combine h2 h3))
	)
	:pattern (PHeap.combine (PHeap.combine h1 h2) h3))))

