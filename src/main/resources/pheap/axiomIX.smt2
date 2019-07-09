;
; PHeap IX: Associativity of 'combine'
;

(assert (forall ((h1 PHeap) (h2 PHeap) (h3 PHeap)) (!
	(=
		(combine (combine h1 h2) h3)
		(combine h1 (combine h2 h3))
	)
	:pattern (combine (combine h1 h2) h3))))

