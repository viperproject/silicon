;
; PHeap VIII: Commutativity of 'combine'
;

(assert (forall ((h1 PHeap) (h2 PHeap)) (!
	(=
		(combine h1 h2)
		(combine h2 h1)
	)
	:pattern (combine h1 h2))))

