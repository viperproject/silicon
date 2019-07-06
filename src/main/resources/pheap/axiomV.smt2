(assert (forall ((h1 PHeap) (h2 PHeap))
	(Set_equal
		(dom_$FLD$ (combine h1 h2))
		(Set_union (dom_$FLD$ h1) (dom_$FLD$ h2))
	)))
