(assert (forall ((h1 PHeap) (h2 PHeap) (x $Ref))
	(!
		(=>
			(Set_in x (PHeap.dom_$FLD$ h1))
			(=
				(PHeap.lookup_$FLD$ (PHeap.combine h1 h2) x)
				(PHeap.lookup_$FLD$ h1 x)
			)
		)
		:pattern ((PHeap.lookup_$FLD$ (PHeap.combine h1 h2) x))
		:pattern ((PHeap.lookup_$FLD$ h1 x) (PHeap.combine h1 h2))
		:qid |field_lookup_combine[$FLD$]|)))

