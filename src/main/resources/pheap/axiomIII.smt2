(assert (forall ((h1 PHeap) (h2 PHeap) (x $Ref))
	(!
		(=>
			(Set_in x (dom_$FLD$ h1))
			(=
				(lookup_$FLD$ (combine h1 h2) x)
				(lookup_$FLD$ h1 x)
			)
		)
		:pattern ((lookup_$FLD$ (combine h1 h2) x)))))
