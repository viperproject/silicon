(assert (forall (($H1$ PHeap) ($H2$ PHeap)) (!
	(=
		(PHeap_equal $H1$ $H2$)
		(and
			$ALL_EXT_EQ_FIELD$
			$ALL_EXT_EQ_PREDICATE$
		))
		:pattern (PHeap_equal $H1$ $H2$))))

