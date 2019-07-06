(and
	(Set.equal (dom_$PRD$ $H1$) (dom_$PRD$ $H2$))
	(forall ((l Loc)) (!
		(=>
			(Set.in l (dom_$PRD$ $H1$))
			(=
				(lookup_$PRD$ $H1$ l)
				(lookup_$PRD$ $H2$ l)
			)
		)
	:pattern ((lookup_$PRD$ $H1$ l) (lookup_$PRD$ $H2$ l)))))

