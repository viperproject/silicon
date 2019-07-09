;
; Extensional equality between PHeaps over a predicate
; 
; Parametrization:
;	$PRD$		=> Predicate identifier
;   $H1$, $H2$  => Variable name for free PHeap variables,

(and
	(Set_equal (dom_$PRD$ $H1$) (dom_$PRD$ $H2$))
	(forall ((l Loc)) (!
		(=>
			(Set_in l (dom_$PRD$ $H1$))
			(=
				(lookup_$PRD$ $H1$ l)
				(lookup_$PRD$ $H2$ l)
			)
		)
	:pattern ((lookup_$PRD$ $H1$ l) (lookup_$PRD$ $H2$ l)))))

