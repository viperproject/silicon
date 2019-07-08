;
; Extensional equality between PHeaps over a field
; 
; Parametrization:
;	$FLD$					=> Field identifier
;   $H1$, $H2$				=> Variable name for free PHeap variables,

(and
	(Set_equal (dom_$FLD$ $H1$) (dom_$FLD$ $H2$))
	(forall ((x $Ref)) (!
		(=>
			(Set_in x (dom_$FLD$ $H1$))
			(=
				(lookup_$FLD$ $H1$ x)
				(lookup_$FLD$ $H2$ x)
			)
		)
	:pattern ((lookup_$FLD$ $H1$ x) (lookup_$FLD$ $H2$ x)))))

