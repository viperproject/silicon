;
; PHeap I: Define 'PHeap_equal' as extensional equality
; 
; Parametrization:
;   $ALL_EXT_EQ_FIELD$ 		=> newline-separated list of partials/ext_eq_field.smt2 for every field
;   $ALL_EXT_EQ_PREDICATE$ 	=> newline-separated list of partials/ext_eq_predicate.smt2 for every predicate
;   $H1$, $H2$				=> Variable name for quantified PHeap,
; 							   should match the one used to instantiate $ALL_EXT_EQ_FIELD$ and $ALL_EXT_EQ_PREDICATE$
;


(assert (forall (($H1$ PHeap) ($H2$ PHeap)) (!
	(=
		(PHeap_equal $H1$ $H2$)
		(and
			$ALL_EXT_EQ_FIELD$
			$ALL_EXT_EQ_PREDICATE$
		))
		:pattern (PHeap_equal $H1$ $H2$)
		:qid |pheap_axiomI|
)))

