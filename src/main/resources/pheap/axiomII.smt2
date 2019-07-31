;
; PHeap II: Equality of abstract function applications
;
; This axiom is logically redundant as it is implied by VII and the theory uf uninterpreted functions,
; but it is currently needed for triggering reasons
; 
; Parametrization:
;   $FUN$ 			=> Identifier of function corresponding to abstract Viper function
;   $FUN_ARGS_Q$	=> Space-separated list of sorted function arguments, e.g. '(x $Ref) (b Bool)'
;   $FUN_ARGS$ 		=> Space-separated list of function argument identifiers introduced by $FUN_ARGS_Q$


(assert (forall ((h1 PHeap) (h2 PHeap) $FUN_ARGS_Q$) (!
	(=>
		(PHeap.equal h1 h2)
		(= ($FUN$ h1 $FUN_ARGS$) ($FUN$ h2 $FUN_ARGS$))
	)
	:pattern (($FUN$ h2 $FUN_ARGS$) ($FUN$ h1 $FUN_ARGS$))
	:qid |pheapII($FUN$)|)))

