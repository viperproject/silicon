;
; Parametrization:
;   $PRD$ 	   => Predicate identifier
;   $PRD_ARGS$ => Space-separated list of predicate argument sorts
;

(declare-fun PHeap.lookup_$PRD$ (PHeap Loc) PHeap)
(declare-fun PHeap.dom_$PRD$ (PHeap) Set<Loc>)
(declare-fun PHeap.loc_$PRD$ ($PRD_ARGS_S$) Loc)

(declare-fun PHeap.singleton_$PRD$ ($PRD_ARGS_S$ PHeap) PHeap)

(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(= (PHeap.dom_$PRD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h)) (Set_singleton (PHeap.loc_$PRD$ $PRD_ARGS$)))
	:pattern (PHeap.dom_$PRD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h)))))

(assert (forall ($PRD_ARGS_Q$ (h PHeap)) (!
	(= (PHeap.lookup_$PRD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h) (PHeap.loc_$PRD$ $PRD_ARGS$)) h)
	:pattern (PHeap.lookup_$PRD$ (PHeap.singleton_$PRD$ $PRD_ARGS$ h) (PHeap.loc_$PRD$ $PRD_ARGS$)))))

; TODO: move this
(assert (Set_equal
  (PHeap.dom_$PRD$ PHeap.emp)
  (as Set_empty Set<Loc>)))

