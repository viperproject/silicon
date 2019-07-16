;
; Parametrization:
;   $PRD$ 	   => Predicate identifier
;   $PRD_ARGS$ => Space-separated list of predicate argument sorts
;

(declare-fun PHeap.lookup_$PRD$ (PHeap Loc) PHeap)
(declare-fun PHeap.dom_$PRD$ (PHeap) Set<Loc>)
(declare-fun PHeap.loc_$PRD$ ($PRD_ARGS$) Loc)

; TODO: move this
(assert (Set_equal
  (PHeap.dom_$PRD$ PHeap.emp)
  (as Set_empty Set<Loc>)))

