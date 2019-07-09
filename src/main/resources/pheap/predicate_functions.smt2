;
; Parametrization:
;   $PRD$ 	   => Predicate identifier
;   $PRD_ARGS$ => Space-separated list of predicate argument sorts
;

(declare-fun lookup_$PRD$ (PHeap Loc) PHeap)
(declare-fun dom_$PRD$ (PHeap) Set<Loc>)
(declare-fun loc_$PRD$ ($PRD_ARGS$) Loc)

; TODO: move this
(assert (Set_equal
  (dom_$PRD$ emp)
  Set.empty<Loc>))

