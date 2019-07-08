;
; Parametrization:
;   $FLD$ => Field identifier
;   $S$   => Sort corresponding to field type
;

(declare-fun lookup_$FLD$ (PHeap $Ref) $S$)
(declare-fun dom_$FLD$ (PHeap) Set<$Ref>)

