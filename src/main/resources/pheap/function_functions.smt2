;
; Parametrization:
;   $FUN$ => Function identifier
;

(declare-fun restrict_$FUN$ (PHeap) PHeap)

; TODO: Remove this and generate correct axiom dynamically during function welldefinedness check 
(assert (forall ((h PHeap)) (!
	(= h (restrict_$FUN$ h))
	:pattern (restrict_$FUN$ h))))
