; Parameters:
; ????  - $FLD$ is the name of the field f to look-up at x in vs
; ????  - $S$ is the sort that corresponds to x's type

; forall vs: FVF, x: Ref :: lookup(vs, x)^-1 = x
(assert (forall ((vs $FVF<$S$>) (x $Ref)) (!
    (= ($FVF.lookup_$FLD$_inv vs ($FVF.lookup_$FLD$ vs x)) x)
    :pattern (($FVF.lookup_$FLD$_inv vs ($FVF.lookup_$FLD$ vs x)))
    )))
