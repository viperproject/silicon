; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The axioms are parametric
;   - $FLD$ is a Silver field name
;   - $S$ is the sort corresponding to the type of the field

; ATTENTION: The triggers mention the sort wrappers introduced for FVFs.
; The axiom therefore needs to be emitted after the sort wrappers have
; been emitted.

(assert (forall ((vs $FVF<$S$>) (ws $FVF<$S$>)) (!
    (implies
      (and
        ($Set.equal ($FVF.domain_$FLD$ vs) ($FVF.domain_$FLD$ ws))
        (forall ((x $Ref)) (!
          (implies
            ($Set.in x ($FVF.domain_$FLD$ vs))
            (= ($FVF.lookup_$FLD$ vs x) ($FVF.lookup_$FLD$ ws x)))
          ; :pattern (($Set.in x ($FVF.domain_$FLD$ vs)))
          :pattern (($FVF.lookup_$FLD$ vs x) ($FVF.lookup_$FLD$ ws x))
          :qid |qp.$FVF<$S$>-eq-inner|
          )))
      (= vs ws))
    ; :pattern (($FVF.domain_$FLD$ vs) ($FVF.domain_$FLD$ ws))
;     :pattern (($FVF.domain_$FLD$ ($SortWrappers.$SnapTo$FVF<$S$>($SortWrappers.$FVF<$S$>To$Snap vs)))
;               ($FVF.domain_$FLD$ ($SortWrappers.$SnapTo$FVF<$S$>($SortWrappers.$FVF<$S$>To$Snap ws))))
    :pattern (($SortWrappers.$FVF<$S$>To$Snap vs)
              ($SortWrappers.$FVF<$S$>To$Snap ws)
              ($FVF.after_$FLD$ vs ws))
    :qid |qp.$FVF<$S$>-eq-outer|
    )))

(assert (forall ((fvf1 $FVF<$S$>) (fvf2 $FVF<$S$>) (fvf3 $FVF<$S$>)) (!
    (implies
      (and
        ($FVF.after_$FLD$ fvf3 fvf2)
        ($FVF.after_$FLD$ fvf2 fvf1))
      ($FVF.after_$FLD$ fvf3 fvf1))
    :pattern (($FVF.after_$FLD$ fvf3 fvf2) ($FVF.after_$FLD$ fvf2 fvf1))
              ; ($SortWrappers.$FVF<Bool>To$Snap fvf1)
              ; ($SortWrappers.$FVF<Bool>To$Snap fvf2)
              ; ($SortWrappers.$FVF<Bool>To$Snap fvf3))
    :qid |qp.$FVF<$S$>-after_$FLD$|
    )))

(assert (forall ((fvf1 $FVF<$S$>) (fvf2 $FVF<$S$>)) (!
    (implies
      (and
        ($FVF.after_$FLD$ fvf1 $fvfTOP_$FLD$)
        ($FVF.after_$FLD$ fvf2 $fvfTOP_$FLD$))
      (or
        (= fvf1 fvf2)
        ($FVF.after_$FLD$ fvf1 fvf2)
        ($FVF.after_$FLD$ fvf2 fvf1)
      )
    )
    :pattern (($FVF.after_$FLD$ fvf1 $fvfTOP_$FLD$) ($FVF.after_$FLD$ fvf2 $fvfTOP_$FLD$))
    :qid |qp.$FVF<$S$>-top|
    )))
