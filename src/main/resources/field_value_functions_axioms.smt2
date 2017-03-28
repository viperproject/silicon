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
        (Set_equal ($FVF.domain_$FLD$ vs) ($FVF.domain_$FLD$ ws))
        (forall ((x $Ref)) (!
          (implies
            (Set_in x ($FVF.domain_$FLD$ vs))
            (= ($FVF.lookup_$FLD$ vs x) ($FVF.lookup_$FLD$ ws x)))
          ; :pattern ((Set_in x ($FVF.domain_$FLD$ vs)))
          :pattern (($FVF.lookup_$FLD$ vs x) ($FVF.lookup_$FLD$ ws x))
          :qid |qp.$FVF<$S$>-eq-inner|
          )))
      (= vs ws))
    :pattern (($SortWrappers.$FVF<$S$>To$Snap vs)
              ($SortWrappers.$FVF<$S$>To$Snap ws)
;              ($FVF.after_$FLD$ vs ws)
              )
    :qid |qp.$FVF<$S$>-eq-outer|
    )))