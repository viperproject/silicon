; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The axioms are parametric
;   - $FLD$ is a Silver field name
;   - $S$ is the sort corresponding to the type of the field
;   - $T$ is the sanitized name of the sort corresponding to the type of the field

; ATTENTION: The triggers mention the sort wrappers introduced for FVFs.
; The axiom therefore needs to be emitted after the sort wrappers have
; been emitted.

(assert (forall ((vs $FVF<$FLD$>) (ws $FVF<$FLD$>)) (!
    (=>
      (and
        (Set_equal ($FVF.domain_$FLD$ vs) ($FVF.domain_$FLD$ ws))
        (forall ((x $Ref)) (!
          (=>
            (Set_in x ($FVF.domain_$FLD$ vs))
            (= ($FVF.lookup_$FLD$ vs x) ($FVF.lookup_$FLD$ ws x)))
          :pattern (($FVF.lookup_$FLD$ vs x) ($FVF.lookup_$FLD$ ws x))
          :qid |qp.$FVF<$FLD$>-eq-inner|
          )))
      (= vs ws))
    :pattern (($SortWrappers.$FVF<$FLD$>To$Snap vs) ($FVF.has_domain_$FLD$ vs)
              ($SortWrappers.$FVF<$FLD$>To$Snap ws) ($FVF.has_domain_$FLD$ ws)
              )
    :qid |qp.$FVF<$FLD$>-eq-outer|
    )))

(assert (forall ((r $Ref) (pm $FPM)) (!
    ($Perm.isValidVar ($FVF.perm_$FLD$ pm r))
    :pattern (($FVF.perm_$FLD$ pm r))
    :qid |qp.$FVF<$FLD$>-validvar|)))

(assert (forall ((r $Ref) (f $S$)) (!
    (= ($FVF.loc_$FLD$ f r) true)
    :pattern (($FVF.loc_$FLD$ f r))
    :qid |qp.$FVF<$FLD$>-loc|)))
