; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The axioms are parametric
;   - $FLD$ is a Silver field name
;   - $S$ is the sort corresponding to the type of the field

; ATTENTION: The triggers mention the sort wrappers introduced for FVFs.
; The axiom therefore needs to be emitted after the sort wrappers have
; been emitted.

(assert (forall ((vs $PSF<$S$>) (ws $PSF<$S$>)) (!
    (implies
      (and
        (Set_equal ($PSF.domain_$PRD$ vs) ($PSF.domain_$PRD$ ws))
        (forall ((x $Snap)) (!
          (implies
            (Set_in x ($PSF.domain_$FRD$ vs))
            (= ($PSF.lookup_$PRD$ vs x) ($PSF.lookup_$PRD$ ws x)))
          :qid |qp.$PSF<$S$>-eq-inner|
          )))
      (= vs ws))
    :qid |qp.$PSF<$S$>-eq-outer|
    )))