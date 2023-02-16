; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The axioms are parametric
;   - $PRD$ is a Silver predicate name
;   - $S$ is the sort corresponding to the type of the field

; ATTENTION: The triggers mention the sort wrappers introduced for PSFs.
; The axiom therefore needs to be emitted after the sort wrappers have
; been emitted.

(assert (forall ((vs $PSF<$PRD$>) (ws $PSF<$PRD$>)) (!
    (=>
      (and
        (Set_equal ($PSF.domain_$PRD$ vs) ($PSF.domain_$PRD$ ws))
        (forall ((x $Snap)) (!
          (=>
            (Set_in x ($PSF.domain_$PRD$ vs))
            (= ($PSF.lookup_$PRD$ vs x) ($PSF.lookup_$PRD$ ws x)))
          ; :pattern ((Set_in x ($PSF.domain_$PRD$ vs)))
          :pattern (($PSF.lookup_$PRD$ vs x) ($PSF.lookup_$PRD$ ws x))
          :qid |qp.$PSF<$PRD$>-eq-inner|
          )))
      (= vs ws))
    :pattern (($SortWrappers.$PSF<$PRD$>To$Snap vs)
              ($SortWrappers.$PSF<$PRD$>To$Snap ws)
;              ($PSF.after_$PRD$ vs ws)
              )
    :qid |qp.$PSF<$PRD$>-eq-outer|
    )))

(assert (forall ((s $Snap) (pm $PPM)) (!
    ($Perm.isValidVar ($PSF.perm_$PRD$ pm s))
    :pattern (($PSF.perm_$PRD$ pm s)))))

(assert (forall ((s $Snap) (f $S$)) (!
    (= ($PSF.loc_$PRD$ f s) true)
    :pattern (($PSF.loc_$PRD$ f s)))))
