; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The axioms are parametric
;   - $FLD$ is a Silver field name

(assert (forall ((vs $FVF) (ws $FVF)) (!
    (implies
      (and
        ($Set.eq ($FVF.domain_$FLD$ vs) ($FVF.domain_$FLD$ ws))
        (forall ((x $Ref)) (!
          (implies
            ($Set.in x ($FVF.domain_$FLD$ vs))
            (= ($FVF.lookup_$FLD$ vs x) ($FVF.lookup_$FLD$ ws x)))
          ; :pattern (($Set.in x ($FVF.domain_$FLD$ vs)))
          :pattern (($FVF.lookup_$FLD$ vs x) ($FVF.lookup_$FLD$ ws x)))))
      (= vs ws))
    :pattern (($FVF.domain_$FLD$ vs) ($FVF.domain_$FLD$ ws)))))
