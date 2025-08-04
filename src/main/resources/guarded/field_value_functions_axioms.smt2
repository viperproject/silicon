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

(declare-fun  preambleax1$FLD$@$S$<$T$> (Bool) Bool)
(assert (forall (($guardvar Bool))  (! (forall ((vs $FVF<$FLD$>) (ws $FVF<$FLD$>)) (!
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
                                                                                   :pattern (($SortWrappers.$FVF<$FLD$>To$Snap vs)
                                                                                             ($SortWrappers.$FVF<$FLD$>To$Snap ws)
                                                                                             )
                                                                                   :qid |qp.$FVF<$FLD$>-eq-outer|
                                                                                   ))
                                      :pattern ((preambleax1$FLD$@$S$<$T$> $guardvar))
                                      :pattern (($GlobalGuard $guardvar)))))

(declare-fun  preambleax2$FLD$@$S$<$T$> (Bool) Bool)
(assert (forall (($guardvar Bool))  (! (forall ((r $Ref) (pm $FPM)) (!
                                                                    ($Perm.isValidVar ($FVF.perm_$FLD$ pm r))
                                                                    :pattern (($FVF.perm_$FLD$ pm r))))
                                      :pattern ((preambleax2$FLD$@$S$<$T$> $guardvar))
                                      :pattern (($GlobalGuard $guardvar)))))

(declare-fun  preambleax3$FLD$@$S$<$T$> (Bool) Bool)
(assert (forall (($guardvar Bool))  (! (forall ((r $Ref) (f $S$)) (!
                                                                  (= ($FVF.loc_$FLD$ f r) true)
                                                                  :pattern (($FVF.loc_$FLD$ f r))))
                                      :pattern ((preambleax3$FLD$@$S$<$T$> $guardvar))
                                      :pattern (($GlobalGuard $guardvar)))))
