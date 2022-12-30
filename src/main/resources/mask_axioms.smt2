; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

(assert (forall ((r $Ref)) (!
      (=
        ($Hp.get_$Perm $Hp.zeroMask r)
        0.0)
    :pattern (($Hp.get_$Perm $Hp.zeroMask r))
    :qid |qp.$Hp.zeroMask-def|
    )))

(assert (forall ((m1 $Hp<$Perm>) (m2 $Hp<$Perm>)) (!
      (=>
        (forall ((x $Ref)) (!
                                                    (= (> ($Hp.get_$Perm m1 x) 0.0) (> ($Hp.get_$Perm m2 x) 0.0))
                                                  :pattern (($Hp.get_$Perm m1 x) ($Hp.get_$Perm m2 x))
                                                  :qid |qp.$Hp.maskDomainIdentical-def-inner|
                                                  ))
        ($Hp.maskDomainIdentical m1 m2)
        )
    :pattern (($Hp.maskDomainIdentical m1 m2))
    :qid |qp.$Hp.maskDomainIdentical-def|
    )))


(assert (forall ((m1 $Hp<$Perm>) (m2 $Hp<$Perm>) (r $Ref)) (!
      (=
        (+ ($Hp.get_$Perm m1 r) ($Hp.get_$Perm m2 r))
        ($Hp.get_$Perm ($Hp.maskSum m1 m2) r)
        )
    :pattern (($Hp.get_$Perm ($Hp.maskSum m1 m2) r))
    :qid |qp.$Hp.maskSum-def|
    )))

(assert (forall ((m1 $Hp<$Perm>) (m2 $Hp<$Perm>) (r $Ref)) (!
      (=
        (- ($Hp.get_$Perm m1 r) ($Hp.get_$Perm m2 r))
        ($Hp.get_$Perm ($Hp.maskDiff m1 m2) r)
        )
    :pattern (($Hp.get_$Perm ($Hp.maskDiff m1 m2) r))
    :qid |qp.$Hp.maskDiff-def|
    )))

;(declare-fun $Hp.maskAdd ($Hp<$Perm> $Ref $Perm) $Hp<$Perm>)

(assert (forall ((m $Hp<$Perm>) (r1 $Ref) (v Real) (r2 $Ref)) (!
      (=
        ($Hp.get_$Perm ($Hp.maskAdd m r1 v) r2)
        (ite (= r1 r2) (+ v ($Hp.get_$Perm m r2)) ($Hp.get_$Perm m r2)))
    :pattern (($Hp.get_$Perm ($Hp.maskAdd m r1 v) r2))
    :qid |qp.$Hp.maskAdd-def|
    )))