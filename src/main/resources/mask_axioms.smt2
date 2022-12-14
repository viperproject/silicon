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