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

(assert (forall ((m1 $Hp<$Perm>) (m2 $Hp<$Perm>)) (!
  (=>
    (forall ((x $Ref)) (!
        (= ($Hp.get_$Perm m1 x) ($Hp.get_$Perm m2 x))
      :pattern (($Hp.get_$Perm m1 x) ($Hp.get_$Perm m2 x))
      :qid |qp.$Hp.maskEq-def-inner|
      ))
    ($Hp.maskEq m1 m2)
    )
    :pattern (($Hp.maskEq m1 m2))
    :qid |qp.$Hp.maskEq-def|
    )))


(assert (forall ((m1 $Hp<$Perm>) (m2 $Hp<$Perm>)) (!
     (forall ((r $Ref)) (!
        (=
          (+ ($Hp.get_$Perm m1 r) ($Hp.get_$Perm m2 r))
          ($Hp.get_$Perm ($Hp.maskSum m1 m2) r)
          )
      :pattern (($Hp.get_$Perm ($Hp.maskSum m1 m2) r))
      :qid |qp.$Hp.maskSum-def-inner|
      ))
    :pattern (($Hp.maskSum m1 m2))
    :qid |qp.$Hp.maskSum-def|
    )))

(assert (forall ((m1 $Hp<$Perm>) (m2 $Hp<$Perm>)) (!
    (forall ((r $Ref)) (!
        (=
          (- ($Hp.get_$Perm m1 r) ($Hp.get_$Perm m2 r))
          ($Hp.get_$Perm ($Hp.maskDiff m1 m2) r)
          )
      :pattern (($Hp.get_$Perm ($Hp.maskDiff m1 m2) r))
      :qid |qp.$Hp.maskDiff-def-inner|
      ))
    :pattern (($Hp.maskDiff m1 m2))
    :qid |qp.$Hp.maskDiff-def|
    )))

(assert (forall ((m $Hp<$Perm>) (r1 $Ref) (v Real)) (!
  (forall ((r2 $Ref)) (!
        (=
          ($Hp.get_$Perm ($Hp.maskAdd m r1 v) r2)
          (+ ($Hp.get_$Perm m r2) (ite (= r1 r2) v 0.0)))
      :pattern (($Hp.get_$Perm ($Hp.maskAdd m r1 v) r2))
      ;:pattern (($Hp.get_$Perm m r2))
      :qid |qp.$Hp.maskAdd-def-inner|
      ))
    :pattern (($Hp.maskAdd m r1 v))
    :qid |qp.$Hp.maskAdd-def|
    )))

(assert (forall ((m $Hp<$Perm>) (r1 $Ref) (v Real)) (!
        (=
          ($Hp.get_$Perm ($Hp.maskAdd m r1 v) r1)
          (+ ($Hp.get_$Perm m r1) v))
    :pattern (($Hp.maskAdd m r1 v))
    :qid |qp.$Hp.maskAdd-def|
    )))

(assert (forall ((m $Hp<$Perm>)) (!
  (=> ($Hp.maskGood m)
  (forall ((r2 $Ref)) (!
        (>=
          ($Hp.get_$Perm m r2)
          0.0)
      :pattern (($Hp.get_$Perm m r2))
      :qid |qp.$Hp.maskGood-def-inner|
      )))
    :pattern (($Hp.maskGood m))
    :qid |qp.$Hp.maskGood-def|
    )))


(assert (forall ((m $Hp<$Perm>)) (!
  (=> ($Hp.maskGoodField m)
  (and
  (forall ((r2 $Ref)) (!
        (and (>=
          ($Hp.get_$Perm m r2)
          0.0)
          (<=
                    ($Hp.get_$Perm m r2)
                    1.0))
      :pattern (($Hp.get_$Perm m r2))
      :qid |qp.$Hp.maskGoodField-def-inner|
      ))
  (= ($Hp.get_$Perm m $Ref.null) 0.0)
      ))
    :pattern (($Hp.maskGoodField m))
    :qid |qp.$Hp.maskGoodField-def|
    )))


(assert (forall ((m $Hp<$Perm>) (r $Ref) (v Real)) (!
  (=> ($Hp.maskGoodField m)
        (and (>=
          ($Hp.get_$Perm ($Hp.maskAdd m r v) r)
          0.0)
          (<=
                    ($Hp.get_$Perm ($Hp.maskAdd m r v) r)
                    1.0)))
    :pattern (($Hp.maskGoodField ($Hp.maskAdd m r v)))
    :qid |qp.$Hp.maskGoodFieldAdd-def|
    )))
