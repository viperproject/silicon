; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The definitions are parametric
;   - $S$ is the sort corresponding to the type of the field
;   - $T$ is the sanitized name of the sort corresponding to the type of the field




(assert (forall ((m1 $Hp<$T$>) (r1 $Ref) (v $S$) (r2 $Ref)) (!
      (=
        ($Hp.get_$T$ ($Hp.update_$T$ m1 r1 v) r2)
        (ite (= r1 r2) v ($Hp.get_$T$ m1 r2)))
    :pattern (($Hp.get_$T$ ($Hp.update_$T$ m1 r1 v) r2))
    :qid |qp.$Hp.update_$T$-def|
    )))


(assert (forall ((oh $Hp<$T$>) (nh $Hp<$T$>) (m $Hp<$Perm>) (r $Ref)) (!
      (=> ($Hp.identicalOnKnown_$T$ oh nh m)
       (=>
        (> ($Hp.get_$Perm m r) $Perm.No)
        (= ($Hp.get_$T$ oh r) ($Hp.get_$T$ nh r))))
    :pattern (($Hp.identicalOnKnown_$T$ oh nh m) ($Hp.get_$T$ nh r))
    :qid |qp.$Hp.update_$T$-def|
    )))


(assert (forall ((oh $Hp<$T$>) (nh $Hp<$T$>) (m $Hp<$Perm>) (r $Ref)) (!
       (and
        (=> (> ($Hp.get_$Perm m r) $Perm.No) (= ($Hp.get_$T$ nh r) ($Hp.get_$T$ ($Hp.merge_$T$ oh nh m) r)))
        (= ($Hp.get_$T$ oh r) ($Hp.get_$T$ ($Hp.merge_$T$ oh nh m) r)))
    :pattern (($Hp.get_$T$ ($Hp.merge_$T$ oh nh m) r))
    :qid |qp.$Hp.merge_$T$-def|
    )))

(assert (forall ((oh $Hp<$T$>) (r $Ref) (v $S$)) (!
       (and
        (= ($Hp.merge_single_$T$ oh r v) oh)
        (= ($Hp.get_$T$ oh r) v))
    :pattern (($Hp.merge_single_$T$ oh r v))
    :qid |qp.$Hp.merge_single_$T$-def|
    )))
