; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The definitions are parametric
;   - $S$ is the sort corresponding to the type of the field
;   - $T$ is the sanitized name of the sort corresponding to the type of the field


(assert (forall ((m1 $Hp<$T$>) (r1 $Ref) (v $S$)) (!
      (forall ((r2 $Ref)) (!
            (implies (not (= r1 r2))
            (=
              ($Hp.get_$T$ ($Hp.update_$T$ m1 r1 v) r2)
              ($Hp.get_$T$ m1 r2)))
          :pattern (($Hp.get_$T$ ($Hp.update_$T$ m1 r1 v) r2))
          :qid |qp.$Hp.update_$T$-def-inner|
          ))
    :pattern (($Hp.update_$T$ m1 r1 v))
    :qid |qp.$Hp.update_$T$-def|
    )))


(assert (forall ((m1 $Hp<$T$>) (r1 $Ref) (v $S$)) (!
            (=
              ($Hp.get_$T$ ($Hp.update_$T$ m1 r1 v) r1)
              v)
    :pattern (($Hp.update_$T$ m1 r1 v))
    :qid |qp.$Hp.update_$T$-def|
    )))


(assert (forall ((r1 $Ref) (v $S$)) (!
      (=
        ($Hp.get_$T$ ($Hp.singleton_$T$ r1 v) r1)
        v)
    :pattern (($Hp.get_$T$ ($Hp.singleton_$T$ r1 v) r1))
    :qid |qp.$Hp.signleton_$T$-def|
    )))


(assert (forall ((oh $Hp<$T$>) (nh $Hp<$T$>) (m $Hp<$Perm>)) (!
      (=> ($Hp.identicalOnKnown_$T$ oh nh m)
       (forall ((r $Ref)) (!
              (=>
               (> ($Hp.get_$Perm m r) $Perm.No)
               (= ($Hp.get_$T$ oh r) ($Hp.get_$T$ nh r)))
           :pattern (($Hp.get_$T$ nh r))
           :qid |qp.$Hp.update_$T$-def-inner|
           )))
    :pattern (($Hp.identicalOnKnown_$T$ oh nh m))
    :qid |qp.$Hp.update_$T$-def|
    )))


(assert (forall ((h1 $Hp<$T$>) (m1 $Hp<$Perm>) (h2 $Hp<$T$>) (m2 $Hp<$Perm>)) (!
       (forall ((r $Ref)) (!
              (and
               (=> (> ($Hp.get_$Perm m1 r) $Perm.No) (= ($Hp.get_$T$ h1 r) ($Hp.get_$T$ ($Hp.merge_$T$ h1 m1 h2 m2) r)))
               (=> (> ($Hp.get_$Perm m2 r) $Perm.No) (= ($Hp.get_$T$ h2 r) ($Hp.get_$T$ ($Hp.merge_$T$ h1 m1 h2 m2) r))))
           :pattern (($Hp.get_$T$ ($Hp.merge_$T$ h1 m1 h2 m2) r))
           :qid |qp.$Hp.merge_$T$-def-inner|
           ))
    :pattern (($Hp.merge_$T$ h1 m1 h2 m2))
    :qid |qp.$Hp.merge_$T$-def|
    )))

(assert (forall ((h1 $Hp<$T$>) (m1 $Hp<$Perm>) (h2 $Hp<$T$>) (m2 $Hp<$Perm>)) (!
       (forall ((r $Ref)) (!
        (=> ($Hp.overlap_$T$ h1 m1 h2 m2)
               (=> (and (> ($Hp.get_$Perm m1 r) $Perm.No) (> ($Hp.get_$Perm m2 r) $Perm.No)) (= ($Hp.get_$T$ h1 r) ($Hp.get_$T$ h2 r))))
           :pattern (($Hp.get_$T$ h1 r))
           :pattern (($Hp.get_$T$ h2 r))
           :qid |qp.$Hp.overlap_$T$-def-inner|
           ))
    :pattern (($Hp.overlap_$T$ h1 m1 h2 m2))
    :qid |qp.$Hp.overlap_$T$-def|
    )))

(assert (forall ((oh $Hp<$T$>) (om $Hp<$Perm>) (r $Ref) (v $S$)) (!
       (forall ((r2 $Ref)) (!
              (and
               (=> (= r r2) (= ($Hp.get_$T$ ($Hp.merge_single_$T$ oh om r v) r2) v))
               (=> (> ($Hp.get_$Perm om r2) 0.0) (= ($Hp.get_$T$ ($Hp.merge_single_$T$ oh om r v) r2) ($Hp.get_$T$ oh r2))))
           :pattern (($Hp.get_$T$ ($Hp.merge_single_$T$ oh om r v) r2))
           :qid |qp.$Hp.merge_single_$T$-def-inner|
           ))
    :pattern (($Hp.merge_single_$T$ oh om r v))
    :qid |qp.$Hp.merge_single_$T$-def|
    )))
