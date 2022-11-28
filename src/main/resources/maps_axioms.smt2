; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The definitions are parametric
;   - $S$ is the sort corresponding to the type of the field
;   - $T$ is the sanitized name of the sort corresponding to the type of the field




(assert (forall ((m1 $Mp<$T$>) (r1 $Ref) (v $S$) (r2 $Ref)) (!
      (=
        ($Mp.get_$T$ ($Mp.update_$T$ m1 r1 v) r2)
        (ite (= r1 r2) v ($Mp.get_$T$ m1 r2)))
    :pattern (($Mp.get_$T$ ($Mp.update_$T$ m1 r1 v) r2))
    :qid |qp.$Mp.update_$T$-def|
    )))


(assert (forall ((oh $Mp<$T$>) (nh $Mp<$T$>) (m $Mp<$Perm>) (r $Ref)) (!
      (=> ($Mp.identicalOnKnown_$T$ oh nh m)
       (=>
        (> ($Mp.get_$Perm m r) $Perm.No)
        (= ($Mp.get_$T$ oh r) ($Mp.get_$T$ nh r))))
    :pattern (($Mp.identicalOnKnown_$T$ oh nh m) ($Mp.get_$T$ nh r))
    :qid |qp.$Mp.update_$T$-def|
    )))






