; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The definitions are parametric
;   - $FLD$ is a Silver field name
;   - $S$ is the sort corresponding to the type of the field
;   - $T$ is the sanitized name of the sort corresponding to the type of the field



(assert (forall ((h $Mp<$T$>) (s Set<$Ref>) (r $Ref)) (!
      (=>
        (Set_in r s)
        (= ($Hp.get_$T$ ($SortWrappers.$SnapTo$Heap<FLD> ($SortWrappers.$Heap<FLD>To$Snap h s)) r) ($Hp.get_$T$ h r))
        )
    :pattern (($Hp.get_$T$ ($SortWrappers.$SnapTo$Heap<FLD> ($SortWrappers.$Heap<FLD>To$Snap h s)) r))
    :qid |qp.$SnapTo$Heap<FLD>-def|
    )))

(assert (forall ((h1 $Mp<$T$>) (s1 Set<$Ref>) (h2 $Mp<$T$>) (s2 Set<$Ref>)) (!
      (=>
        (and (Set_equal s1 s2) (forall ((x $Ref)) (!
                                          (=>
                                            (Set_in x s1)
                                            (= ($Hp.get_$T$ h1 x) ($Hp.get_$T$ h2 x)))
                                          :pattern (($Hp.get_$T$ h1 x) ($Hp.get_$T$ h2 x))
                                          :qid |qp.$SnapTo$Heap<FLD>-ext-inner|
                                          )))
        (= ($SortWrappers.$Heap<FLD>To$Snap h1 s1) ($SortWrappers.$Heap<FLD>To$Snap h2 s2))
        )
    :pattern (($SortWrappers.$Heap<FLD>To$Snap h1 s1) ($SortWrappers.$Heap<FLD>To$Snap h2 s2))
    :qid |qp.$SnapTo$Heap<FLD>-ext|
    )))