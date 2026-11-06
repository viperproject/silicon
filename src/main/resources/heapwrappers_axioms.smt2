; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The definitions are parametric
;   - $FLD$ is a Silver field name
;   - $S$ is the sort corresponding to the type of the field
;   - $T$ is the sanitized name of the sort corresponding to the type of the field


(assert (forall ((h $Hp<$T$>) (s $Hp<$Perm>)) (!
  (forall ((r $Ref)) (!
        (=>
          (> ($Hp.get_$Perm s r) $Perm.No)
          (= ($Hp.get_$T$ ($SortWrappers.$SnapTo$Heap<$FLD$> ($SortWrappers.$Heap<$FLD$>To$Snap h s)) r) ($Hp.get_$T$ h r))
          )
      :pattern (($Hp.get_$T$ ($SortWrappers.$SnapTo$Heap<$FLD$> ($SortWrappers.$Heap<$FLD$>To$Snap h s)) r))
      :qid |qp.$SnapTo$Heap<$FLD$>-def-inner|
      ))
    :pattern (($SortWrappers.$SnapTo$Heap<$FLD$> ($SortWrappers.$Heap<$FLD$>To$Snap h s)))
    :qid |qp.$SnapTo$Heap<$FLD$>-def|
    )))

(assert (forall ((h1 $Hp<$T$>) (s1 $Hp<$Perm>) (h2 $Hp<$T$>) (s2 $Hp<$Perm>)) (!
  (=>
    (and ($Hp.maskDomainIdentical s1 s2) (forall ((x $Ref)) (!
      (=>
        (> ($Hp.get_$Perm s1 x) 0.0)
        (= ($Hp.get_$T$ h1 x) ($Hp.get_$T$ h2 x)))
      :pattern (($Hp.get_$T$ h1 x) ($Hp.get_$T$ h2 x))
      :qid |qp.$SnapTo$Heap<$FLD$>-ext-inner|
      )))
    (= ($SortWrappers.$Heap<$FLD$>To$Snap h1 s1) ($SortWrappers.$Heap<$FLD$>To$Snap h2 s2))
    )
    :pattern (($SortWrappers.$Heap<$FLD$>To$Snap h1 s1) ($SortWrappers.$Heap<$FLD$>To$Snap h2 s2))
    :qid |qp.$SnapTo$Heap<$FLD$>-ext|
    )))