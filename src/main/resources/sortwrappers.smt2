; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; Having only this axiom makes $SortWrappers.$S$To$Snap injective, which is
; necessary because Z3 otherwise won't know that an assumption such as
;   IntToSnap(x) = IntToSnap(y)
; implies that
;   x = y.
(assert (forall ((x $S$)) (!
    (= x ($SortWrappers.$SnapTo$S$($SortWrappers.$S$To$Snap x)))
    :pattern (($SortWrappers.$S$To$Snap x))
    :qid |$Snap.$S$|
    )))
;(assert (forall ((x $Snap)) (!
;    (= x ($SortWrappers.$S$To$Snap($SortWrappers.$SnapTo$S$ x)))
;    :pattern (($SortWrappers.$SnapTo$S$ x))
;    )))

; On several examples, e.g., AVLTree.iterative.sil, Z3 instantiates the sort
; wrapper axioms somewhat often. It might be possible to include the wrappers
; in the $Snap datatype by declaring the it as
;
;    (declare-datatypes () (($Snap
;      $Snap.unit
;      ($SortWrappers.$RefTo$Snap ($SortWrappers.$SnapTo$Ref $Ref))
;      ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
;
; Might be worth investigating some time.
;
; Another way of reducing the number of wrapper applications could be to
; overload the $Snap.combine function, which Z3 permits. E.g.,
;
;    (declare-datatypes () (($Snap
;      $Snap.unit
;      ($Snap.combine ($Snap.first $Ref) ($Snap.second $Snap))
;      ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))
