; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The definitions are parametric
;   - $FLD$ is a Silver field name
;   - $S$ is the sort corresponding to the type of the field
;   - $T$ is the sanitized name of the sort corresponding to the type of the field


(declare-fun $SortWrappers.$Heap<$FLD$>To$Snap ($Hp<$T$> $Hp<$Perm>) $Snap)

(declare-fun $SortWrappers.$SnapTo$Heap<$FLD$> ($Snap) $Hp<$T$>)
