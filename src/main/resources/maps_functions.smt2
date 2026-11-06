; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The definitions are parametric
;   - $S$ is the sort corresponding to the type of the field
;   - $T$ is the sanitized name of the sort corresponding to the type of the field


(declare-fun $Hp.singleton_$T$ ($Ref $S$) $Hp<$T$>)
(declare-fun $Hp.get_$T$ ($Hp<$T$> $Ref) $S$)
(declare-fun $Hp.update_$T$ ($Hp<$T$> $Ref $S$) $Hp<$T$>)
(declare-fun $Hp.identicalOnKnown_$T$ ($Hp<$T$> $Hp<$T$> $Hp<$Perm>) Bool)
(declare-fun $Hp.merge_$T$ ($Hp<$T$> $Hp<$Perm> $Hp<$T$> $Hp<$Perm>) $Hp<$T$>)
(declare-fun $Hp.merge_single_$T$ ($Hp<$T$> $Hp<$Perm> $Ref $S$) $Hp<$T$>)
(declare-fun $Hp.overlap_$T$ ($Hp<$T$> $Hp<$Perm> $Hp<$T$> $Hp<$Perm>) Bool)
(declare-const $Hp.default_$T$ $Hp<$T$>)
