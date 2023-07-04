; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

(declare-const $Hp.zeroMask $Hp<$Perm>)
(declare-fun $Hp.maskDomainIdentical ($Hp<$Perm> $Hp<$Perm>) Bool)
(declare-fun $Hp.maskSum ($Hp<$Perm> $Hp<$Perm>) $Hp<$Perm>)
(declare-fun $Hp.maskDiff ($Hp<$Perm> $Hp<$Perm>) $Hp<$Perm>)
(declare-fun $Hp.maskEq ($Hp<$Perm> $Hp<$Perm>) Bool)
(declare-fun $Hp.maskAdd ($Hp<$Perm> $Ref Real) $Hp<$Perm>)
(declare-fun $Hp.maskGood ($Hp<$Perm>) Bool)
(declare-fun $Hp.maskGoodField ($Hp<$Perm>) Bool)

