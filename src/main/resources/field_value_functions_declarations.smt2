; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The definitions are parametric
;   - $FLD$ is a Silver field name
;   - $S$ is the sort corresponding to the type of the field

(declare-fun $FVF.domain_$FLD$ ($FVF<$S$>) Set<$Ref>)
(declare-fun $FVF.lookup_$FLD$ ($FVF<$S$> $Ref) $S$)
(declare-fun $FVF.after_$FLD$ ($FVF<$S$> $FVF<$S$>) Bool)
(declare-const $fvfTOP_$FLD$ $FVF<$S$>)
