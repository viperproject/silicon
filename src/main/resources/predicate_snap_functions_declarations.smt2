; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The definitions are parametric
;   - $PRD$ is a Silver predicate name
;   - $S$ is the sort corresponding to the type of the predicate arguments

(declare-fun $PSF.domain_$PRD$ ($PSF<$S$>) Set<$Snap>)
(declare-fun $PSF.lookup_$PRD$ ($PSF<$S$> $Snap) $S$)
(declare-fun $PSF.after_$PRD$ ($PSF<$S$> $PSF<$S$>) Bool)
(declare-const $psfTOP_$PRD$ $PSF<$S$>)
