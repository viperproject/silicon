; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; The definitions are parametric
;   - $S$ is the sort corresponding to the type of the field
;   - $T$ is the sanitized name of the sort corresponding to the type of the field




(declare-fun $Mp.get_$T$ ($Mp<$T$> $Ref) $S$)
(declare-fun $Mp.update_$T$ ($Mp<$T$> $Ref $S$) $Mp<$T$>)

(declare-fun $Mp.identicalOnKnown_$T$ ($Mp<$T$> $Mp<$T$> $Mp<$Perm>) Bool)







