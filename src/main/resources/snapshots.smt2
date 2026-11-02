; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; Requires Z3 >= 4.3.2

; ATTENTION: Continuing multi-line statements must be indented with at least
;            one tab or two spaces. All other lines must not start with tabs
;            or more than one space.

; --- Snapshots ---

; Emitted directly after the $Snap datatype (see DefaultMainVerifier).

(declare-const $Snap.null $Snap) ; hack

(declare-fun internalCondFrame (Bool $Snap $Snap) $Snap)
(assert (forall ((cnd Bool) (frst $Snap) (scnd $Snap)) (!
    (= (internalCondFrame cnd frst scnd) (ite cnd frst scnd))
    :pattern ((internalCondFrame cnd frst scnd)))))
