; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

; Requires Z3 >= 4.3.2

; ATTENTION: Continuing multi-line statements must be indented with at least
;            one tab or two spaces. All other lines must not start with tabs
;            or more than one space.

; --- Snapshots ---

(declare-datatypes () ((
    $Snap ($Snap.unit)
    ($Snap.combine ($Snap.first $Snap) ($Snap.second $Snap)))))

; --- References ---

(declare-sort $Ref 0)
(declare-const $Ref.null $Ref)

; --- Permissions ---

(define-sort $Perm () Real)

(define-const $Perm.Write $Perm 1.0)
(define-const $Perm.No $Perm 0.0)

(define-fun $Perm.isValidVar ((p $Perm)) Bool
	(<= $Perm.No p))

(define-fun $Perm.isReadVar ((p $Perm) (ub $Perm)) Bool
    (and ($Perm.isValidVar p)
         (not (= p $Perm.No))
         (< p $Perm.Write)))

; min function for permissions
(define-fun $Perm.min ((p1 $Perm) (p2 $Perm)) Real
    (ite (<= p1 p2) p1 p2))

; --- Sort wrappers ---

; Sort wrappers are no longer part of the static preamble. Instead, they are
; emitted as part of the program-specific preamble.

; --- Math ---

;function Math#min(a: int, b: int): int;
(define-fun $Math.min ((a Int) (b Int)) Int
    (ite (<= a b) a b))

;function Math#clip(a: int): int;
(define-fun $Math.clip ((a Int)) Int
    (ite (< a 0) 0 a))

; --- End static preamble ---

; (get-proof "stdout")
; (get-info :all-statistics)

; (push)
; (check-sat)
; (pop)
