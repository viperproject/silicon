; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

(assert (forall ((r $Ref)) (!
      (=
        ($Mp.get_$Perm $Mp.zeroMask r)
        $Perm.No)
    :pattern (($Mp.get_$Perm $Mp.zeroMask r))
    :qid |qp.$Mp.zeroMask-def|
    )))