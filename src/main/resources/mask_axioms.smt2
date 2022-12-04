; This Source Code Form is subject to the terms of the Mozilla Public
; License, v. 2.0. If a copy of the MPL was not distributed with this
; file, You can obtain one at http://mozilla.org/MPL/2.0/.

(assert (forall ((r $Ref)) (!
      (=
        ($Hp.get_$Perm $Hp.zeroMask r)
        $Perm.No)
    :pattern (($Hp.get_$Perm $Hp.zeroMask r))
    :qid |qp.$Hp.zeroMask-def|
    )))