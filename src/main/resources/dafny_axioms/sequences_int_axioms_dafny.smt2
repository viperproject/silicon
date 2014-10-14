; These axioms are derived from the corresponding axioms of the prelude of
; Microsoft's Dafny tool by translating them from Boogie to SMT-LIB. Visit
; http://dafny.codeplex.com for more information about the Dafny verifier.
;
; A snapshot of the corresponding DafnyPrelude.bpl file including the date
; of the version and its copyright notices can be found in this directory.
;
; This file is subject to the terms of the Microsoft Public License
; (Ms-PL). A copy of the Ms-PL is provided in this directory (LICENCE.TXT)



; Axioms specific to integer sequences

(assert (forall ((min Int) (max Int) ) (! (and
  (=> (< min max) (= ($Seq.length ($Seq.range min max)) (- max min)))
  (=> (<= max min) (= ($Seq.length ($Seq.range min max)) 0)))
   :pattern ( ($Seq.length ($Seq.range min max)))
  )))
(assert (forall ((min Int) (max Int) (j Int) ) (! (=> (and
  (<= 0 j)
  (< j (- max min))) (= ($Seq.index ($Seq.range min max) j) (+ min j)))
   :pattern ( ($Seq.index ($Seq.range min max) j))
  )))
(assert (forall ((min Int) (max Int) (v Int) ) (! (and
  (=> ($Seq.contains ($Seq.range min max) v) (and
  (<= min v)
  (< v max)))
  (=> (and
  (<= min v)
  (< v max)) ($Seq.contains ($Seq.range min max) v)))
   :pattern ( ($Seq.contains ($Seq.range min max) v))
  )))
