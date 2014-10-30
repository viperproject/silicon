; These axioms are derived from the corresponding axioms of the prelude of
; Microsoft's Dafny tool by translating them from Boogie to SMT-LIB. Visit
; http://dafny.codeplex.com for more information about the Dafny verifier.
;
; A snapshot of the corresponding DafnyPrelude.bpl file including the date
; of the version and its copyright notices can be found in this directory.
;
; This file is subject to the terms of the Microsoft Public License
; (Ms-PL). A copy of the Ms-PL is provided in this directory (LICENCE.TXT)



(declare-fun $Multiset.count ($Multiset<$S$> $S$) Int)
(declare-fun $Multiset.card ($Multiset<$S$>) Int)
(declare-fun $Multiset.empty<$S$> () $Multiset<$S$>)
(declare-fun $Multiset.singleton ($S$) $Multiset<$S$>)
(declare-fun $Multiset.unionone ($Multiset<$S$> $S$) $Multiset<$S$>)
(declare-fun $Multiset.union ($Multiset<$S$> $Multiset<$S$>) $Multiset<$S$>)
(declare-fun $Multiset.intersection ($Multiset<$S$> $Multiset<$S$>) $Multiset<$S$>)
(declare-fun $Multiset.difference ($Multiset<$S$> $Multiset<$S$>) $Multiset<$S$>)
(declare-fun $Multiset.subset ($Multiset<$S$> $Multiset<$S$>) Bool)
(declare-fun $Multiset.equal ($Multiset<$S$> $Multiset<$S$>) Bool)
(declare-fun $Multiset.disjoint ($Multiset<$S$> $Multiset<$S$>) Bool)
