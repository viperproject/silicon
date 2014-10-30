; These axioms are derived from the corresponding axioms of the prelude of
; Microsoft's Dafny tool by translating them from Boogie to SMT-LIB. Visit
; http://dafny.codeplex.com for more information about the Dafny verifier.
;
; A snapshot of the corresponding DafnyPrelude.bpl file including the date
; of the version and its copyright notices can be found in this directory.
;
; This file is subject to the terms of the Microsoft Public License
; (Ms-PL). A copy of the Ms-PL is provided in this directory (LICENCE.TXT)



(declare-fun $Set.in ($S$ $Set<$S$>) Bool)
(declare-fun $Set.card ($Set<$S$>) Int)
(declare-fun $Set.empty<$S$> () $Set<$S$>)
(declare-fun $Set.singleton ($S$) $Set<$S$>)
(declare-fun $Set.unionone ($Set<$S$> $S$) $Set<$S$>)
(declare-fun $Set.union ($Set<$S$> $Set<$S$>) $Set<$S$>)
(declare-fun $Set.disjoint ($Set<$S$> $Set<$S$>) Bool)
(declare-fun $Set.difference ($Set<$S$> $Set<$S$>) $Set<$S$>)
(declare-fun $Set.intersection ($Set<$S$> $Set<$S$>) $Set<$S$>)
(declare-fun $Set.subset ($Set<$S$> $Set<$S$>) Bool)
(declare-fun $Set.equal ($Set<$S$> $Set<$S$>) Bool)
