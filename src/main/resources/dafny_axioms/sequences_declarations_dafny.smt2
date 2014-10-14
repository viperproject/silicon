; These axioms are derived from the corresponding axioms of the prelude of
; Microsoft's Dafny tool by translating them from Boogie to SMT-LIB. Visit
; http://dafny.codeplex.com for more information about the Dafny verifier.
;
; A snapshot of the corresponding DafnyPrelude.bpl file including the date
; of the version and its copyright notices can be found in this directory.
;
; This file is subject to the terms of the Microsoft Public License
; (Ms-PL). A copy of the Ms-PL is provided in this directory (LICENCE.TXT)



; General sequence declarations

(declare-fun $Seq.length ($Seq<$S$>) Int)
(declare-fun $Seq.empty<$S$> () $Seq<$S$>)
(declare-fun $Seq.singleton ($S$) $Seq<$S$>)
(declare-fun $Seq.build ($Seq<$S$> $S$) $Seq<$S$>)
(declare-fun $Seq.index ($Seq<$S$> Int) $S$)
(declare-fun $Seq.append ($Seq<$S$> $Seq<$S$>) $Seq<$S$>)
(declare-fun $Seq.update ($Seq<$S$> Int $S$) $Seq<$S$>)
(declare-fun $Seq.contains ($Seq<$S$> $S$) Bool)
(declare-fun $Seq.take ($Seq<$S$> Int) $Seq<$S$>)
(declare-fun $Seq.drop ($Seq<$S$> Int) $Seq<$S$>)
(declare-fun $Seq.equal ($Seq<$S$> $Seq<$S$>) Bool)
(declare-fun $Seq.sameuntil ($Seq<$S$> $Seq<$S$> Int) Bool)
