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

(declare-fun $Seq.nil<$S$> () $Seq<$S$>)
(declare-fun $Seq.len ($Seq<$S$>) Int)
(declare-fun $Seq.elem ($S$) $Seq<$S$>)
; function Seq#Build<T>(s: Seq T, index: int, val: T, newLength: int) returns (Seq T);
(declare-fun $Seq.build ($Seq<$S$> Int $S$ Int) $Seq<$S$>)
; function Seq#Append<T>(Seq T, Seq T) returns (Seq T);
(declare-fun $Seq.con ($Seq<$S$> $Seq<$S$>) $Seq<$S$>)
; function Seq#Index<T>(Seq T, int) returns (T);
(declare-fun $Seq.at ($Seq<$S$> Int) $S$)
; function Seq#Contains<T>(Seq T, T) returns (bool);
(declare-fun $Seq.in ($Seq<$S$> $S$) Bool)
; function Seq#Equal<T>(Seq T, Seq T) returns (bool);
(declare-fun $Seq.eq ($Seq<$S$> $Seq<$S$>) Bool)
; function Seq#SameUntil<T>(Seq T, Seq T, int) returns (bool);
(declare-fun $Seq.sameUntil ($Seq<$S$> $Seq<$S$> Int) Bool)
; function Seq#Take<T>(s: Seq T, howMany: int) returns (Seq T);
(declare-fun $Seq.take ($Seq<$S$> Int) $Seq<$S$>)
; function Seq#Drop<T>(s: Seq T, howMany: int) returns (Seq T);
(declare-fun $Seq.drop ($Seq<$S$> Int) $Seq<$S$>)
; function Seq#Range(min: int, max: int) returns (Seq int);
; (declare-fun $Seq.rng (Int Int) Int)
; function Seq#Update<T>(Seq_ T, int, T): Seq_ T;
(declare-fun $Seq.update ($Seq<$S$> Int $S$) $Seq<$S$>)

(declare-fun $Multiset.fromSeq ($Seq<$S$>) $Multiset<$S$>)
