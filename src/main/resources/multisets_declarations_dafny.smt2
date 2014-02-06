; These declarations correspond to Dafny's multiset axiomatisation from 2013-06-27.
; They depend on the set axiomatisation due to the fromSet-function.



; 2013-07-24 Malte: Ignored for now. Not sure when it should be used.
;function $IsGoodMultiSet<T>(ms: MultiSet T): bool;

(declare-fun $Multiset.count ($Multiset<$S$> $S$) Int)

;function MultiSet#Card<T>(MultiSet T): int;
(declare-fun $Multiset.card ($Multiset<$S$>) Int)

;function MultiSet#Empty<T>(): MultiSet T;
(declare-fun $Multiset.empty<$S$> () $Multiset<$S$>)

;function MultiSet#Singleton<T>(T): MultiSet T;
(declare-fun $Multiset.singleton ($S$) $Multiset<$S$>)

;function MultiSet#UnionOne<T>(MultiSet T, T): MultiSet T;
(declare-fun $Multiset.add ($Multiset<$S$> $S$) $Multiset<$S$>)

;function MultiSet#Union<T>(MultiSet T, MultiSet T): MultiSet T;
(declare-fun $Multiset.union ($Multiset<$S$> $Multiset<$S$>) $Multiset<$S$>)

;function MultiSet#Intersection<T>(MultiSet T, MultiSet T): MultiSet T;
(declare-fun $Multiset.intersection ($Multiset<$S$> $Multiset<$S$>) $Multiset<$S$>)

;function MultiSet#Difference<T>(MultiSet T, MultiSet T): MultiSet T;
(declare-fun $Multiset.difference ($Multiset<$S$> $Multiset<$S$>) $Multiset<$S$>)

;function MultiSet#Subset<T>(MultiSet T, MultiSet T): bool;
(declare-fun $Multiset.subset ($Multiset<$S$> $Multiset<$S$>) Bool)

;function MultiSet#Equal<T>(MultiSet T, MultiSet T): bool;
(declare-fun $Multiset.eq ($Multiset<$S$> $Multiset<$S$>) Bool)

;function MultiSet#Disjoint<T>(MultiSet T, MultiSet T): bool;
(declare-fun $Multiset.disjoint ($Multiset<$S$> $Multiset<$S$>) Bool)

;function MultiSet#FromSet<T>(Set T): MultiSet T;
(declare-fun $Multiset.fromSet ($Set<$S$>) $Multiset<$S$>)
