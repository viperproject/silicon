; These declarations correspond to Dafny's set axiomatisation from 2013-06-27.

(declare-fun $Set.in ($S$ $Set<$S$>) Bool)

; function Set#Card<T>(Set T): int;
(declare-fun $Set.card ($Set<$S$>) Int)

; function Set#Empty<T>(): Set T;
(declare-fun $Set.empty<$S$> () $Set<$S$>)

; function Set#Singleton<T>(T): Set T;
(declare-fun $Set.singleton ($S$) $Set<$S$>)

; function Set#UnionOne<T>(Set T, T): Set T;
(declare-fun $Set.add ($Set<$S$> $S$) $Set<$S$>)

; function Set#Union<T>(Set T, Set T): Set T;
(declare-fun $Set.union ($Set<$S$> $Set<$S$>) $Set<$S$>)

; function Set#Intersection<T>(Set T, Set T): Set T;
(declare-fun $Set.intersection ($Set<$S$> $Set<$S$>) $Set<$S$>)

; function Set#Difference<T>(Set T, Set T): Set T;
(declare-fun $Set.difference ($Set<$S$> $Set<$S$>) $Set<$S$>)

; function Set#Subset<T>(Set T, Set T): bool;
(declare-fun $Set.subset ($Set<$S$> $Set<$S$>) Bool)

; function Set#Equal<T>(Set T, Set T): bool;
(declare-fun $Set.eq ($Set<$S$> $Set<$S$>) Bool)

; function Set#Disjoint<T>(Set T, Set T): bool;
(declare-fun $Set.disjoint ($Set<$S$> $Set<$S$>) Bool)
