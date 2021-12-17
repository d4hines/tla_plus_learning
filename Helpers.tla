------------------------------ MODULE Helpers ------------------------------
\* Helpers for calculating the majority value of a function
EXTENDS Naturals, Integers, FiniteSets

Quantify(S, P(_)) ==
  Cardinality({s \in S : P(s)})
  
Codomain(f) == { f[x] : x \in DOMAIN f }

CountsOfCodomain(f) ==
  [ x \in Codomain(f) |->
    Quantify(DOMAIN f, LAMBDA y : f[y] = x) ]

Majority(f) ==
  LET counts == CountsOfCodomain(f) IN
  CHOOSE x \in Codomain(f) : ~(\E y : counts[y] > counts[x])
  
(* 
Gets the set of all possible values that f maps to.
essential the "opposite" of DOMAIN. Uses a set comprehension-map.
*)
Range(f) == { f[x] : x \in DOMAIN f }

OrderSet(set) == CHOOSE seq \in [1..Cardinality(set) -> set]: Range(seq) = set

=============================================================================
\* Modification History
\* Last modified Fri Dec 17 16:55:34 EST 2021 by d4hines
\* Created Fri Dec 17 16:17:58 EST 2021 by d4hines
