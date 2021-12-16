---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_163957875069268000 == 
2 \in 1..3
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_163957875069268000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_163957875069269000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_163957875069270000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Wed Dec 15 09:32:30 EST 2021 by d4hines
