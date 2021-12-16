---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_163957865523050000 == 
1 + 2
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_163957865523050000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_163957865523051000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_163957865523052000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Wed Dec 15 09:30:55 EST 2021 by d4hines
