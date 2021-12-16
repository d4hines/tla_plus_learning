---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_163957873122762000 == 
1..3
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_163957873122762000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_163957873122763000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_163957873122764000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Wed Dec 15 09:32:11 EST 2021 by d4hines
