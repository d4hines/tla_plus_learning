---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_163957878109074000 == 
1..10 \ 4..6
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_163957878109074000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_163957878109075000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_163957878109076000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Wed Dec 15 09:33:01 EST 2021 by d4hines
