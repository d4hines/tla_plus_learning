---- MODULE MC ----
EXTENDS wire, TLC

\* Constant expression definition @modelExpressionEval
const_expr_163957866807756000 == 
1 = 2
----

\* Constant expression ASSUME statement @modelExpressionEval
ASSUME PrintT(<<"$!@$!@$!@$!@$!",const_expr_163957866807756000>>)
----

\* INIT definition @modelBehaviorNoSpec:0
init_163957866807757000 ==
FALSE/\people = 0
----
\* NEXT definition @modelBehaviorNoSpec:0
next_163957866807758000 ==
FALSE/\people' = people
----
=============================================================================
\* Modification History
\* Created Wed Dec 15 09:31:08 EST 2021 by d4hines
