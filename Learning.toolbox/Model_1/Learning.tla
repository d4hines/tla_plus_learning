------------------------------ MODULE Learning ------------------------------
EXTENDS Naturals, Integers, Sequences

(*--algorithm wire
variables
  my_var = 0;
  my_other_var = 0;
define
end define
begin
DoA:
  my_var := 1;
DoC:
  my_var := 3;
DoB:
  my_var := 2;


end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "69b485b2" /\ chksum(tla) = "90455c70")
VARIABLES my_var, my_other_var, pc

vars == << my_var, my_other_var, pc >>

Init == (* Global variables *)
        /\ my_var = 0
        /\ my_other_var = 0
        /\ pc = "DoA"

DoA == /\ pc = "DoA"
       /\ my_var' = 1
       /\ pc' = "DoC"
       /\ UNCHANGED my_other_var

DoC == /\ pc = "DoC"
       /\ my_var' = 3
       /\ pc' = "DoB"
       /\ UNCHANGED my_other_var

DoB == /\ pc = "DoB"
       /\ my_var' = 2
       /\ pc' = "Done"
       /\ UNCHANGED my_other_var

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == DoA \/ DoC \/ DoB
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Dec 15 12:20:06 EST 2021 by d4hines
\* Created Wed Dec 15 08:44:34 EST 2021 by d4hines
