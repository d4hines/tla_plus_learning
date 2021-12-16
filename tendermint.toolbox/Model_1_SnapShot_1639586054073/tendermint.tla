----------------------------- MODULE tendermint -----------------------------

EXTENDS Integers, Sequences

(*--algorithm tendermint

variables
  good_nodes = 1..1;
  \*bad_nodes = {4};
  nodes = good_nodes \* \cup bad_nodes
define
end define

macro MyFirstMacro(height)
begin
  height := 1
end macro;

process Node \in nodes
  variables
    height = 0;
    (*round = 0;
    step \in {"propose", "prevote", "precommit"};
    decision = <<>>;
    lockedValue = "nil";
    lockedRound = -1;
    validValue = "nil";
    validRound = -1;*)
begin
  MyFirstTransition:
    MyFirstMacro(height);
  skip;
end process

end algorithm;*)



\* BEGIN TRANSLATION (chksum(pcal) = "96880fc2" /\ chksum(tla) = "3f761749")
VARIABLES good_nodes, nodes, pc, height

vars == << good_nodes, nodes, pc, height >>

ProcSet == (nodes)

Init == (* Global variables *)
        /\ good_nodes = 1..1
        /\ nodes = good_nodes
        (* Process Node *)
        /\ height = [self \in nodes |-> 0]
        /\ pc = [self \in ProcSet |-> "MyFirstTransition"]

MyFirstTransition(self) == /\ pc[self] = "MyFirstTransition"
                           /\ height' = [height EXCEPT ![self] = 1]
                           /\ TRUE
                           /\ pc' = [pc EXCEPT ![self] = "Done"]
                           /\ UNCHANGED << good_nodes, nodes >>

Node(self) == MyFirstTransition(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in nodes: Node(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

DummyInvariant == TRUE

=============================================================================
\* Modification History
\* Last modified Wed Dec 15 11:34:10 EST 2021 by d4hines
\* Created Wed Dec 15 10:35:08 EST 2021 by d4hines
