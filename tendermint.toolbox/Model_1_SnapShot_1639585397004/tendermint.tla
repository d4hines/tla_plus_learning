----------------------------- MODULE tendermint -----------------------------

EXTENDS Integers, Sequences

(*--algorithm tendermint

variables
  good_nodes = 1..3;
  bad_nodes = {4};
  nodes = good_nodes \cup bad_nodes
define
end define

macro MyFirstMacro(height)
begin
  height := 1
end macro;

process Node \in nodes
  variables
    height = 0;
    round = 0;
    step \in {"propose", "prevote", "precommit"};
    decision = <<>>;
    lockedValue = "nil";
    lockedRound = -1;
    validValue = "nil";
    validRound = -1;
begin
  Do:
    MyFirstMacro(height);
  skip;
end process

end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "97998bf2" /\ chksum(tla) = "bf5fab18")
VARIABLES good_nodes, bad_nodes, nodes, pc, height, round, step, decision, 
          lockedValue, lockedRound, validValue, validRound

vars == << good_nodes, bad_nodes, nodes, pc, height, round, step, decision, 
           lockedValue, lockedRound, validValue, validRound >>

ProcSet == (nodes)

Init == (* Global variables *)
        /\ good_nodes = 1..3
        /\ bad_nodes = {4}
        /\ nodes = (good_nodes \cup bad_nodes)
        (* Process Node *)
        /\ height = [self \in nodes |-> 0]
        /\ round = [self \in nodes |-> 0]
        /\ step \in [nodes -> {"propose", "prevote", "precommit"}]
        /\ decision = [self \in nodes |-> <<>>]
        /\ lockedValue = [self \in nodes |-> "nil"]
        /\ lockedRound = [self \in nodes |-> -1]
        /\ validValue = [self \in nodes |-> "nil"]
        /\ validRound = [self \in nodes |-> -1]
        /\ pc = [self \in ProcSet |-> "Do"]

Do(self) == /\ pc[self] = "Do"
            /\ height' = [height EXCEPT ![self] = 1]
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "Done"]
            /\ UNCHANGED << good_nodes, bad_nodes, nodes, round, step, 
                            decision, lockedValue, lockedRound, validValue, 
                            validRound >>

Node(self) == Do(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in nodes: Node(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Wed Dec 15 11:23:13 EST 2021 by d4hines
\* Created Wed Dec 15 10:35:08 EST 2021 by d4hines