----------------------------- MODULE tendermint -----------------------------

EXTENDS Naturals, Integers, Sequences

(*--algorithm tendermint

variables
  Height = 1..100;
  Round = 1..100;
  Values = {"value1", "value2", "value3"};
  good_nodes = 1..1;
  \*bad_nodes = {4};
  Nodes = good_nodes; \* \cup bad_nodes
  proposer = [Height \X Round -> Nodes];
  getValue = [Height -> Values];
define

getValue() == CHOOSE x \in Values

end define



procedure StartRound(p, round)
variables proposal
begin
  StartRound:
    round_p := round;
    step_p := "propose";
    if proposer[<<height_p, round_p>>] == p then
      proposal := validValue_p
    else
      proposal := getValue()
    end
end procedure;

process p \in Nodes
  variables
    height_p = 0;
    round_p = 0;
    step_p \in {"propose", "prevote", "precommit"};
    decision_p = <<>>;
    lockedValue_p = "nil";
    lockedRound_p = -1;
    validValue_p = "nil";
    validRound_p = -1;
begin
  
  HandleMessage:
    call StartRound(p, height_p);
end process

end algorithm;*)



\* BEGIN TRANSLATION (chksum(pcal) = "8df979e8" /\ chksum(tla) = "1cb7aa9a")
\* Label StartRound of procedure StartRound at line 23 col 5 changed to StartRound_
\* Process p at line 32 col 1 changed to p_
CONSTANT defaultInitValue
VARIABLES Height, Round, Values, good_nodes, Nodes, proposer, getValue, pc, 
          stack, p, round, proposal, height_p, round_p, step_p, decision_p, 
          lockedValue_p, lockedRound_p, validValue_p, validRound_p

vars == << Height, Round, Values, good_nodes, Nodes, proposer, getValue, pc, 
           stack, p, round, proposal, height_p, round_p, step_p, decision_p, 
           lockedValue_p, lockedRound_p, validValue_p, validRound_p >>

ProcSet == (Nodes)

Init == (* Global variables *)
        /\ Height = 1..100
        /\ Round = 1..100
        /\ Values = {"value1", "value2", "value3"}
        /\ good_nodes = 1..1
        /\ Nodes = good_nodes
        /\ proposer = [Height \X Round -> Nodes]
        /\ getValue = [Height -> Values]
        (* Procedure StartRound *)
        /\ p = [ self \in ProcSet |-> defaultInitValue]
        /\ round = [ self \in ProcSet |-> defaultInitValue]
        /\ proposal = [ self \in ProcSet |-> defaultInitValue]
        (* Process p_ *)
        /\ height_p = [self \in Nodes |-> 0]
        /\ round_p = [self \in Nodes |-> 0]
        /\ step_p \in [Nodes -> {"propose", "prevote", "precommit"}]
        /\ decision_p = [self \in Nodes |-> <<>>]
        /\ lockedValue_p = [self \in Nodes |-> "nil"]
        /\ lockedRound_p = [self \in Nodes |-> -1]
        /\ validValue_p = [self \in Nodes |-> "nil"]
        /\ validRound_p = [self \in Nodes |-> -1]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "HandleMessage"]

StartRound_(self) == /\ pc[self] = "StartRound_"
                     /\ round_p' = [round_p EXCEPT ![self] = round[self]]
                     /\ step_p' = [step_p EXCEPT ![self] = "propose"]
                     /\ IF proposer[<<height_p[self], round_p'[self]>>] == p[self]
                           THEN /\ proposal' = [proposal EXCEPT ![self] = validValue_p[self]]
                           ELSE /\ proposal' = [proposal EXCEPT ![self] = CHOOSE s \in Values]
                     /\ pc' = [pc EXCEPT ![self] = "Error"]
                     /\ UNCHANGED << Height, Round, Values, good_nodes, Nodes, 
                                     proposer, getValue, stack, p, round, 
                                     height_p, decision_p, lockedValue_p, 
                                     lockedRound_p, validValue_p, validRound_p >>

StartRound(self) == StartRound_(self)

HandleMessage(self) == /\ pc[self] = "HandleMessage"
                       /\ /\ p' = [p EXCEPT ![self] = p[self]]
                          /\ round' = [round EXCEPT ![self] = height_p[self]]
                          /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "StartRound",
                                                                   pc        |->  "Done",
                                                                   proposal  |->  proposal[self],
                                                                   p         |->  p[self],
                                                                   round     |->  round[self] ] >>
                                                               \o stack[self]]
                       /\ proposal' = [proposal EXCEPT ![self] = defaultInitValue]
                       /\ pc' = [pc EXCEPT ![self] = "StartRound_"]
                       /\ UNCHANGED << Height, Round, Values, good_nodes, 
                                       Nodes, proposer, getValue, height_p, 
                                       round_p, step_p, decision_p, 
                                       lockedValue_p, lockedRound_p, 
                                       validValue_p, validRound_p >>

p_(self) == HandleMessage(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: StartRound(self))
           \/ (\E self \in Nodes: p_(self))
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

DummyInvariant == TRUE

=============================================================================
\* Modification History
\* Last modified Wed Dec 15 12:36:15 EST 2021 by d4hines
\* Created Wed Dec 15 10:35:08 EST 2021 by d4hines 