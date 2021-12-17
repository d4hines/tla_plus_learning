----------------------------- MODULE await_test -----------------------------

(*--algorithm tendermint

variables
 Values = { "a", "b", "c" };
 processes = 1..3;
 proposer \in [ Nat \X Nat -> processes ];  
define
nil_value == CHOOSE x : x \notin Values
nil_process == CHOOSE x : x \notin processes
end define

procedure Broadcast(step_type, h, broadcast_round, v, valid_round)
variables
  remaining = processes;
  message = <<step_type, h, broadcast_round, v, valid_round>>;
  p = nil_process
begin
  Broadcast:
    while remaining /= {} do
      p := CHOOSE x \in processes : TRUE;
      received_messages[p] := received_messages[p] \union {message};
      remaining := remaining \ {p}
    end while
end procedure

procedure StartRound(p,r)
variables proposal
begin
    StartRound:
        round[p] := r;
        step[p] := "propose";
        if proposer[<<h[p], round[p]>>] = p then
           if validValue[p] /= nil_value then
             proposal := validValue[p]
           else
             proposal :=  CHOOSE x \in Values : TRUE; \* Get a random value, equivalent to getValue() in paper
           end if;
           call Broadcast("PROPOSAL", h[p], round[p], proposal, validRound[p])
        else
          \* schedule
          skip;
        end if;
end procedure

\* TODO: verify we have the correct notion of fairness
fair+ process p \in processes
  variables
    h = 0;
    round = 0;
    step \in { "propose", "prevote", "precommit"};
    decision = nil_value;
    lockedValue = nil_value;
    lockedRound = -1;
    validValue = nil_value;
    validRound = -1;
    received_messages = {}
begin
  Start:
    skip;
end process
end algorithm;*)
\* BEGIN TRANSLATION (chksum(pcal) = "fd8b786e" /\ chksum(tla) = "7e31c8f6")
\* Label Broadcast of procedure Broadcast at line 21 col 5 changed to Broadcast_
\* Label StartRound of procedure StartRound at line 32 col 9 changed to StartRound_
\* Process p at line 48 col 7 changed to p_
\* Process variable h of process p at line 50 col 5 changed to h_
\* Procedure variable p of procedure Broadcast at line 18 col 3 changed to p_B
CONSTANT defaultInitValue
VARIABLES Values, processes, proposer, pc, stack

(* define statement *)
nil_value == CHOOSE x : x \notin Values
nil_process == CHOOSE x : x \notin processes

VARIABLES step_type, h, broadcast_round, v, valid_round, remaining, message, 
          p_B, p, r, proposal, h_, round, step, decision, lockedValue, 
          lockedRound, validValue, validRound, received_messages

vars == << Values, processes, proposer, pc, stack, step_type, h, 
           broadcast_round, v, valid_round, remaining, message, p_B, p, r, 
           proposal, h_, round, step, decision, lockedValue, lockedRound, 
           validValue, validRound, received_messages >>

ProcSet == (processes)

Init == (* Global variables *)
        /\ Values = { "a", "b", "c" }
        /\ processes = 1..3
        /\ proposer \in [ Nat \X Nat -> processes ]
        (* Procedure Broadcast *)
        /\ step_type = [ self \in ProcSet |-> defaultInitValue]
        /\ h = [ self \in ProcSet |-> defaultInitValue]
        /\ broadcast_round = [ self \in ProcSet |-> defaultInitValue]
        /\ v = [ self \in ProcSet |-> defaultInitValue]
        /\ valid_round = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining = [ self \in ProcSet |-> processes]
        /\ message = [ self \in ProcSet |-> <<step_type[self], h[self], broadcast_round[self], v[self], valid_round[self]>>]
        /\ p_B = [ self \in ProcSet |-> nil_process]
        (* Procedure StartRound *)
        /\ p = [ self \in ProcSet |-> defaultInitValue]
        /\ r = [ self \in ProcSet |-> defaultInitValue]
        /\ proposal = [ self \in ProcSet |-> defaultInitValue]
        (* Process p_ *)
        /\ h_ = [self \in processes |-> 0]
        /\ round = [self \in processes |-> 0]
        /\ step \in [processes -> { "propose", "prevote", "precommit"}]
        /\ decision = [self \in processes |-> nil_value]
        /\ lockedValue = [self \in processes |-> nil_value]
        /\ lockedRound = [self \in processes |-> -1]
        /\ validValue = [self \in processes |-> nil_value]
        /\ validRound = [self \in processes |-> -1]
        /\ received_messages = [self \in processes |-> {}]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Start"]

Broadcast_(self) == /\ pc[self] = "Broadcast_"
                    /\ IF remaining[self] /= {}
                          THEN /\ p_B' = [p_B EXCEPT ![self] = CHOOSE x \in processes : TRUE]
                               /\ received_messages' = [received_messages EXCEPT ![self][p_B'[self]] = received_messages[self][p_B'[self]] \union {message[self]}]
                               /\ remaining' = [remaining EXCEPT ![self] = remaining[self] \ {p_B'[self]}]
                               /\ pc' = [pc EXCEPT ![self] = "Broadcast_"]
                          ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                               /\ UNCHANGED << remaining, p_B, 
                                               received_messages >>
                    /\ UNCHANGED << Values, processes, proposer, stack, 
                                    step_type, h, broadcast_round, v, 
                                    valid_round, message, p, r, proposal, h_, 
                                    round, step, decision, lockedValue, 
                                    lockedRound, validValue, validRound >>

Broadcast(self) == Broadcast_(self)

StartRound_(self) == /\ pc[self] = "StartRound_"
                     /\ round' = [round EXCEPT ![self][p[self]] = r[self]]
                     /\ step' = [step EXCEPT ![self][p[self]] = "propose"]
                     /\ IF proposer[<<h[self][p[self]], round'[self][p[self]]>>] = p[self]
                           THEN /\ IF validValue[self][p[self]] /= nil_value
                                      THEN /\ proposal' = [proposal EXCEPT ![self] = validValue[self][p[self]]]
                                      ELSE /\ proposal' = [proposal EXCEPT ![self] = CHOOSE x \in Values : TRUE]
                                /\ /\ broadcast_round' = [broadcast_round EXCEPT ![self] = round'[self][p[self]]]
                                   /\ h' = [h EXCEPT ![self] = h[self][p[self]]]
                                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "Broadcast",
                                                                            pc        |->  "Error",
                                                                            remaining |->  remaining[self],
                                                                            message   |->  message[self],
                                                                            p_B       |->  p_B[self],
                                                                            step_type |->  step_type[self],
                                                                            h         |->  h[self],
                                                                            broadcast_round |->  broadcast_round[self],
                                                                            v         |->  v[self],
                                                                            valid_round |->  valid_round[self] ] >>
                                                                        \o stack[self]]
                                   /\ step_type' = [step_type EXCEPT ![self] = "PROPOSAL"]
                                   /\ v' = [v EXCEPT ![self] = proposal'[self]]
                                   /\ valid_round' = [valid_round EXCEPT ![self] = validRound[self][p[self]]]
                                /\ remaining' = [remaining EXCEPT ![self] = processes]
                                /\ message' = [message EXCEPT ![self] = <<step_type'[self], h'[self], broadcast_round'[self], v'[self], valid_round'[self]>>]
                                /\ p_B' = [p_B EXCEPT ![self] = nil_process]
                                /\ pc' = [pc EXCEPT ![self] = "Broadcast_"]
                           ELSE /\ TRUE
                                /\ pc' = [pc EXCEPT ![self] = "Error"]
                                /\ UNCHANGED << stack, step_type, h, 
                                                broadcast_round, v, 
                                                valid_round, remaining, 
                                                message, p_B, proposal >>
                     /\ UNCHANGED << Values, processes, proposer, p, r, h_, 
                                     decision, lockedValue, lockedRound, 
                                     validValue, validRound, received_messages >>

StartRound(self) == StartRound_(self)

Start(self) == /\ pc[self] = "Start"
               /\ TRUE
               /\ pc' = [pc EXCEPT ![self] = "Done"]
               /\ UNCHANGED << Values, processes, proposer, stack, step_type, 
                               h, broadcast_round, v, valid_round, remaining, 
                               message, p_B, p, r, proposal, h_, round, step, 
                               decision, lockedValue, lockedRound, validValue, 
                               validRound, received_messages >>

p_(self) == Start(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: Broadcast(self) \/ StartRound(self))
           \/ (\E self \in processes: p_(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in processes : SF_vars(p_(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

=============================================================================
\* Modification History
\* Last modified Fri Dec 17 13:23:28 EST 2021 by d4hines
\* Created Fri Dec 17 13:22:36 EST 2021 by d4hines
