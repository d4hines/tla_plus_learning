-------------------------------- MODULE SimpleConsensus --------------------------------

EXTENDS Naturals, Integers, Sequences, FiniteSets, Helpers
----------------------------------------------------------------------------------------

CONSTANTS good_nodes, bad_nodes, NULL

(*--algorithm simpleconsensus

variables
  initial_value \in [ nodes -> BOOLEAN];
  \* r : sender x receiver -> value
  \* A global map of values sent from sender to receiver in phase1
  r = [ pair \in nodes \X nodes |-> NULL ];
  \* m : sender x receiver -> value 
  \* A global map of the majority value sent from sender to receiver in phase2
  \* Of course, bad nodes can lie about this value.
  m = [ pair \in nodes \X nodes |-> NULL ];

define
s == Cardinality(good_nodes)
t == Cardinality(bad_nodes)
nodes == good_nodes \union bad_nodes
end define

procedure BroadcastPhase1(sender,v)
variables
  remaining = OrderSet(nodes);
  node_b = NULL;
begin
  BroacastPhase1:
  while remaining /= <<>> do
    node_b := Head(remaining);
    r[<<sender,node_b>>] := v;
    remaining := Tail(remaining);
  end while
end procedure

fair+ process p \in nodes
  variables
    k = 1; \* round number
    d = initial_value[self]; \* Current value of bit for this node
    remaining = nodes;
begin
  Phase1:
      \* "Broadcast" our value d by updating
      \* a global map
      call BroadcastPhase1(self, d);
  \*Phase2:
    \*await ~(\E n \in nodes : r[n] = "nil");
    \*skip;
  (*Phase2:
    \*call BroadcastPhase2(self,Majority(r));
    d := CHOOSE b \in BOOLEAN : TRUE; 
  (*Finalize:
    await ~(\E n \in nodes : m[n] = "nil");
      if CountsOfCodomain(r)[Majority(r)] >= s then
        d := m[self];
      else
        d := m[k];
      end if*)*)
end process

end algorithm;*)

\* BEGIN TRANSLATION (chksum(pcal) = "f0697b4e" /\ chksum(tla) = "aeb88e21")
\* Process variable remaining of process p at line 43 col 5 changed to remaining_
CONSTANT defaultInitValue
VARIABLES initial_value, r, m, pc, stack

(* define statement *)
s == Cardinality(good_nodes)
t == Cardinality(bad_nodes)
nodes == good_nodes \union bad_nodes

VARIABLES sender, v, remaining, node_b, k, d, remaining_

vars == << initial_value, r, m, pc, stack, sender, v, remaining, node_b, k, d, 
           remaining_ >>

ProcSet == (nodes)

Init == (* Global variables *)
        /\ initial_value \in [ nodes -> BOOLEAN]
        /\ r = [ pair \in nodes \X nodes |-> NULL ]
        /\ m = [ pair \in nodes \X nodes |-> NULL ]
        (* Procedure BroadcastPhase1 *)
        /\ sender = [ self \in ProcSet |-> defaultInitValue]
        /\ v = [ self \in ProcSet |-> defaultInitValue]
        /\ remaining = [ self \in ProcSet |-> OrderSet(nodes)]
        /\ node_b = [ self \in ProcSet |-> NULL]
        (* Process p *)
        /\ k = [self \in nodes |-> 1]
        /\ d = [self \in nodes |-> initial_value[self]]
        /\ remaining_ = [self \in nodes |-> nodes]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "Phase1"]

BroacastPhase1(self) == /\ pc[self] = "BroacastPhase1"
                        /\ IF remaining[self] /= <<>>
                              THEN /\ node_b' = [node_b EXCEPT ![self] = Head(remaining[self])]
                                   /\ r' = [r EXCEPT ![<<sender[self],node_b'[self]>>] = v[self]]
                                   /\ remaining' = [remaining EXCEPT ![self] = Tail(remaining[self])]
                                   /\ pc' = [pc EXCEPT ![self] = "BroacastPhase1"]
                              ELSE /\ pc' = [pc EXCEPT ![self] = "Error"]
                                   /\ UNCHANGED << r, remaining, node_b >>
                        /\ UNCHANGED << initial_value, m, stack, sender, v, k, 
                                        d, remaining_ >>

BroadcastPhase1(self) == BroacastPhase1(self)

Phase1(self) == /\ pc[self] = "Phase1"
                /\ /\ sender' = [sender EXCEPT ![self] = self]
                   /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "BroadcastPhase1",
                                                            pc        |->  "Phase2",
                                                            remaining |->  remaining[self],
                                                            node_b    |->  node_b[self],
                                                            sender    |->  sender[self],
                                                            v         |->  v[self] ] >>
                                                        \o stack[self]]
                   /\ v' = [v EXCEPT ![self] = d[self]]
                /\ remaining' = [remaining EXCEPT ![self] = OrderSet(nodes)]
                /\ node_b' = [node_b EXCEPT ![self] = NULL]
                /\ pc' = [pc EXCEPT ![self] = "BroacastPhase1"]
                /\ UNCHANGED << initial_value, r, m, k, d, remaining_ >>

Phase2(self) == /\ pc[self] = "Phase2"
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << initial_value, r, m, stack, sender, v, 
                                remaining, node_b, k, d, remaining_ >>

p(self) == Phase1(self) \/ Phase2(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in ProcSet: BroadcastPhase1(self))
           \/ (\E self \in nodes: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in nodes : SF_vars(p(self)) /\ SF_vars(BroadcastPhase1(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

----------------------------
\*  Consensus Properties

Agree(b) == \A g \in good_nodes: d[g] = b

AgreementSpec == \E b \in BOOLEAN : <>[]Agree(b) 

ValiditySpec == \A b \in BOOLEAN : Init /\ Agree(b) ~> []Agree(b)

=============================================================================
\* Modification History
\* Last modified Tue Dec 21 11:08:54 EST 2021 by d4hines
\* Created Thu Dec 16 14:59:47 EST 2021 by d4hines
