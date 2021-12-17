-------------------------------- MODULE SimpleConsensus --------------------------------

EXTENDS Naturals, Integers, Sequences, FiniteSets
----------------------------------------------------------------------------------------
\* Helpers for calculating the majority value of a function

Quantify(S, P(_)) ==
  Cardinality({s \in S : P(s)})
  
Codomain(f) == { f[x] : x \in DOMAIN f }

CountsOfCodomain(f) ==
  [ x \in Codomain(f) |->
    Quantify(DOMAIN f, LAMBDA y : f[y] = x) ]

Majority(f) ==
  LET counts == CountsOfCodomain(f) IN
  CHOOSE x \in Codomain(f) : ~(\E y : counts[y] > counts[x])
  
----------------------------------------------------------------------------------------

CONSTANTS s,t

ASSUME s > (3 * t)
ASSUME s >= 0
ASSUME (s + t) % 2 = 1

(*--algorithm simpleconsensus

variables
  bad_nodes = CHOOSE bad_set \in (SUBSET nodes) : Cardinality(bad_set) = t;
  good_nodes = nodes \ bad_nodes;
  initial_value \in [ nodes -> BOOLEAN ];
  m = [ n \in nodes |-> "nil" ];
define

nodes == 0..(s+t)

end define

(*procedure BroadcastPhase1(sender, value)
variables
    i = 0;
begin
  BroadcastPhase1:
    while i <= Cardinality(nodes) do
      r[i][sender] := value
    end while
end procedure*)

(*procedure BroadcastPhase2(sender, value)
variables
    i = 0;
begin
  BroadcastPhase2:
    m[sender] := value
end procedure*)

fair+ process p \in nodes
  variables
    k = 1; \* round number
    d = initial_value[self]; \* Current value of bit for this node
    \*r = [ n \in nodes |-> "nil" ]; \* the map of nodes to values recieved in phase 1 from those nodes
begin
  Phase1:
    d := TRUE;
    skip;
    \*call BroadcastPhase1(self, d);
  (*Phase2:
    await ~(\E n \in nodes : r[n] = "nil");
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

\* BEGIN TRANSLATION (chksum(pcal) = "2b539873" /\ chksum(tla) = "1b033c8f")
VARIABLES bad_nodes, good_nodes, initial_value, m, pc

(* define statement *)
nodes == 0..(s+t)

VARIABLES k, d

vars == << bad_nodes, good_nodes, initial_value, m, pc, k, d >>

ProcSet == (nodes)

Init == (* Global variables *)
        /\ bad_nodes = (CHOOSE bad_set \in (SUBSET nodes) : Cardinality(bad_set) = t)
        /\ good_nodes = nodes \ bad_nodes
        /\ initial_value \in [ nodes -> BOOLEAN ]
        /\ m = [ n \in nodes |-> "nil" ]
        (* Process p *)
        /\ k = [self \in nodes |-> 1]
        /\ d = [self \in nodes |-> initial_value[self]]
        /\ pc = [self \in ProcSet |-> "Phase1"]

Phase1(self) == /\ pc[self] = "Phase1"
                /\ d' = [d EXCEPT ![self] = TRUE]
                /\ TRUE
                /\ pc' = [pc EXCEPT ![self] = "Done"]
                /\ UNCHANGED << bad_nodes, good_nodes, initial_value, m, k >>

p(self) == Phase1(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == (\E self \in nodes: p(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in nodes : SF_vars(p(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Agree(b) == \A g \in good_nodes: d[g] = b

AgreementSpec == \E b \in BOOLEAN : <>[]Agree(b) 

ValiditySpec == \E b \in BOOLEAN : Init /\ Agree(b) => <>[]Agree(b)

=============================================================================
\* Modification History
\* Last modified Fri Dec 17 10:34:38 EST 2021 by d4hines
\* Created Thu Dec 16 14:59:47 EST 2021 by d4hines
