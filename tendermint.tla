


----------------------------- MODULE tendermint -----------------------------

----------- MODULE IMod -----------

CONSTANT x, y

====================================
-----------------------------------------------------------------------------

EXTENDS Naturals, Integers, Sequences, IMod

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


=============================================================================

\* Modification History
\* Last modified Thu Dec 16 11:28:50 EST 2021 by d4hines
\* Created Wed Dec 15 10:35:08 EST 2021 by d4hines 