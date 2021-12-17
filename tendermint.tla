----------------------------- MODULE tendermint -----------------------------
EXTENDS Naturals, Integers

(*--algorithm tendermint

variables
 Values = { "a", "b", "c" };
 processes = 1..3;
 proposer \in [ Nat \X Nat -> processes ];  
define
nil_value == CHOOSE x : x \notin Values

end define

procedure StartRound(p, r)
variable proposal
begin
  StartRound:
    round[p] := r;
    step[p] := "propose";
    if proposer[<<h[p], round[p]>>] = p then
      if validValue[p] /= nil_value then
        proposal := validValue[p];
      else
        proposal :=  CHOOSE x \in Values : TRUE
      end if
    else
      skip;
    end if
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
begin
  Start:
    skip;
end process
end algorithm;*)



=============================================================================

\* Modification History
\* Last modified Fri Dec 17 12:35:11 EST 2021 by d4hines
\* Created Wed Dec 15 10:35:08 EST 2021 by d4hines 
