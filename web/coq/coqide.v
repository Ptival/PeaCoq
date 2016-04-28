Require Import PeaCoq.PeaCoq.

Theorem test : 0 = 0 /\ 0 = 0.
Proof.
  + split.
    - pose proof I.
      PeaCoqGetContext.