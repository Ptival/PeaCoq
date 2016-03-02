Theorem split_then_solve : (True /\ True) /\ True.
Proof.
  split.
  split.
  exact I.
  exact I.
  exact I.
Qed.