Theorem theorem (x: nat) : forall (y: nat), True \/ True -> x = 0 \/ True.
Proof.
  intros. split. left.

