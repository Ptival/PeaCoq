Theorem many_diffs : forall n,
  n + n + n + n + n + n + n + n + n + n + n = 0 ->
  n = 0 ->
  n + n + n + n + n + n + n + n + n + n + n = 0.
Proof.
  intros. rewrite -> H0 in *; clear H0; pose proof I as I.
