Theorem diffSample : forall n m,
  n + m = 0 ->
  n = 0 ->
  m + n = 0.
Proof.
  intros. rewrite -> H0 in *; clear H0; pose proof (eq_refl 2) as I.