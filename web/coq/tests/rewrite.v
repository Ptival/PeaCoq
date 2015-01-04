
(* notree *)
Theorem plus_0_r : forall n, n + 0 = n.
Proof.
  induction n.
  { reflexivity. }
  { simpl. rewrite IHn. reflexivity. }
Qed.

(* After intros, you should be able to rewrite -> plus_0_r *)
Theorem rewriter : forall n m, (n + 0) + m = n + m.

