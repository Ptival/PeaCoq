Theorem t : forall n, n = 0 \/ n <> 0.
Proof. intros. destruct n. left. reflexivity. right. discriminate. Qed.
