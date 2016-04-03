
Fixpoint pow a b :=
  match b with
  | O => 1
  | S n => a * pow a n
  end.

Notation "a ^ b" := (pow a b).

Theorem testing_pow : forall (x y : nat), x ^ 2 = x * x.
Proof.
  intros. simpl. induction x.
  + simpl. reflexivity.
  + simpl in *. 



