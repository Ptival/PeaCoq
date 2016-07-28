From Coq Require Import List.

Theorem concat_nil_right : forall l : list nat,
  app l nil = l.
Proof. intros. induction l. simpl. reflexivity. simpl. rewrite -> IHl. reflexivity.
  (* FILL IN HERE *)
Qed.