Require Import Coq.Arith.Plus.

Fixpoint pow a b :=
  match b with
  | O => 1
  | S c => a * (pow a c)
  end.

Notation "a ^ b" := (pow a b).

Theorem testing : forall a b x y z,
  x ^ (y + z) = x ^ (z + y) /\ (a && b)%bool = (b && a)%bool.
Proof.
  intros. split.
  + rewrite plus_comm. reflexivity.
  + rewrite Bool.andb_comm. reflexivity.
Qed.

(* Note: there is a bug in subterm highlighting here *)
Theorem test_nesting : forall x, x ^ x ^ x = x ^ x ^ x.

