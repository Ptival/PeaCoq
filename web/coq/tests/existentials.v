Inductive Fake : nat -> nat -> Prop :=
| Make : forall a b,
  42 = a ->
  a + b = 43 ->
  a - b = 41 ->
  Fake a b
.

Theorem test_exists : exists c, exists d, Fake c d.
(*
econstructor. econstructor. split.
  { reflexivity. }
  { admit. }
*)
