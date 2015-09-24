Require Import List.

Theorem test : forall T (l: list T), length l = length (rev l).
Proof. intros. induction l. simpl. reflexivity. simpl.