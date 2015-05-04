Require Import List.
Import ListNotations.

Theorem test : forall (n : nat) l1 l2, (n :: l1) ++ l2 = n :: (l1 ++ l2).
Proof.
