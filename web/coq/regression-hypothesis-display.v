From Coq Require Import ZArith.

Open Scope Z.

Theorem test: forall (d x y kx: Z) (dx: d * kx = x), False.
Proof.
  intros.