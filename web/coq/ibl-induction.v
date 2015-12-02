Require Import ZArith.

Open Scope Z.

Fixpoint sum (f : Z -> Z) (n : nat) : Z :=
  match n with
  | O => f 0
  | S n => f (Z.of_nat (S n)) + (sum f n)
  end.

Lemma sum_decomposition :
  forall f n, sum f (S n) = sum f n + f (Z.of_nat (S n)).
Proof.
  intros f n.
  simpl.
  rewrite Z.add_comm.
  reflexivity.
Qed.

Axiom square_plus :
  forall a b,
  Z.square (a + b) = Z.square a + 2 * a * b + Z.square b.

Lemma Z_of_nat_succ : forall n, Z.of_nat (S n) = Z.of_nat n + 1.
Proof.
  intros n.
  rewrite -> Nat2Z.inj_succ.
  reflexivity.
Qed.

Theorem thm_1_9_Z :
  forall n,
  sum (fun n => 2 * n + 1) n = Z.square (Z.of_nat n + 1).
Proof.
  intros.
  induction n.
  + simpl.
    reflexivity.
  + rewrite sum_decomposition.
    rewrite IHn.
    rewrite square_plus.
    rewrite square_plus.
    rewrite Z_of_nat_succ.
    rewrite square_plus.
    rewrite Z.mul_1_r.
    rewrite Z.add_assoc.
    rewrite Z.mul_1_r.
    reflexivity.
Qed.
