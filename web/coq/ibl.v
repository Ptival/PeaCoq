Require Import ZArith.

Definition divides (d n : Z) := exists k, (d * k = n)%Z.

Definition even n := divides n 2.

Definition odd n := ~ (even n).

Theorem interaction_with_sign_A_even : forall n, even n -> even (- n).
Proof.
  intros.
  destruct H.
  unfold even.
  unfold divides.
  exists (- x)%Z.
  rewrite -> Z.mul_opp_opp.
  exact H.
Qed.

Theorem interaction_with_sign_A_odd : forall n, odd n -> odd (- n).
Proof.
  intros.
  unfold odd in *.
  intro.
  apply H.
  clear H.
  destruct H0.
  unfold even.
  unfold divides.
  exists (- x)%Z.
  rewrite <- Z.mul_opp_comm.
  exact H.
Qed.

Theorem interaction_with_sign_B_1 :
  forall d a,
  divides (- d) a -> divides d a.
Proof.
  intros.
  unfold divides in *.
  destruct H.
  exists (- x)%Z.
  rewrite <- Z.mul_opp_comm.
  exact H.
Qed.

Theorem interaction_with_sign_B_2 :
  forall d a,
  divides d a -> divides d (- a).
Proof.
  intros.
  unfold divides in *.
  destruct H.
  exists (- x)%Z.
  rewrite -> Z.mul_opp_r.
  apply Z.opp_inj_wd.
  exact H.
Qed.

Theorem interaction_with_sign_B_3 :
  forall d a,
  divides d a -> divides d (Z.abs a).
Proof.
  intros.
  unfold divides in *.
  destruct H.
  unfold Z.abs.
  exists (- x)%Z.
  rewrite -> Z.mul_opp_r.
  apply Z.opp_inj_wd.
  exact H.
Qed.


