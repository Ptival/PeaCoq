Require Import ZArith.

Definition divides (d n : Z) := exists k, (d * k = n)%Z.

Notation "a | b" := (divides a b) (at level 50).

Definition even n := 2 | n.

Definition odd n := ~ (even n).

Theorem interaction_with_sign_A_even : forall n, even n -> even (- n).
Proof.
  intros n evenn.
  unfold even in *.
  unfold divides in *.
  destruct evenn as [kn evenn].
  exists (- kn)%Z.
  rewrite -> Z.mul_opp_r.
  apply Z.opp_inj_wd.
  assumption.
Qed.

Theorem interaction_with_sign_A_odd : forall n, odd n -> odd (- n).
Proof.
  intros n oddn.
  unfold odd in *.
  intros evenn.
  apply interaction_with_sign_A_even in evenn.
  rewrite Z.opp_involutive in evenn.
  contradiction.
Qed.

Theorem interaction_with_sign_B1 :
  forall d a,
  - d | a -> d | a.
Proof.
  intros d a da.
  unfold divides in *.
  destruct da as [kd da].
  exists (- kd)%Z.
  rewrite <- Z.mul_opp_comm.
  assumption.
Qed.

Theorem interaction_with_sign_B2 :
  forall d a,
  d | a -> d | - a.
Proof.
  intros d a da.
  apply interaction_with_sign_B1.
  unfold divides in *.
  destruct da as [kd da].
  exists kd.
  rewrite -> Z.mul_opp_l.
  apply Z.opp_inj_wd.
  assumption.
Qed.

Theorem interaction_with_sign_B3 :
  forall d a,
  d | a -> d | Z.abs a.
Proof.
  intros d a da.
  unfold Z.abs.
  destruct a.
  + assumption.
  + assumption.
  + unfold divides in *.
    destruct da as [kd da].
    exists (- kd)%Z.
    rewrite -> Z.mul_opp_r.
    apply Z.opp_inj_wd in da.
    rewrite -> Pos2Z.opp_neg in da.
    assumption.
Qed.

Theorem interaction_parity_addition_A1 :
  forall x y, even x -> even y -> even (x + y).
Proof.
  intros x y evenx eveny.
  unfold even in *.
  unfold divides in *.
  destruct evenx as [kx evenx].
  destruct eveny as [ky eveny].
  exists (kx + ky)%Z.
  rewrite Z.mul_add_distr_l.
  rewrite evenx.
  rewrite eveny.
  reflexivity.
Qed.

Theorem interaction_parity_addition_A2 :
  forall x y, even x -> even y -> even (x - y).
Proof.
  intros x y evenx eveny.
  apply interaction_with_sign_A_even in eveny.
  pose proof (interaction_parity_addition_A1 _ _ evenx eveny) as I.
  rewrite Z.add_opp_r in I.
  assumption.
Qed.

Lemma odd1 : odd 1.
Proof.
  unfold odd.
  intros even1.
  unfold even in *.
  unfold divides in *.
  destruct even1 as [k1 even1].
  destruct k1.
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

Theorem interaction_parity_addition_B1 :
  ~ (forall x y, odd x -> odd y -> odd (x + y)).
Proof.
  intros wrong.
  specialize (wrong _ _ odd1 odd1).
  contradiction wrong.
  exists 1%Z.
  reflexivity.
Qed.

Theorem interaction_parity_addition_B2 :
  ~ (forall x y, odd x -> odd y -> odd (x - y)).
Proof.
  intros wrong.
  specialize (wrong _ _ odd1 odd1).
  contradiction wrong.
  exists 0%Z.
  reflexivity.
Qed.

Theorem interaction_parity_addition_C :
  forall a b,
  even (a + b) <-> even (a - b).
Proof.
  intros a b.
  split.
  + intros evenab.
    destruct evenab as [kab evenab].
    exists (kab - b)%Z.
    rewrite Z.mul_sub_distr_l.
    rewrite evenab.
    rewrite <- Z.add_diag.
    rewrite -> Z.add_add_simpl_r_l.
    reflexivity.
  + intros evenab.
    destruct evenab as [kab evenab].
    exists (kab + b)%Z.
    rewrite Z.mul_add_distr_l.
    rewrite evenab.
    rewrite <- Z.add_diag.
    rewrite -> Z.sub_add_simpl_r_l.
    reflexivity.
Qed.

Theorem interaction_parity_addition_D1 :
  forall d x y,
  d | x -> d | y -> d | (x + y)%Z.
Proof.
  intros d x y dx dy.
  destruct dx as [kx dx].
  destruct dy as [ky dy].
  exists (kx + ky)%Z.
  rewrite Z.mul_add_distr_l.
  rewrite dx.
  rewrite dy.
  reflexivity.
Qed.


