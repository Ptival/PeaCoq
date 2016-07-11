From Coq Require Import ZArith.

Open Scope Z.

Definition divides (d n : Z) := exists k, d * k = n.

Notation "a `| b" := (divides a b) (at level 50, only parsing).

Definition even n := 2 `| n.

Definition odd n := ~ (even n).

Theorem interaction_with_sign_A_even : forall n, even n -> even (- n).
Proof.
  intros n evenn.
  unfold even in *.
  unfold divides in *.
  destruct evenn as [kn evenn].
  exists (- kn).
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
  - d `| a -> d `| a.
Proof.
  intros d a da.
  unfold divides in *.
  destruct da as [kd da].
  exists (- kd).
  rewrite <- Z.mul_opp_comm.
  assumption.
Qed.

Theorem interaction_with_sign_B2 :
  forall d a,
  d `| a -> d `| - a.
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
  d `| a -> d `| Z.abs a.
Proof.
  intros d a da.
  unfold Z.abs.
  destruct a.
  + assumption.
  + assumption.
  + unfold divides in *.
    destruct da as [kd da].
    exists (- kd).
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
  exists (kx + ky).
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
  exists 1.
  reflexivity.
Qed.

Theorem interaction_parity_addition_B2 :
  ~ (forall x y, odd x -> odd y -> odd (x - y)).
Proof.
  intros wrong.
  specialize (wrong _ _ odd1 odd1).
  contradiction wrong.
  exists 0.
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
    exists (kab - b).
    rewrite Z.mul_sub_distr_l.
    rewrite evenab.
    rewrite <- Z.add_diag.
    rewrite -> Z.add_add_simpl_r_l.
    reflexivity.
  + intros evenab.
    destruct evenab as [kab evenab].
    exists (kab + b).
    rewrite Z.mul_add_distr_l.
    rewrite evenab.
    rewrite <- Z.add_diag.
    rewrite -> Z.sub_add_simpl_r_l.
    reflexivity.
Qed.

Theorem interaction_parity_addition_D1 :
  forall d x y,
  d `| x -> d `| y -> d `| (x + y).
Proof.
  intros d x y dx dy.
  destruct dx as [kx dx].
  destruct dy as [ky dy].
  exists (kx + ky).
  rewrite Z.mul_add_distr_l.
  rewrite dx.
  rewrite dy.
  reflexivity.
Qed.

Theorem interaction_parity_addition_D2 :
  forall d x y,
  d `| x -> d `| y -> d `| (x - y).
Proof.
  intros d x y dx dy.
  destruct dx as [kx dx].
  destruct dy as [ky dy].
  exists (kx - ky).
  rewrite Z.mul_sub_distr_l.
  rewrite dx.
  rewrite dy.
  reflexivity.
Qed.

Theorem interaction_parity_multiplication_A1 :
  forall x y,
  even x -> even y -> even (x * y).
Proof.
  intros x y evenx eveny.
  destruct evenx as [kx evenx].
  destruct eveny as [ky eveny].
  exists (2 * kx * ky).
  rewrite evenx.
  rewrite Z.mul_assoc.
  rewrite Z.mul_shuffle0.
  rewrite eveny.
  rewrite Z.mul_comm.
  reflexivity.
Qed.

Theorem interaction_parity_multiplication_A2 :
  forall d x y,
  d `| x -> d `| y -> d `| (x * y).
Proof.
  intros d x y dx dy.
  destruct dx as [kx dx].
  destruct dy as [ky dy].
  exists (d * kx * ky).
  rewrite dx.
  rewrite Z.mul_assoc.
  rewrite Z.mul_shuffle0.
  rewrite dy.
  rewrite Z.mul_comm.
  reflexivity.
Qed.

Lemma even2 : even 2.
Proof. exists 1. reflexivity. Qed.

Theorem interaction_parity_multiplication_B :
  ~ (
  forall x y,
  even x -> even y -> even (x / y)
  ).
Proof.
  intros wrong.
  specialize (wrong _ _ even2 even2).
  destruct wrong as [k wrong].
  rewrite Z.div_same in wrong.
  + destruct k.
    - discriminate.
    - discriminate.
    - discriminate.
  + discriminate.
Qed.

Theorem divisibility_reflexivity : forall x, x `| x.
Proof.
  exists 1. rewrite Z.mul_1_r. reflexivity.
Qed.

Theorem every_number_divides_zero :
  forall d, d `| 0.
Proof.
  exists 0. rewrite Z.mul_0_r. reflexivity.
Qed.

Theorem zero_only_divides_itself :
  forall x, 0 `| x -> x = 0.
Proof.
  intros z zd.
  destruct zd as [k zd].
  subst.
  rewrite Z.mul_0_l.
  reflexivity.
Qed.

Theorem divisibility_transitivity : forall d n m,
  d `| n -> n `| m -> d `| m.
Proof.
  intros d n m dn nm.
  destruct dn as [kdn dn].
  destruct nm as [knm nm].
  exists (kdn * knm).
  rewrite Z.mul_assoc.
  rewrite dn.
  rewrite nm.
  reflexivity.
Qed.

Theorem divisibility_cancellation : forall d n a,
  a <> 0 ->
  a * d `| a * n ->
  d `| n.
Proof.
  intros d n a a0 adan.
  destruct adan as [kadan adan].
  rewrite <- Z.mul_assoc in adan.
  apply Z.mul_cancel_l in adan.
  + exists kadan.
    assumption.
  + assumption.
Qed.

Theorem divisibility_cancellation_converse : forall d n a,
  d `| n ->
  a * d `| a * n.
Proof.
  intros d n a [kdn dn].
  exists kdn.
  rewrite <- Z.mul_assoc.
  rewrite dn.
  reflexivity.
Qed.

Theorem divisibility_comparison : forall d n,
  d > 0 ->
  n > 0 ->
  d `| n ->
  n >= d.
Proof.
  intros d n d0 n0 [k dn].
  subst.
  pose proof Zmult_ge_compat_l as H.
  specialize (H k 1 d).
  rewrite Z.mul_1_r in H.
  apply H.
  + admit. (* sign reasoning *)
  + admit. (* should be easy *)
Admitted.
