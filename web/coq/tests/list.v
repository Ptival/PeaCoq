Require Import List.

(** We'll use [countdown] to help test our list functions. *)
Fixpoint countdown (n: nat) :=
  match n with
    | O => nil
    | S m => n :: countdown m
  end.

(** In lecture, we noticed a simple relationship between [length] and [countdown]: *)
Lemma length_countdown:
  forall n, length (countdown n) = n.
Proof.
  (** Consider arbitrary [n]. *)
  intro. induction n.
