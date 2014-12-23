Require Import Unicode.Utf8.

(*
  Welcome to the PeaCoq frontend to the Coq Proof Assistant.
 *)

(*
Here is some code:
 *)

Inductive bool : Type :=
| true : bool
| false : bool
.

(* Here is a theorem: *)

Theorem bools_are_true_or_false : ∀ b, b = true \/ b = false.
Proof.
  intro. destruct b.
  { left. reflexivity. }
  { right. reflexivity. }
Qed.

(* Here is another theorem: *)

Theorem bools_are_not_true_and_false : ∀ b, ~ (b = true /\ b = false).
Proof.
  intro. intro. destruct H. destruct b. inversion H0. inversion H.
Qed.

(* Yet another theorem: *)

Theorem bools_are_not_true_and_false : ∀ b, ~ (b = true /\ b = false).
Proof.
  intro. intro. destruct H. destruct b. inversion H0. inversion H.
Qed.
