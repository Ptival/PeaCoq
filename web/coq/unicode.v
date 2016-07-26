(* Test of error highlighting

The error should highlight the last γ₁₂ variable occurrence, the whole
of it, and only it (not the final dot nor the preceding space).
*)

From Coq Require Import Utf8.

Lemma α₁: ∀ x:nat, ∀ γ₁₂: bool, x = γ₁₂.
