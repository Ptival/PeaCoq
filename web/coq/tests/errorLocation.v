Require Import List.

Definition typo l :=
  match l with
    | nil => 0
    | h::t => t
  end.
