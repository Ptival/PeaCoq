(* bug: the regexp was matching the first { with the last } *)
Definition foo {A : Type} {B : Type} := 0.

(* bug: these braces are not optional arguments *)
Class ILogicOps (A : Type) := {
  lentails: A -> A -> Prop;
  ltrue: A;
  lfalse: A;
  limpl: A -> A -> A;
  land: A -> A -> A;
  lor: A -> A -> A;
  lforall: forall {T}, (T -> A) -> A;
  lexists: forall {T}, (T -> A) -> A
}.
