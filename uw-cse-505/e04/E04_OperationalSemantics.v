(** * Episode 04: Operational Semantics *)

Require Import String.
Open Scope string.

Definition var := string.
Definition val := nat.

Inductive expr : Type :=
| Const : val -> expr
| Var : var -> expr
| Add : expr -> expr -> expr
| Mul : expr -> expr -> expr.

Inductive stmt : Type :=
| Skip : stmt
| Assign : var -> expr -> stmt
| Seq : stmt -> stmt -> stmt
| Cond : expr -> stmt -> stmt -> stmt
| While : expr -> stmt -> stmt.

Definition heap := var -> val.

Definition empty : heap :=
  fun s => 0.

Definition add_binding n v h : heap :=
  fun s => if string_dec s n then v else h s.

Inductive Eval (h: heap) : expr -> val -> Prop :=
| EConst : forall n,
  Eval h (Const n) n
| EVar : forall x,
  Eval h (Var x) (h x)
| EAdd : forall e1 e2 c1 c2 c3,
  Eval h e1 c1 ->
  Eval h e2 c2 ->
  c3 = c1 + c2 ->
  Eval h (Add e1 e2) c3
(*
was:

| EAdd : forall e1 e2 c1 c2,
  Eval h e1 c1 ->
  Eval h e2 c2 ->
  Eval h (Add e1 e2) (c1 + c2)

but this forces Coq to guess [c1] and [c2] from [(c1 + c2)] which can be
impossible, so it helps to introduce another variable [c3] and add an
equality that can be delayed until [c1] and [c2] have been figured out in
other parts of the proof.
 *)
| EAdd : forall e1 e2 c1 c2 c3,
  Eval h e1 c1 ->
  Eval h e2 c2 ->
  c3 = c1 + c2 ->
  Eval h (Add e1 e2) c3
| EMul : forall e1 e2 c1 c2,
  Eval h e1 c1 ->
  Eval h e2 c2 ->
  Eval h (Mul e1 e2) (c1 * c2).

Theorem Eval_101 :
  Eval (add_binding "y" 4 empty) (Add (Add (Const 3) (Var "y")) (Const 5)) 12.
Proof.
  eapply EAdd.
  eapply EAdd.
  constructor.
  constructor.
  constructor.
  constructor.
  constructor.
Qed.

Print Eval_101.

Inductive Step (h : heap) : stmt -> heap -> stmt -> Prop :=
| SAssign : forall e c x,
  Eval h e c ->
  Step h (Assign x e) (fun s => if string_dec s x then c else h s) Skip
| SSeq1 : forall s,
  Step h (Seq Skip s) h s
| SSeq2 : forall s1 s2 s1' h',
  Step h s1 h' s1' ->
  Step h (Seq s1 s2) h' (Seq s1' s2)
| SCondT : forall e c s1 s2,
  Eval h e c ->
  c > 0 ->
  Step h (Cond e s1 s2) h s1
| SCondF : forall e c s1 s2,
  Eval h e c ->
  c <= 0 ->
  Step h (Cond e s1 s2) h s2
| SWhileT : forall e c s,
  Eval h e c ->
  c > 0 ->
  Step h (While e s) h (Seq s (While e s))
| SWhileF : forall e c s,
  Eval h e c ->
  c <= 0 ->
  Step h (While e s) h Skip.

(** alternatively...
| SWhileT : forall e s,
  Step h (While e s) h (Seq (Cond e s) (While e s))
*)
