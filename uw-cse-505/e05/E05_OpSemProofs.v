(** * Episode 05: Proofs About Operational Semantics *)

Require Import List.
Require Import String.
Require Import ZArith.

(** use fancy string notations *)
Open Scope string.

(** we'll use a binary representation of signed integers *)
Print Z.
Print positive.

Set Implicit Arguments.

(** quick review of fold *)
Fixpoint fold A B (f: A -> B -> B)
                  (l: list A) (b: B) :=
  match l with
    | nil => b
    | x :: xs => f x (fold f xs b)
  end.

(** "+" can mean different things in different scopes *)
Locate "+".

Fixpoint countdown (n: nat) :=
  match n with
    | O => nil
    | S m => Z_of_nat n :: countdown m
  end.

Eval cbv in (countdown 5).
Eval cbv in (fold Z.add (countdown 5) 0%Z).
Eval cbv in (fold Z.add (countdown 12) 0%Z).

(**
<<
 fold + (3 :: 2 :: 1 :: nil) 0
     ==> 3 + (2 + (1 + 0))
>>
*)

(** Defining [fact] with an anonymous [fix] (note the type!): *)
Definition fact : nat -> nat :=
  fix loop (n: nat) :=
      match n with
        | O => 1
        | S m => n * loop m
      end.

(** Could have also defined [fact] using [Fixpoint]:
<<
Fixpoint fact (n: nat) : nat := ...
>>
*)


(** AST *)

Definition var := string.
Definition val := Z.

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

(** switch to association lists for heaps *)
Definition heap := list (var * val).

Fixpoint lkup (k: var) (h: heap) :=
  match h with
    | nil => 0%Z
    | (x, v) :: h' =>
      if string_dec k x then v else lkup k h'
  end.

(** fancy type containing proofs, but that acts like a [bool] *)
Check string_dec.
(**
<<
string_dec
     : forall s1 s2 : string,
       {s1 = s2} + {s1 <> s2}
>>
*)

Definition empty : heap :=
  nil.

(** Small Step Operational Semantics *)
Inductive Eval (h: heap) : expr -> val -> Prop :=
| EConst : forall n,
  Eval h (Const n) n
| EVar : forall x,
  Eval h (Var x) (lkup x h)
| EAdd : forall e1 e2 c1 c2 c3,
  Eval h e1 c1 ->
  Eval h e2 c2 ->
  c3 = (c1 + c2)%Z ->
  Eval h (Add e1 e2) c3
| EMul : forall e1 e2 c1 c2 c3,
  Eval h e1 c1 ->
  Eval h e2 c2 ->
  c3 = (c1 * c2)%Z ->
  Eval h (Mul e1 e2) c3.

(** not every [(heap, expr, Z)] is related by [Eval] *)
Lemma not_in_eval:
  forall x,
  Eval nil (Var x) 1%Z -> False.
Proof.
  intros. inversion H.
Qed.

(** the [Eval] relation has nothing to do with [Eval] command *)
Eval cbv in (countdown 5).

Inductive Step (h : heap)
 : stmt -> heap -> stmt -> Prop :=
| SAssign : forall e c x,
  Eval h e c ->
  Step h (Assign x e) ((x, c) :: h) Skip
| SSeq1 : forall s,
  Step h (Seq Skip s) h s
| SSeq2 : forall s1 s2 s1' h',
  Step h s1 h' s1' ->
  Step h (Seq s1 s2) h' (Seq s1' s2)
| SCondT : forall e c s1 s2,
  Eval h e c ->
  (c > 0)%Z ->
  Step h (Cond e s1 s2) h s1
| SCondF : forall e c s1 s2,
  Eval h e c ->
  (c <= 0)%Z ->
  Step h (Cond e s1 s2) h s2
| SWhileT : forall e c s,
  Eval h e c ->
  (c > 0)%Z ->
  Step h (While e s) h (Seq s (While e s))
| SWhileF : forall e c s,
  Eval h e c ->
  (c <= 0)%Z ->
  Step h (While e s) h Skip.

Inductive StepN : heap -> stmt -> nat ->
                  heap -> stmt -> Prop :=
| StepN_refl: forall h s,
  StepN h s O h s
| StepN_step: forall h s n h' s' h'' s'',
  Step h s h' s' ->
  StepN h' s' n h'' s'' ->
  StepN h s (S n) h'' s''.

(** Divergance *)

Lemma diverges1:
  forall h n, exists h', exists s',
  StepN h (While (Const 1%Z) Skip) n h' s'.
Proof.
Admitted.
(*
  intros.
  induction n.
  { exists h.
    exists (While (Const 1%Z) Skip).
    apply StepN_refl. (* constructor. *)
  }
  { firstorder. rename x into h'.
    rename x0 into s'. exists h.
    eexists. eapply StepN_step.
    ... stuck! ...
*)
