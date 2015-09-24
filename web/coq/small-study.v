Require Import String.

Inductive nat :=
| O : nat
| S : nat -> nat
.

Fixpoint plus n m :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Theorem plus_O_right : forall n, plus n O = n.
Proof.
  intros. induction n.
  + simpl. reflexivity.
  + simpl. rewrite -> IHn. reflexivity.
Qed.

Inductive binaryTree :=
| Leaf : bool -> binaryTree
| Node : binaryTree -> binaryTree -> binaryTree
.

Fixpoint insertRight b t :=
  match t with
  | Leaf b2 => Node (Leaf b2) (Leaf b)
  | Node t1 t2 => Node t1 (insertRight b t2)
  end.

Fixpoint tSize t :=
  match t with
  | Leaf _ => 1
  | Node t1 t2 => tSize t1 + tSize t2
  end.

Theorem insertRight_length : forall b t, tSize (insertRight b t) = 1 + tSize t.
Proof.
  intros. induction t.
  + simpl. reflexivity.
  + simpl. rewrite -> IHt2. simpl. rewrite plus_n_Sm. reflexivity.
Qed.

Inductive expr :=
| Var : string -> expr
| App : expr -> expr -> expr
.

Fixpoint renameAllVars s e :=
  match e with
  | Var _ => Var s
  | App e1 e2 => App (renameAllVars s e1) (renameAllVars s e2)
  end.

Fixpoint nbVars e :=
  match e with
  | Var _ => 1
  | App e1 e2 => nbVars e1 + nbVars e2
  end.

Theorem renameAllVars_nbVars : forall e, nbVars e = nbVars (renameAllVars "foo" e).
Proof.
  intros. induction e.
