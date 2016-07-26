(* Homework 01 *)

(* include some library code *)
Require Import List.
Require Import NPeano.

(* binary trees of nats *)
Inductive nat_tree : Set :=
| Leaf : nat_tree
| Branch : nat -> nat_tree -> nat_tree -> nat_tree.

Fixpoint fold {T: Type} (base: T) (f: T -> nat -> T) (nt: nat_tree) : T :=
  match nt with
    | Leaf => base
    | Branch n l r => f (fold (fold base f l) f r) n
  end.

Definition avg' (nt: nat_tree) : nat :=
  (let (totalSum, totalSize) := 
      (fold 
        (pair 0 0)
        (fun sumAndSize n => 
          let (sum, size) := sumAndSize in (pair (sum + n) (size + 1)))
        nt)
    in (totalSum / totalSize)).
