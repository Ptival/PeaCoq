Require Import List.

Fixpoint length {A: Set} (l: list A) :=
  match l with
    | nil => 0
    | x :: xs => 1 + length xs
  end.

Fixpoint length2_loop acc {A: Set} (l: list A) :=
  match l with
    | nil => acc
    | x :: xs => length2_loop (1 + acc) xs
  end.

Definition length2 {A: Set} (l: list A) :=
  length2_loop 0 l.

Inductive tree (A: Set) : Set :=
| Leaf: tree A
| Branch : A -> tree A -> tree A -> tree A.

Fixpoint size {A: Set} (t: tree A) :=
  match t with
    | Leaf => 0
    | Branch a l r => 1 + size l + size r
  end.

Fixpoint size2_loop acc {A: Set} (t: tree A) :=
  match t with
    | Leaf => acc
    | Branch a l r => size2_loop (size2_loop (1 + acc) l) r
  end.

Definition size2 {A: Set} (t: tree A) :=
  size2_loop 0 t.

(*

Fixpoint size3_loop acc {A: Set} (stack: list (tree A)) (t: tree A) :=
  match t with
    | Leaf => match stack with
                | nil => acc
                | x :: xs => size3_loop acc xs x
              end
    | Branch a l r => size3_loop (1 + acc) (r :: stack) l
  end.

Definition size3 {A: Set} (t: tree A) :=
  size3_loop 0 nil t.

*)



