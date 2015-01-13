Set Implicit Arguments.

Inductive llist (T: Type) :=
| lnil : llist T
| lcons : T -> llist T -> llist T.

Print llist.
Check (lcons 1 (lnil nat)).
Arguments lnil [T].
Check (lcons 1 lnil).
Print llist.

Print list.

(* won't work
Check (lcons 1 (lnil bool)).
*)
(* also won't work
Check (lcons 1 (@lnil bool)).
*)

Require Import List.

Fixpoint length A (l: list A) :=
  match l with
    | nil => O
    | x::xs (* cons x xs *) => S (length xs)
  end.

Print length.

Fixpoint countdown (n: nat) :=
  match n with
    | O => nil
    | S m => n :: countdown m
  end.

Eval cbv in (countdown 5).
Eval cbv in (length (countdown 5)).
Eval cbv in (length (countdown 3)).
Eval cbv in (length (countdown 1)).

Lemma length_countdown:
  forall n, length (countdown n) = n.
Proof.
  intro. induction n.
  { reflexivity. }
  { simpl. rewrite -> IHn. reflexivity. }
Qed.

Fixpoint append (A: Type) (l1 l2: list A) :=
  match l1 with
    | nil => l2
    | x::xs => x :: append xs l2
  end.

Fixpoint rev (A: Type) (l: list A) :=
  match l with
    | nil => nil
    | x::xs => append (rev xs) (x :: nil)
               (* rev xs ++ x :: nil *)
  end.

Definition upto (n: nat) :=
  rev (countdown n).

Eval cbv in (upto 5).

Fixpoint rev'_aux A (acc l: list A) :=
  match l with
    | nil => acc
    | x::xs => rev'_aux (x :: acc) xs
  end.

Definition rev' A (l: list A) :=
  rev'_aux nil l.

(* TODO prove rev l = rev' l *)

Fixpoint map A B (f: A -> B) (l: list A) :=
  match l with
    | nil => nil
    | x::xs => f x :: map f xs
  end.

Eval cbv in (map (fun x => S x) (upto 5)).

Lemma length_map:
  forall A B (f: A -> B) (l: list A),
  length (map f l) = length l.
Proof.
  intros. induction l.
  { reflexivity. }
  { simpl. firstorder. }
Qed.

Fixpoint fold A B (f: A -> B -> B)
              (l: list A) (b: B) :=
  match l with
    | nil => b
    | x::xs => f x (fold f xs b)
  end.

(* fold f l b takes a list of
     x1 :: x2 :: x3 :: ... :: xN :: nil
     cons x1 (cons x2 ( ... (cons xN nil) ...)))
   and computes
     f x1 (f x2 (f x3 (... (f xN b) ...)))
*)




(*
      SYNTAX !!!
*)

(*

BNF: Backus Naur Form

bit ::= 0 | 1

bits ::= bit | bits bit

parens ::= () | ( parens ) | parens parens

x ::= x

*)

(*


bit_0 := empty
bit_1 := {0, 1}
bit_2 := {0, 1}
bit_3 := ...
...

bit := U_i bit_i

bits_0 := empty
bits_1 := {0, 1}
bits_2 := {0, 1, 00, 01, 10, 11}
...

bits := U_i bits_i

What about x?  Turns out, it's empty!

*)

Definition name := nat.

Inductive expr : Set :=
| const : nat -> expr
| var : name -> expr
| add : expr -> expr -> expr
| mul : expr -> expr -> expr.

Fixpoint nconsts (e: expr) : nat :=
  match e with
    | const _ => 1
    | var _ => 0
    | add l r => (nconsts l) + (nconsts r)
    | mul l r => (nconsts l) + (nconsts r)
  end.

Lemma has_3_consts:
  exists e, nconsts e = 3.
Proof.
  exists (add (const 1) (add (const 2) (const 3))). simpl. reflexivity.
Qed.

Print orb.

Fixpoint has_const (e: expr) : bool :=
  match e with
    | const _ => true
    | var _ => false
    | add l r => orb (has_const l) (has_const r)
    | mul l r => orb (has_const l) (has_const r)
  end.

Fixpoint has_var (e: expr) : bool :=
  match e with
    | const _ => false
    | var _ => true
    | add l r => orb (has_var l) (has_var r)
    | mul l r => orb (has_var l) (has_var r)
  end.

Lemma bottom_out:
  forall e, has_const e = true \/
            has_var e = true.
Proof.
  intro. induction e.
  { firstorder. }
  { firstorder. }
  { simpl. firstorder. }
  { simpl. firstorder. }
Qed.

Inductive yo: Type :=
| yolo : yo -> yo.

Lemma whack:
  yo -> False.
Proof.
  intro. induction H. destruct IHyo.
Qed.

(* we'll think very carefully about this function soon... *)
Print expr_ind.
