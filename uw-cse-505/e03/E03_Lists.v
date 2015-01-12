(* tell Coq to infer what it can *)
Set Implicit Arguments.

(* what are the tradeoffs of inference? *)

Inductive llist (T: Set) :=
| lnil : llist T
| lcons : T -> llist T -> llist T.

Print llist.
Check (lcons 1 (lcons 2 (lcons 3 (@lnil nat)))).

Arguments lnil [T].
Print llist.
Check (lcons 1 (lcons 2 (lcons 3 lnil))).

(* coq's list is isomorphic *)
Print list.

(*
Fixpoint length l :=
  match l with
    | nil => 0
    | x::xs => S (length xs)
  end.
*)

(* get nifty syntx *)
Require Import List.

Fixpoint countdown (n: nat) :=
  match n with
    | O => nil
    | S m => n :: countdown m
  end.

Eval cbv in (countdown 5).

Fixpoint length (A: Type) (l: list A) :=
  match l with
    | nil => 0
    | x::xs => S (length xs)
  end.

Eval cbv in (length (1 :: 2 :: 3 :: nil)).
Eval cbv in (length (countdown 5)).

Lemma length_countdown:
  forall A (l: list A) n, length (countdown n) = n.
Proof.
  intros. induction n.
  { reflexivity. }
  { simpl. firstorder. }
Qed.

Fixpoint append (A: Type) (l1 l2: list A) :=
  match l1 with
    | nil => l2
    | x::xs => x :: append xs l2
  end.

Eval cbv in (append (countdown 5) (countdown 2)).

Lemma length_append:
  forall A (l1 l2: list A),
  length (append l1 l2) = length l1 + length l2.
Proof.
  intro. intro. induction l1.
  { reflexivity. }
  { simpl. firstorder. }
Qed.

(* in class *)
Fixpoint rev A (l: list A) :=
  match l with
    | nil => nil
    | x::xs => append (rev xs) (x :: nil)
  end.

Definition rev' A (l: list A) :=
  (fix loop acc l := match l with nil => acc | x::xs => loop (x::acc) xs end) l.

Fixpoint rev''_aux A (acc l: list A) :=
  match l with
    | nil => acc
    | x::xs => rev''_aux (x::acc) xs
  end.

Definition rev'' A (l: list A) :=
  rev''_aux nil l.

Eval cbv in (rev (countdown 5)).


Lemma length_rev:
  forall A (l: list A), length (rev l) = length l.
Abort.

Print plus.

Require Import Omega.

Lemma length_rev:
  forall A (l: list A), length (rev l) = length l.
Proof.
  intros. induction l.
  { reflexivity. }
  { simpl. rewrite -> length_append. simpl. firstorder. }
Qed.

Definition upto n :=
  rev (countdown n).

(* we can pass funcs as args *)
Fixpoint map A B (f: A -> B) (l: list A) :=
  match l with
    | nil => nil (* are these the same nil? *)
    | x::xs => f x :: map f xs
  end.

Eval cbv in (map (fun x => S x) (upto 5)).

Lemma length_map:
  forall A B (f: A -> B) (l: list A), length (map f l) = length l.
Proof.
  intros. induction l.
  { reflexivity. }
  { simpl. rewrite -> IHl. reflexivity. }
Qed.

Fixpoint fold A B (f: A -> B -> B) (l: list A) (b: B) :=
  match l with
    | nil => b
    | x::xs => f x (fold f xs b)
  end.

(* in class *)
Definition map' A B (f: A -> B) (l: list A) :=
  fold (fun x fxs => f x :: fxs) l nil.

Lemma map_map':
  forall A B (f: A -> B) (l: list A), map f l = map' f l.
Abort.

Lemma map'_unroll:
  forall A B (f: A -> B) (x: A) (xs: list A),
  map' f (x :: xs) = f x :: map' f xs.
Proof.
  reflexivity.
Qed.

Lemma map_map':
  forall A B (f: A -> B) (l: list A), map f l = map' f l.
Proof.
  intros. induction l.
  { reflexivity. }
  { simpl. rewrite -> map'_unroll. rewrite -> IHl. reflexivity. }
Qed.



























