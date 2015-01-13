(** * Episode 03: Lists and Syntax *)

(** Ask Coq to infer type arguments. *)
Set Implicit Arguments.

(* Question: What are some of the tradeoffs of inference? *)

(** List is a parameterized, recursive type: *)
Inductive llist (T: Set) :=
| lnil : llist T
| lcons : T -> llist T -> llist T.

(** By default, Coq will not try to infer the type argument for [nil], even if it is obvious from context. *)
Print llist.
Check (lcons 1 (lcons 2 (lcons 3 (@lnil nat)))).

(** But we can tell Coq to always try: *)
Arguments lnil [T].
Print llist.
Check (lcons 1 (lcons 2 (lcons 3 lnil))).

(** The list type Coq provides is isomorphic to our [llist]. *)
Print list.

(** Get nifty notations for cons, append, etc. *)
Require Import List.

(** We'll use [countdown] to help test our list functions. *)
Fixpoint countdown (n: nat) :=
  match n with
    | O => nil
    | S m => n :: countdown m
  end.

Eval cbv in (countdown 5).

(** For polymorphic functions like [length], we must explicitly add a type argument.

If we try to define length without the type argument, like so:
<<
Fixpoint length l :=
  match l with
    | nil => 0
    | x::xs => S (length xs)
  end.
>>
we will get an error like:
<<
Error: Cannot infer an internal placeholder of type "Type".
>>
To avoid this problem, just add the type argument and the type for [l].  Coq can infer the rest:
*)
Fixpoint length (A: Type) (l: list A) :=
  match l with
    | nil => 0
    | x::xs => S (length xs)
  end.

Eval cbv in (length (1 :: 2 :: 3 :: nil)).
Eval cbv in (length (countdown 5)).

(** In lecture, we noticed a simple relationship between [length] and [countdown]: *)
(* notree *)
Lemma length_countdown:
  forall n, length (countdown n) = n.
Proof.
  (** Consider arbitrary [n]. *)
  intro.

  (** We can prove property for arbitrary (S n) if we know property is true for n, so use [induction]. *)
  induction n.

  (** Base case: [n = O] *)
  (** Need to prove [length (countdown O) = O], which reflexivity solves by crunching down [countdown 0] to [nil], then [length nil] to [O], which leaves the goal [O = O]. *)
  { reflexivity. }

  (** Inductive case: [n = S m] *)
  (** Need to prove [length (countdown (S m)) = S m]. First we can cruch [countdown (S m)] down to [S m :: countdown m]. Now we crunch [length (S m :: countdown m)] down to [S (length (countdown m))]. This leaves us with the goal:
<<
  S (length (countdown m)) = S m
>>
   Now if only we happened to know that [length (countdown m) = m] ... BUT WAIT!  That's *exactly* what our induction hypothesis give us!  The [firstorder] tactic is smart enought to figure all this out and use it to finish the proof. *)
  { simpl. firstorder. }
Qed.

(** Append one list to the end of another. *)
Fixpoint append (A: Type) (l1 l2: list A) :=
  match l1 with
    | nil => l2
    | x::xs => x :: append xs l2
  end.

Eval cbv in (append (countdown 5) (countdown 2)).

(** Show that length of two lists appended is just the sum of their lengths. *)
Lemma length_append:
  forall A (l1 l2: list A),
  length (append l1 l2) = length l1 + length l2.
Proof.
  (** Consider arbitrary lists [l1] and [l2]. *)
  intros.

  (** We can prove for arbitrary [l1 = x :: xs] if we just know property is true for [xs], so use induction. *) 
  induction l1.

  (** Base case: [l1 = nil]. *)
  (** Need to prove [length (append nil l2) = length nil + length l2], which reflexivity solves by crunching down to [length (l2) = O + length l2] and then to [length l2 = length l2]. *)
  { reflexivity. }

  (** Inductive case: [l1 = x :: xs] *)
  (** Need to prove [length (append (x :: xs) l2) = length (x :: xs) + length l2]. First we can cruch [length (append (x :: xs) l2)] down to [length (x :: append xs l2)] and again to [S (length (append xs l2))]. We can also crunch [length (x :: xs) + length l2] down to [(S (length xs)) + length l2] which crunches down again to [S (length xs + length l2)]. This leaves us with the goal:
<<
  S (length (append xs l2)) = S (length xs + length l2)
>>
   Now if only we happened to know that [length (append xs l2) = length xs + length l2] ... BUT WAIT!  That's *exactly* what our induction hypothesis give us!  After a little crunching from [simpl], the [firstorder] tactic is smart enought to figure all this out and use it to finish the proof. *)
  { simpl. firstorder. }
Qed.


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






























