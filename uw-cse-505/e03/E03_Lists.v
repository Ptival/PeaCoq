(** * Episode 03: Lists *)

(** This command asks Coq to infer ``easy'' type arguments. *)
Set Implicit Arguments.
(** As a result of running [Set Implicit Arguments], sometimes we will apply functions or constructors to fewer arguments than they are defined to take.  When you see that, it simply indicates that Coq was able to automatically infer the missing arguments. *)

(* Question: What are some of the tradeoffs of inference? *)

(** A parameterized, recursive type: *)
Inductive llist (T: Type) :=
| lnil : llist T
| lcons : T -> llist T -> llist T.

(** Above we define [list] to be a type parameterized by some other type [T].  Furthermore, we say that there are _exactly_ two ways to build a [llist]: (1) using the [lnil] constructor or (2) using the [lcons] constructor.  When the [lnil] constructor is applied to a _type_ [T], it yields a value of type [llist T]:
 *)
Check lnil.
(**
<<
lnil
     : forall T : Type, llist T
>>
We'll talk a lot more about [forall] throughout the course, but in this case you can think of it as just a fancy [->].  When the [lcons] constructor is applied to a _type_ [T], a _value of type_ [T], and a value of type [llist T], it yields a value of type [llist T]:
 *)
Check lcons.
(**
<<
lcons
     : forall T : Type, T -> llist T -> llist T
>>
*)

(** Coq will infer the type argument [T] for [lcons], but it will not try to infer the type argument [T] for [lnil], even if it is obvious from context. *)
Print llist.
(**  So this will break, even though context forces [T] to be [nat]:
<<
Check (lcons 1 (lcons 2 (lcons 3 lnil))).
>>
But this works:
*)
Check (lcons 1 (lcons 2 (lcons 3 (lnil nat)))).

(** However, we can tell Coq to always try to infer the type argument [T] of [lnil] from context: *)
Arguments lnil [T].
Print llist.
Check (lcons 1 (lcons 2 (lcons 3 lnil))).

(* won't work
Check (lcons 1 (lnil bool)).
*)
(* also won't work
Check (lcons 1 (@lnil bool)).
*)

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
Eval cbv in (length (countdown 3)).
Eval cbv in (length (countdown 1)).

(** In lecture, we noticed a simple relationship between [length] and [countdown]: *)
Lemma length_countdown:
  forall n, length (countdown n) = n.
Proof.
  (** Consider arbitrary [n]. *)
  intro.

  (** We can prove property for arbitrary (S n) if we know property is true for n, so use [induction]. *)
  induction n.

  (** Base case: [n = O] *)
  (** Need to prove [length (countdown O) = O], which reflexivity solves by crunching down [countdown 0] to [nil], then [length nil] to [O], which leaves the goal [O = O]. *)
  { reflexivity. }

  (** Inductive case: [n = S m] *)
  (** Need to prove [length (countdown (S m)) = S m]. First we can cruch [countdown (S m)] down to [S m :: countdown m]. Now we crunch [length (S m :: countdown m)] down to [S (length (countdown m))]. This leaves us with the goal:
<<
  S (length (countdown m)) = S m
>>
   Now if only we happened to know that [length (countdown m) = m] ... BUT WAIT!  That's *exactly* what our induction hypothesis give us!  After crunching with simpl, the [firstorder] tactic is smart enought to figure all this out and use the induction hypothesis to finish the proof. *)
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
  length (l1 ++ l2) = length l1 + length l2.
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
   Now if only we happened to know that [length (append xs l2) = length xs + length l2] ... BUT WAIT!  That's *exactly* what our induction hypothesis give us!  After a little crunching from [simpl], the [firstorder] tactic is smart enought to figure all this out and use the induction hypothesis to finish the proof. *)
  { simpl. firstorder. }
Qed.

(** Reverse the elements of a list. *)
Fixpoint rev A (l: list A) :=
  match l with
    | nil => nil
    | x::xs =>
    (** Note: [++] is just an infix operator for [append], so: *)
      rev xs ++ x :: nil
    (** is the same as:
<<
      append (rev xs) (x :: nil)
>> *)
  end.

Eval cbv in (rev (countdown 5)).

(** Note that the above version of [rev] is not efficient. We can do better using a helper function to collect the reversed version of the list as we recurse: *)
Fixpoint rev'_aux A (acc l: list A) :=
  match l with
    | nil => acc
    | x :: xs => rev'_aux (x :: acc) xs
  end.

Definition rev' A (l: list A) :=
  rev'_aux nil l.

(** While [rev'] is more efficient than [rev], it is a bit trickier to reason about. *)

(** To prove [rev] and [rev'] are equivalent, we'll need a fact about [append]: *)
Lemma append_associative:
  forall A (l1 l2 l3: list A),
  l1 ++ l2 ++ l3 = (l1 ++ l2) ++ l3.
Proof.
  (** It turns out that firstorder already know this one. *)
  firstorder.
Qed.

(** Now we need to prove a carefully chosen lemma about rev'_aux. *)
Lemma rev_rev'_aux:
  forall A (l acc: list A),
  rev'_aux acc l = rev l ++ acc.
Proof.
  intro. intro. induction l.
  { reflexivity. }
  { intro. simpl. rewrite -> IHl. rewrite <- append_associative. reflexivity. }
Qed.

(** Now we should be able to prove equivalence. *)
Lemma rev_rev':
  forall A (l: list A), rev l = rev' l.
Proof.
  (** Note: we have to unfold [rev] first! This allows us to use [rev_rev'_aux]. *)
  unfold rev'. intros. rewrite -> rev_rev'_aux. firstorder.
Qed.

(** Question: Why did we need to prove [rev_rev'_aux] separately from [rev_rev']? *)

(** To prove that [rev] preserved length, we'll need to know a little more about arithmetic. *)
Lemma length_rev:
  forall A (l: list A), length (rev l) = length l.
  (** We get stuck trying to prove:
<<
  length l + 1 = S (length l)
>> *)
Abort.

(** Question: Why do we get stuck? *)
Print plus.

(** Coq has a decision procedure for Pressburger arithmetic.  It will make short work of our problem. *)
Require Import Omega.

Lemma length_rev:
  forall A (l: list A), length (rev l) = length l.
Proof.
  intros. induction l.
  { reflexivity. }
  { simpl. rewrite -> length_append. simpl. firstorder. }
Qed.

(** [upto] is another useful function for testing. *)
Definition upto n :=
  rev (countdown n).

(** We can prove that [rev (rev l) = l], but we'll need a lemma about [rev] and [append]: *)
Lemma rev_append:
  forall A (l1 l2: list A), rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intro. intro. induction l1.
  { simpl. firstorder. }
  { intro. simpl. rewrite -> IHl1. firstorder. }
Qed.

(** Now for the lemma we really want: *)
Lemma rev_involutive:
  forall A (l: list A), rev (rev l) = l.
Proof.
  intros. induction l.
  { reflexivity. }
  { simpl. rewrite -> rev_append. simpl. rewrite -> IHl. reflexivity. }
Qed.

(** The famous [map] function provides our first useful example of "higher order functions", which is just a fancy way of saying that [map] is a function which takes another function as an argument (in this case, the argument is named [f]). *)
Fixpoint map A B (f: A -> B) (l: list A) :=
  match l with
    (** Question: Are these the same nil? *)
    | nil => nil
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

(** The also famous [fold] function. *)
Fixpoint fold A B (f: A -> B -> B) (l: list A) (b: B) :=
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
