(* The following material is derived from Software Foundations by Benjamin
Pierce et al. Their work is under the following MIT license: *)

(*
Copyright (c) 2012

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
 *)

Ltac each := match goal with |- _ /\ _ => split end.
Ltac goleft := match goal with |- _ \/ _ => left end.
Ltac goright := match goal with |- _ \/ _ => right end.

(* ###################################################################### *)
(** ** Days of the Week *)

Inductive day : Type :=
| monday : day
| tuesday : day
| wednesday : day
| thursday : day
| friday : day
| saturday : day
| sunday : day
.

Definition tomorrow (d: day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday
  | sunday    => monday
  end.

Theorem test_tomorrow:
  tomorrow saturday = sunday.
Proof.
  (* FILL IN HERE *)
Qed.

(* ###################################################### *)
(** ** Lists of Numbers *)

Inductive natlist : Type :=
| nil  : natlist
| cons : nat -> natlist -> natlist
.

Definition empty_list := nil.

Definition singleton_list := cons 42 nil.

Definition one_two_three := cons 1 (cons 2 (cons 3 nil)).

Fixpoint concat (l1 l2 : natlist) : natlist :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (concat t l2)
  end.

Theorem test_concat1:
  concat (cons 1 (cons 2 nil))
         (cons 3 (cons 4 nil))
  = (cons 1 (cons 2 (cons 3 (cons 4 nil)))).
Proof.
  (* FILL IN HERE *)
Qed.

(* ###################################################### *)
(** * Reasoning About Lists *)

Theorem concat_nil_left : forall l : natlist,
  concat nil l = l.
Proof.
  (* FILL IN HERE *)
Qed.

Theorem concat_nil_right : forall l : natlist,
  concat l nil = l.
Proof.
  (* FILL IN HERE *)
Qed.

(* In-class exercise! *)
Theorem concat_associativity : forall l2 l1 l3 : natlist,
  concat (concat l1 l2) l3 = concat l1 (concat l2 l3).
Proof.
  (* FILL IN HERE *)
Qed.

(*
  [snoc] adds an element [v] at the end of the list [l]:
    snoc (cons 1 (cons 2 nil)) 3 = cons 1 (cons 2 (cons 3 nil))
*)
Fixpoint snoc (l: natlist) (v: nat) : natlist :=
  match l with
  | nil      => cons v nil
  | cons h t => cons h (snoc t v)
  end.

(*
  [rev] reverses a list:
    rev (cons 1 (cons 2 nil)) = cons 2 (cons 1 nil)
*)
Fixpoint rev (l: natlist) : natlist :=
  match l with
  | nil      => nil
  | cons h t => snoc (rev t) h
  end.

(* ###################################################### *)
(** 
  For each theorem:
  - Discuss the statement of the theorem with your partner.
  - Once you understand it, prove the theorem.

  Every time you solve a theorem, switch who uses the keyboard/mouse.
 *)

Theorem rev_snoc : forall x l,
  rev (snoc l x) = cons x (rev l).
Proof.
  (* FILL IN HERE *)
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  (* FILL IN HERE *)
Qed.

Theorem concat_cons_snoc : forall l1 x l2,
  concat l1 (cons x l2) = concat (snoc l1 x) l2.
Proof.
  (* FILL IN HERE *)
Qed.

(* ###################################################### *)

(* We now use notations from logic:
  /\   stands for the logical conjunction (AND) of two propositions
  \/   stands for the logical disjunction (OR)  of two propositions

  New tactics: goleft, goright

  When your goal looks like [A \/ B]
  You get to pick which of [A] or [B] you will prove.
  If you believe you can prove [A], use the [goleft.] tactic.
  If you believe you can prove [B], use the [goright.] tactic.

  Here is an example:
*)

Theorem goright_example : 0 = 1 \/ 1 = 1.
Proof.
  goright. reflexivity.
Qed.

Theorem go_somewhere : 0 = 1 \/ (2 = 2 \/ 2 = 3).
Proof.
  (* FILL IN HERE *)
Qed.


(*
  New tactic: apply

  If you ever have a goal [G]
  And a hypothesis [H : G] or [H : X -> ... -> G]
  You can use the tactic [apply H.] to solve your goal in the former case,
  or turn your goal into subgoal(s) [X], [...] in the latter case.
*)

Theorem B_is_enough : forall A B : Prop,
  B ->
  A \/ B.
Proof.
  (* FILL IN HERE *)
Qed.

(*
  New tactic: each

  When your goal looks like [A /\ B]
  You need to prove both [A] and [B].
  The tactic [each.] lets you split your goal into these two goals.

  Here is an example:
*)

Theorem two_facts : nil = nil /\ 42 = 42.
Proof.
  each. reflexivity. reflexivity.
Qed.

Theorem more_facts : 1 = 2 \/ (1 = 1 /\ nil = nil).
Proof.
  (* FILL IN HERE *)
Qed.

Theorem A_and_B : forall A B : Prop,
  A ->
  B ->
  A /\ B.
Proof.
  (* FILL IN HERE *)
Qed.

(* ###################################################### *)

Theorem snoc_concat_end : forall (l: natlist) (n: nat),
  snoc l n = concat l (cons n nil).
Proof.
  (* FILL IN HERE *)
Qed.

Theorem rev_distributes_over_concat : forall l1 l2 : natlist,
  rev (concat l1 l2) = concat (rev l2) (rev l1).
Proof.
  (* FILL IN HERE *)
Qed.

(* ###################################################### *)
(** We now introduce [map], which applies a function [f] to
    every element of a list [l].
*)

Fixpoint map (f: nat -> nat) (l: natlist) :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
  end.

Theorem map_commutes : forall f g l,
  (forall x, f (g x) = g (f x)) ->
  map f (map g l) = map g (map f l).
Proof.
  (* FILL IN HERE *)
Qed.

(* In this theorem, "fun x =>" introduces an anonymous function which receives
   a parameter [x] and returns the result on the right of the arrow. *)
Theorem map_fusion : forall f g l,
  map f (map g l) = map (fun x => f (g x)) l.
Proof.
  (* FILL IN HERE *)
Qed.

(* ###################################################### *)
(** We now introduce [fold], which processes a list with an
    accumulating function [f], starting from an initial value [b].
*)
Fixpoint fold (f: nat -> natlist -> natlist) (l: natlist) (b: natlist) :=
  match l with
  | nil => b
  | cons x xs => f x (fold f xs b)
  end.

Theorem fold_snoc : forall f l x b,
  fold f (snoc l x) b = fold f l (f x b).
Proof.
  (* FILL IN HERE *)
Qed.

Definition map' f l := fold (fun x fxs => cons (f x) fxs) l nil.

(* We use [Lemma] instead of [Theorem] here to indicate that this theorem may
   help you in proving the next theorem. *)
Lemma map'_unroll : forall f x xs,
  map' f (cons x xs) = cons (f x) (map' f xs).
Proof.
  (* FILL IN HERE *)
Qed.

Theorem map_map' : forall f l, map f l = map' f l.
Proof.
  (* FILL IN HERE *)
Qed.

(*
  New tactic: destruct

  When a hypothesis looks like [H : A \/ B]
  You have to prove the goal for each case, to do so, use the tactic [destruct H.]
  You will get two goals as a result, one with a [A] hypothesis, one with a [B] hypothesis.

  Finally, if you ever get a hypothesis like [H : False]
  You have derived a contradiction, and you can indicate this to the system by calling
  the tactic [contradiction.], which will solve your goal.
*)

Fixpoint In n l :=
  match l with
  | nil      => False
  | cons h t => h = n \/ In n t
  end.

Theorem In_cons : forall x h l,
  In x l ->
  In x (cons h l).
Proof.
  (* FILL IN HERE *)
Qed.

Theorem In_concat_left : forall x l1 l2,
  In x l1 ->
  In x (concat l1 l2).
Proof.
  (* FILL IN HERE *)
Qed.
