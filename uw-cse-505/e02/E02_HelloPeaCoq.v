(** * Episode 02: Hello PeaCoq *)

(** Comments go between _left-paren star_ and _star right-paren_.
<<
(* (* they can even be nested *) *)
>>
*)

(** This _binding_ associates the name [x] to the expression [0]: *)

Definition x := 0.

(** Coq code is primarily a sequence of bindings. In PeaCoq, we can step through the bindings one at a time by pressing:
<<
  Control-Alt-Down
>>
When we ask Coq to process a binding like:
<<
  Definition foo := bar.
>>
it does the following:
- Type check the expression [bar].
  - This ensures that, if asked, Coq will be able to evaluate [bar] down to a value.
- Extend the environment to associate the name [foo] to the expression [bar].
*)

(** Coq also has _commands_ which let us poke around and ask Coq questions. For example, the [Print] command displays the value associated with a name:
*)

Print x.

(** It only works on names though; this will crash:
<<
Print 1.
>>
*)

(** The [Check] command displays the type of an expression: *)

Check x.

(** The [Eval cbv in] command evaluates an expression down to a value: *)

Eval cbv in (1 + 1).

(** Here is a simple _inductive definition_: *)

Inductive boolean :=
| btrue : boolean
| bfalse : boolean.

(** It says that [boolean] is a type and that there are exactly two values that have type [boolean], [btrue] and [bfalse]. *)

(** Coq actually doesn't have any built-in types! However, the standard prelude provides a several familiar types. For example, the type [bool] from the standard prelude is just like our type [boolean]: *)

Print bool.

(** We can also bind names to functions by including arguments to our Definitions: *)

Definition bid (x: bool) := x.

(** This binds a function [bid] to a function which takes a sinlge argument, [x] of type [bool] and when called simply returns [x]. *)

(** We call functions via juxtaposition which is a fancy way of saying we just write the function name and the argument next to it: *)

Eval cbv in (bid true).
Eval cbv in (bid false).

(** In Coq we can also prove that our functions work as expected.  Here is a simple proof showing that bid has the behavior we expect: it always just returns its argument: *)

Lemma bid_ok :
  forall b, bid b = b.
Proof.
  intro.

(** The _tactic_ [intro] above transforms the _proof goal_ from:
<<
  
  ============================
   forall b : bool, bid b = b
>>
to:
<<
  b : bool
  ============================
   bid b = b
>>

You can think of it as proving a universally quantified claim about booleans by considering an arbitrary boolean.

*)

  unfold bid.

(** The tactic [unfold bid] above transforms the proof goal to:
<<
  b : bool
  ============================
   b = b
>>

This simply replaces the identifier [bid] with whatever it is bound to in the current environment.

*)

  reflexivity.

(** Finally, the [reflexivity] tactic solves this subgoal. Since we don't have any outstanding subgoals, the proof is done and we end with a nice [Qed.] *)

Qed.

(** We can also define functions that do case analysis, or _pattern matching_, on their arguments: *)

Definition bneg (b: bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Eval cbv in (bneg true).
Eval cbv in (bneg false).

(** To define functions of multiple arguments, just add another argument! *)

Definition band (l: bool) (r: bool) : bool :=
  match l with 
    | true =>
      match r with
        | true => true
        | false => false
       end
    | false => false
  end.

Eval cbv in (band true true).
Eval cbv in (band true false).
Eval cbv in (band false true).
Eval cbv in (band false false).

(** We can also lump arguments of the same type together. *)

Definition bor (l r: bool) : bool :=
  match l with 
    | true => true
    | false =>
      match r with
        | true => true
        | false => false
       end
  end.

Eval cbv in (bor true true).
Eval cbv in (bor true false).
Eval cbv in (bor false true).
Eval cbv in (bor false false).

(** What types do our functions have? *)

Check bid.
(** <<
bid
     : bool -> bool
>> *)

Check bneg.
(** <<
bid
     : bool -> bool
>> *)

Check band.
(** <<
band
     : bool -> bool -> bool
>> *)

Check bor.
(** <<
bor
     : bool -> bool -> bool
>> *)

(** A function with type [A -> B] takes an argument of type [A] and returns a result of type [B].  The arrow [->] associates to the right, so [A -> B -> C] means the same as [A -> (B -> C)].  Here we see _currying_ where we can encode functions of _multiple_ arguments as functions of _single_ arguments which take an argument and return a _function_ that takes the next argument and return a _function_ that takes the next argument and return ... until all the arguments have been taken and then the function can simply return the result. *)

Lemma demorgan_band:
  forall l r,
  band l r = bneg (bor (bneg l) (bneg r)).
Proof.
  intros.

  (** [intros] works like [intro], but it slurps up all the universally quantified variables at the front of a goal. *)
  
  intros.

  (** [destruct] does case analysis. *)
  destruct l.

  (** In the case that [l = true], we want to also do case analysis on [r]: *)
  destruct r.

  (** We can solve both the subcases with [reflexivity]. *)
  reflexivity.
  reflexivity.

  (** In the case that [l = false], [reflexivity] does the trick. *)
  { reflexivity. }
Qed.

(** Another of DeMorgan's laws can be proved similarly: *)

Lemma demorgan_bor:
  forall l r,
  bor l r = bneg (band (bneg l) (bneg r)).
Proof.
  intros. destruct l.
  { reflexivity. }
  { destruct r.
    { reflexivity. }
    { reflexivity. }
  }
Qed.

(** The curly baces ``{'' and ``}'' help us note which subgoals we're in and make the structure of the proof a little bit clearer.  While they're technically optional, PeaCoq will always generate them to help make the resulting proof term easier to understand. *)


(** _Side Note_ : We can write our functions to just bind a name to an expression and use [fun] to build an _anonymous function_: *)

Definition bneg' : bool -> bool :=
  fun (b: bool) =>
    match b with
      | true => false
      | false => true
    end.

(** Also we can often omit certain type annotations, and Coq will figure them out automatically! *)

Definition bneg'' :=
  fun (b: bool) =>
    match b with
      | true => false
      | false => true
    end.

Check bneg''.

Definition bneg''' : bool -> bool :=
  fun b =>
    match b with
      | true => false
      | false => true
    end.

Check bneg'''.

(** The same goes for functions with multiple arguments: *)

Definition band' : bool -> bool -> bool :=
  fun (l: bool) =>
    fun (r: bool) =>
      match l with 
        | true =>
          match r with
            | true => true
            | false => false
          end
        | false => false
      end.

Lemma band_equiv_band':
  forall b, band b = band' b.
Proof.
  reflexivity.
Qed.

(** OK, enough booleans. Let's look at numbers. *)

Definition nid (x: nat) := x.

Eval cbv in (nid 0).
Eval cbv in (nid 1).
Eval cbv in (nid 2).

Check (nid 2).

Lemma nid_ok :
  forall n, nid n = n.
Proof.
  reflexivity.
Qed.

(** [nat] is defined a bit differently from [bool]: *)

Print nat.
(** <<
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.
>> *)

(** The [S] _constructor_ takes a [nat] as an argument.  This allows [nat] to contain infinitely many terms: [O] represents 0 and [S n] represents [1 + n]. *)

Eval cbv in O.
Eval cbv in (S O).
Eval cbv in (S (S O)).
Eval cbv in (S (S (S O))).
Eval cbv in (S (S (S (S O)))).

(** This also means that if we want to write functions over [nat], we need _recursive_ definitions, which we introduce with [Fixpoint]: *)

Fixpoint nadd (n1 n2: nat) : nat :=
  match n1 with
    | O => n2
    | S n => S (nadd n n2)
  end.

Fixpoint nmult (n1 n2: nat) : nat :=
  match n1 with
    | O => O
    | 1 => n2
    | S n => nadd n2 (nmult n n2)
  end.

Fixpoint factorial n :=
  match n with
  | O => 1
  | S m => n * factorial m
  end.

(** We can prove things about functions over [nat] similar to our proofs about functions over [bool]: *)

Lemma nadd_0_n:
  forall n, nadd 0 n = n.
Proof.
  reflexivity.
Qed.

(** However, some of these proof will also require [induction], which we'll talk about extensively during the course: *)

Lemma nadd_n_0:
  forall n, nadd n 0 = n.
Proof.
  intro. induction n.
  { reflexivity. }
  { simpl. rewrite -> IHn. reflexivity. }
Qed.

(** _Question_ : Why did we need [induction] for [nadd_n_0] but not for [nadd_0_n] ? *)

(** Consider these types for representing pairs of nats and booleans and also booleans and nats respectively: *)

Inductive nat_and_bool :=
| nnb : nat -> bool -> nat_and_bool.

Inductive bool_and_nat :=
| bnn : bool -> nat -> bool_and_nat.

(** We can write functions that swap these around: *)

Definition swap_nat_and_bool (x : nat_and_bool) : bool_and_nat :=
  match x with
    | nnb n b => bnn b n
  end.

Definition swap_bool_and_nat x :=
  match x with
    | bnn b n => nnb n b
  end.

(** We can also prove that these swaps work as we expect: *)

Lemma swap_swap:
  forall x, swap_nat_and_bool (swap_bool_and_nat x) = x.
Proof.
  intro. destruct x0. reflexivity.
Qed.

(** These definitions are overly specific though, we should define some sort of generic pair type. Unfortunately, our technique for writing parameterized definitions doesn't really cut it here:
<<
Definition pair x y :=
   ... (* what do we put here ?! *)
>>
*)

(** Instead we can use the type [prod]: *)

Print prod.
(** <<
Inductive prod A B :=
  |  pair : A -> B -> A * B
>> *)

(** This is an example of a _parameterized type_.  With it we can write a generic [swap] function: *)

Definition swap (A B: Type) (p: A * B) : B * A :=
  match p with
    | pair a b => pair b a
  end.

(** Note that we don't have to include all the type arguments.  This is due to Coq's inference mechanisms, which we will disucuss in more detail later. *)

(** We can also prove our generic swap correct: *)

Lemma swap_ok:
  forall A B (p: A * B),
  swap B A (swap A B p) = p.
Proof.
  intros. destruct p. reflexivity.
Qed.

(** One parameterized type named [option] is super useful for encoding partial functions: *)

Print option.
(** <<
Inductive option (A : Type) : Type :=
  | Some : A -> option A
  | None : option A.
>> *)

Definition pred (n: nat) : option nat :=
  match n with
    | O => None
    | S m => Some m
  end.

(** Next time we'll talk more about inductive types and how they can be used to encode syntax.  However, you should check out the list type and think about it until then: *)

Print list.
(** <<
Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.
>> *)

Eval cbv in (cons 1 (cons 2 (cons 3 nil))).
