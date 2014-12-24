(** * Episode 1: A Quick Introduction to Coq

Comments are real important. They go between paren star / star paren like this:
<<
  (* this is a comment *)
>>
We're in a comment right now!

This _binding_ associates the name [x] to the expression [0]:

*)

Definition x := 0.

(** 

Coq code is primarily a sequence of bindings. We can step through the bindings and process them one at a time by pressing:
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

Coq also has _commands_ which let us poke around and ask Coq questions about the bindings we have processed so far.

The [Print] command displays the value associated with a name:

 *)

Print x.

(** 

The [Check] command displays the type of an expression:

*)

Check x.

(** 

The [Eval cbv in] command evaluates an expression to a value:

*)

Eval cbv in (1 + 1).










(* Simple Inductive Definitions *)

Inductive boolean : Type :=
| true
| false.

Inductive positive_numbers_under_ten : Type :=
| one
| two
| three
| four
| five
| six
| seven
| eight
| nine.

Definition pnut : Type :=
  positive_numbers_under_ten.

(* Functions *)

Definition boolean_negation : boolean -> boolean :=
  fun (b: boolean) =>
    match b with
      | true => false
      | false => true
    end.

Definition boolean_negation' (b: boolean) : boolean :=
  match b with
    | true => false
    | false => true
  end.

Definition pnut_scramble (n : pnut) : pnut :=
  (* TODO scramble *)
  match n with
    | one => one
    | two => two
    | three => three
    | four => four
    | five => five
    | six => six
    | seven => seven
    | eight => eight
    | nine => nine
  end.

(* What about successor? It's a partial function... *)

Definition identity (T: Type) (v: T) : T :=
  v.

(* Parameterized Types *)

Inductive option (T: Type) : Type :=
| Some : T -> option T
| None : option T.

(* More Functions *)

Definition pnut_successor (n : pnut) : option pnut :=
  match n with
    | one => Some pnut two
    | two => Some pnut three
    | three => Some pnut four
    | four => Some pnut five
    | five => Some pnut six
    | six => Some pnut seven
    | seven => Some pnut eight
    | eight => Some pnut nine
    | nine => None pnut
  end.




