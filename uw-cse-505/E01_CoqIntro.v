(** 

Let us kick things off with a lightning fast introduction to Coq:
   https://coq.inria.fr/

Comments go between "(*" and "*)".  We're in a comment right now!

This _binding_ associates the name [x] with the expression [0]:

*)

Definition x := 0.

(** 

Coq code is primarily a sequence of bindings.

We can step through the bindings and process one at a time by pressing Control-Alt-Down.

When we process a binding Coq does the following:
- Evaluate the expression to the right of the ":=" using the existing environment.
- This produces a value.
- Extend the environment to bind the name to the value.

We can use a "command" to ask Coq to print expressions too.

The [Print] command prints the value of an expression.

*)

Print x.

(**

The _Check_ command just prints the type of an expression.

*)

Check x.











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




