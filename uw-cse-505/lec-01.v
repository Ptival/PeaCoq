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




