(** * Episode 03: Syntax *)

Require Import List.

(*

BNF : Backus Naur Form

A BNF is a concise way of describing a set of objects.

  bit ::= 0 | 1

  binary_string ::= bit | binary_string bit

  (* in class *)
  parens ::= () | ( parens ) | parens parens

BNF is a metalanguage.

Normally write in concrete syntax.

Can be ambiguous.

Converting concrete syntax to abstract syntax is parsing.

*)

Definition name := nat.

(* why expr first? *)
Inductive expr : Set :=
| const : nat -> expr
| var : name -> expr
| add : expr -> expr -> expr
| mul : expr -> expr -> expr.

Inductive stmt : Set :=
| skip : stmt
| updt : name -> expr -> stmt
| seq : stmt -> stmt -> stmt
| branch : expr -> stmt -> stmt -> stmt
| loop : expr -> stmt -> stmt.

Fixpoint nconsts (e: expr) : nat :=
  match e with
    | const n => 1
    | var v => 0
    | add l r => nconsts l + nconsts r
    | mul l r => nconsts l + nconsts r
  end.

Lemma has_3_consts:
  exists e, nconsts e = 3.
Proof.
  exists (add (const 1) (add (const 1) (const 1))). reflexivity.
Qed.

Check orb.

(*

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
    | add l r => orb (has_const l) (has_const r)
    | mul l r => orb (has_const l) (has_const r)
  end.

Lemma bottoms_out:
  forall e, has_const e = true \/ has_var e = true.

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
