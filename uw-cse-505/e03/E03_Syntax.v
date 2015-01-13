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
