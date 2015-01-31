Require Import List.
Require Import String.
Require Import ZArith.

Ltac break_if :=
  match goal with
    | _ : context [ if ?cond then _ else _ ] |- _ =>
     destruct cond as [] eqn:?
    | |- context [ if ?cond then _ else _ ] =>
      destruct cond as [] eqn:?
    | _ : context [ match ?cond with _ => _ end ] |- _ =>
     destruct cond as [] eqn:?
    | |- context [ match ?cond with _ => _ end ] =>
      destruct cond as [] eqn:?
  end.

(*
  We will extend IMP with the ability to push and pop heaps.

  In normal IMP, program states just included the heap "h" and
  statement to execute "s".

  In our extended version of IMP, program state will also include
  the current stack of heaps "l", represented as a list.

  There will be two new statements: "PushHeap" and "PopHeap x".
    - "PushHeap" adds the current heap "h" to the beginning of "l".
      Informally, it copies "h" all at once.
    - "PopHeap x" replaces the current heap "h" with the first
      element of "l" *except* "x" maps to "lkup x h" and replaces "l"
      with the tail of "l".  If "l" is the empty list, then
     "PopHeap x" has no effect.
  Both "PushHeap" and "PopHeap x" become Skip in one step.
*)

Set Implicit Arguments.

Definition var := string.

(* We'll start by defining the syntax of our extended IMP. *)

(* Expressions are just like those from IMP seen in lecture. *)
Inductive Expr : Type :=
| Int : Z -> Expr
| Var : var -> Expr
| Add : Expr -> Expr -> Expr
| Mul : Expr -> Expr -> Expr.

(* Add the PushHeap and PopHeap x statements to the Stmt type. *)
Inductive Stmt : Type :=
| Skip : Stmt
| Assign : var -> Expr -> Stmt
| Seq : Stmt -> Stmt -> Stmt
| Cond : Expr -> Stmt -> Stmt -> Stmt
| While : Expr -> Stmt -> Stmt
(*
  [PROBLEM 1]
  Add constructors for PushHeap and PopHeap x here.
*)
.

(* Next we define the semantics of our language *)

(* Heaps are represented as association lists. *)
Definition Heap := list (var * Z).

Fixpoint lkup (x: var) (h: Heap) :=
  match h with
    | nil => 0%Z
    | (k, v) :: h' => if string_dec x k then v else lkup x h'
  end.

(* Since expressions are unchanged from IMP, their semantics are the same: *)
Inductive Eval : Heap -> Expr -> Z -> Prop :=
| EInt : forall h z,
  Eval h (Int z) z
| EVar : forall h v,
  Eval h (Var v) (lkup v h)
| EAdd : forall h e1 e2 c1 c2 c3,
  Eval h e1 c1 ->
  Eval h e2 c2 ->
  c3 = (c1 + c2)%Z ->
  Eval h (Add e1 e2) c3
| EMul : forall h e1 e2 c1 c2 c3,
  Eval h e1 c1 ->
  Eval h e2 c2 ->
  c3 = (c1 * c2)%Z ->
  Eval h (Mul e1 e2) c3.

(*
  Define a small-step operational semantics for our extended version of IMP.
  Because the form of rules has changed, include all the rules.
*)
Inductive Step : list Heap -> Heap -> Stmt ->
                 list Heap -> Heap -> Stmt -> Prop :=
(*
  [PROBLEM 2]
  Add the rules (constructors) for the small step semantics of
  our extended version of IMP.  I have 10 rules in my solution.

  * NOTE *
  For statements that involve branching (Cond and While), the
  "then" / "enter loop" branch should be taken when the condition
  expression evaluates to something not equal to 0, and the
  "else" / "exit loop" branch should be taken when the condition
  expression evaluates to 0.
*)
.

(*
  [PROBLEM 3]
  In a short English paragraph, explain why our language would be much less
  useful if popping a heap did not copy one value from the popped heap.
*)

(*
  [PROBLEM 4]
  Give an interesting IMP program that uses both "PushHeap" and "PopHeap x".
*)

(* Interpreters *)

(*
  In class we saw how to implement and verify a function
  that evaluates expressions:
*)

Fixpoint eval (h: Heap) (e: Expr) : Z :=
  match e with
    | Int z => z
    | Var v => lkup v h
    | Add e1 e2 => Z.add (eval h e1) (eval h e2)
    | Mul e1 e2 => Z.mul (eval h e1) (eval h e2)
  end.

Lemma eval_Eval:
  forall h e c,
  eval h e = c -> Eval h e c.
Proof.
  intro. intro. induction e.
  { intros. simpl in *. subst. constructor. }
  { intros. simpl in *. rewrite <- H. constructor. }
  { intros. simpl in *. econstructor.
    { firstorder. }
    { firstorder. }
    { firstorder. }
  }
  { intros. simpl in *. econstructor.
    { firstorder. }
    { firstorder. }
    { firstorder. }
  }
Qed.

Lemma Eval_eval:
  forall h e c,
  Eval h e c -> eval h e = c.
Proof.
  intros. induction H.
  { reflexivity. }
  { reflexivity. }
  { subst. reflexivity. }
  { subst. reflexivity. }
Qed.

Lemma Eval_eval':
  forall h e,
  Eval h e (eval h e).
Proof.
  intros. remember (eval h e) as c. apply eval_Eval. omega.
Qed.


(* [Problem 5] *)
(* Write a function which tests whether a statement is a Skip statement. *)
Definition isSkip (s: Stmt) : bool :=
 (* TODO *)
 false.

(* [Problem 6] *)
(* Prove isSkip correct in the true case. *)
Lemma isSkip_t:
  forall s, isSkip s = true -> s = Skip.
Proof.
  (* TODO *)
  admit.
Qed.

(* [Problem 7] *)
(* Prove isSkip correct in the false case. *)
Lemma isSkip_f:
  forall s, isSkip s = false -> s <> Skip.
Proof.
  (* TODO *)
  admit.
Qed.

(* [Problem 8] *)
(* Implement step as a function. *)
(* Hint: Use your isSkip function in the Seq case. *)
(* Hint: Z.eq_dec decides if a Z is equal to 0. *)
Check Z.eq_dec.
Fixpoint step (l: list Heap) (h: Heap) (s: Stmt) :
  option (list Heap * Heap * Stmt) :=
  (* TODO *)
  None.

(* [Problem 9] *)
(* Prove that only Skip cannot step. *)
Lemma step_None_Skip:
  forall l h s, step l h s = None -> s = Skip.
Proof.
  (* TODO *)
  admit.
Qed.

(* [Problem 10] *)
(* Prove that your step function is SOUND with respect to the Step relation. *)
Lemma step_Step:
  forall l h s l' h' s',
  step l h s = Some (l', h', s') -> Step l h s l' h' s'.
Proof.
  (* TODO *)
  admit.
Qed.

(* [Problem 11] *)
(* Prove that your step function is COMPLETE with respect to the Step relation. *)
Lemma Step_step:
  forall l h s l' h' s',
  Step l h s l' h' s' -> step l h s = Some (l', h', s').
Proof.
  (* TODO *)
  admit.
Qed.

(* StepN as seen in class *)
Inductive StepN : list Heap -> Heap -> Stmt -> nat ->
                  list Heap -> Heap -> Stmt -> Prop :=
| StepN_refl : forall l h s,
  StepN l h s 0 l h s
| StepN_step : forall l h s l' h' s' l'' h'' s'' n,
  Step l h s l' h' s' ->
  StepN l' h' s' n l'' h'' s'' ->
  StepN l h s (S n) l'' h'' s''.

(* [Problem 12] *)
(* Implement stepn as a function. *)
Fixpoint stepn (l: list Heap) (h: Heap) (s: Stmt) (n: nat) :
  option (list Heap * Heap * Stmt) :=
  (* TODO *)
  None.

(* [Problem 13] *)
(* Prove your stepn function SOUND. *)
Lemma stepn_StepN:
  forall n l h s l' h' s',
  stepn l h s n = Some (l', h', s') ->
  StepN l h s n l' h' s'.
Proof.
  (* TODO *)
  admit.
Qed.

(* [Problem 14] *)
(* Prove your stepn function COMPLETE. *)
Lemma StepN_stepn:
  forall l h s n l' h' s',
  StepN l h s n l' h' s' ->
  stepn l h s n = Some (l', h', s').
Proof.
  (* TODO *)
  admit.
Qed.

(* The run function, which takes up to n steps. *)
Fixpoint run (n: nat) (l: list Heap) (h: Heap) (s: Stmt) : list Heap * Heap * Stmt :=
  match n with
    | O => (l, h, s)
    | S m =>
      match step l h s with
        | Some (l', h', s') => run m l' h' s'
        | None => (l, h, s)
      end
  end.

(* [Problem 15] *)
(* Define the StepStar relation, which corresponds to taking any number of steps. *)
Inductive StepStar : list Heap -> Heap -> Stmt ->
                     list Heap -> Heap -> Stmt -> Prop :=
  (* TODO *)
.

(* [Problem 16] *)
(* Prove that run is SOUND with respect to StepStar. *)
Lemma run_StepStar:
  forall n l h s l' h' s',
  run n l h s = (l', h', s') -> StepStar l h s l' h' s'.
Proof.
  (* TODO *)
  admit.
Qed.

(* [Problem 17] *)
(* Prove that running a state that can't step gives that same state. *)
Lemma nostep_run_refl:
  forall l h s, step l h s = None ->
  forall n, run n l h s = (l, h, s).
Proof.
  (* TODO *)
  admit.
Qed.

(* [Problem 18] *)
(* Prove that two consecutive runs are the same as one bigger run. *)
Lemma run_combine:
  forall m n l h s l' h' s' l'' h'' s'',
  run m l h s = (l', h', s') ->
  run n l' h' s' = (l'', h'', s'') ->
  run (m + n) l h s = (l'', h'', s'').
Proof.
  (* TODO *)
  admit.
Qed.


(* Here we define what it means for a statement to contain a while. *)
Fixpoint hasWhile (s: Stmt) : bool :=
  match s with
    | Skip => false
    | Assign _ _ => false
    | Seq s1 s2 => orb (hasWhile s1) (hasWhile s2)
    | Cond _ s1 s2 =>  orb (hasWhile s1) (hasWhile s2)
    | While _ _ => true
    | PushHeap => false
    | PopHeap _ => false
  end.

(* Here we define the number of PushHeap statements contained in a statement. *)
Fixpoint nPushHeap (s: Stmt) : nat :=
  match s with
    | Skip => 0
    | Assign _ _ => 0
    | Seq s1 s2 => nPushHeap s1 + nPushHeap s2
    | Cond _ s1 s2 => nPushHeap s1 + nPushHeap s2
    | While _ s1 => nPushHeap s1
    | PushHeap => 1
    | PopHeap _ => 0
  end.

(*
  [Problem 19]
  Prove that if we take a step from a statement without any whiles,
  then the resulting statement still has no whiles.
*)
Lemma hasWhileStep:
  forall l h s l' h' s',
    Step l h s l' h' s' ->
    hasWhile s = false ->
    hasWhile s' = false.
Proof.
  (* TODO *)
  admit.
Qed.

(* *** A BIT TRICKY! *** *)
(*
  [Problem 20]

  State and prove the following property:
    If statement s has no While loops and from the empty stack
    (l = nil) and empty heap (h = nil), s can step to stack l',
    heap h', and statement s', then the length of l' does not
    exceed the number of PushHeap statements in s (the original
    statement).

  Hints:
    - You will need two lemmas to prove this.
    - Think carefully about your induction hypotheses.
*)

(*
  [Problem 21]

  Prove the previous claim is false if we allow s to contain
  While loops.

  Hint:
    - No need to use induction.
*)

(* Define a weak notion of equivalence between programs. *)
Definition equiv (s1 s2: Stmt) :=
  forall l1' h1' l2' h2',
  StepStar nil nil s1 l1' h1' Skip ->
  StepStar nil nil s2 l2' h2' Skip ->
  l1' = l2' /\ h1' = h2'.

(*
  [Problem 22]
  Prove the following equivalence.
*)
Lemma progs_equiv:
  ~ (forall s x,
  equiv (Seq s (Assign x (Int 0%Z))
        (Seq PushHeap (Seq s (PopHeap x)))).
Proof.
  (* TODO *)
  admit.
Qed.
