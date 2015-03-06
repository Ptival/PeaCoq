Require Import List.
Require Import String.
Require Import ZArith.

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
| PushHeap : Stmt
| PopHeap : var -> Stmt 
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

  For statements that involve branching (Cond and While), the
  "then" / "enter loop" branch should be taken when the condition
  expression evaluates to something not equal to 0, and the
  "else" / "exit loop" branch should be taken when the condition
  expression evaluates to 0.
*)
| ReduceSkip : forall hs h s,
  Step hs h (Seq Skip s) hs h s
| StepAssign : forall hs h v e c,
  Eval h e c ->
  Step hs h (Assign v e) hs ((v,c) :: h) Skip
| ProgSeq : forall hs h s1 s2 s3 hs' h',
  Step hs h s1 hs' h' s2 ->
  Step hs h (Seq s1 s3) hs' h' (Seq s2 s3)
| CondTrue : forall hs h s1 s2 e c,
  Eval h e c ->
  c <> 0%Z ->
  Step hs h (Cond e s1 s2) hs h s1
| CondFalse : forall hs h s1 s2 e c,
  Eval h e c ->
  c = 0%Z ->
  Step hs h (Cond e s1 s2) hs h s2
| WhileTrue : forall hs h s e c,
  Eval h e c ->
  c <> 0%Z ->
  Step hs h (While e s) hs h (Seq s (While e s))
| WhileFalse : forall hs h s e c,
  Eval h e c ->
  c = 0%Z ->
  Step hs h (While e s) hs h Skip
| StepPushHeap : forall hs h,
  Step hs h PushHeap (h::hs) h Skip
| StepPopHeap : forall hs1 hsr h x v,
  lkup x h = v ->
  Step (hs1::hsr) h (PopHeap x) hsr ((x,v)::hs1) Skip
| StepPopEmptyHeapstack : forall h x,
  Step nil h (PopHeap x) nil h Skip
.

(*
  [PROBLEM 3]
  In a short English paragraph, explain why our language would be much less
  useful if popping a heap did not copy one value from the popped heap.

  If you didn't copy one value, then you'd be in the same state you were when 
  you pushed that heap, so any computation you had done since then would be
  useless. Therefore, there would have been no point in anything you did since
  pushing the heap, and pushing and popping heaps would be useless.
*)

(*
  [PROBLEM 4]
  Give an interesting IMP program that uses both "PushHeap" and "PopHeap x".

This program executes (or is supposed to execute) the classic recursive factorial
program (define (fact n) (if (= n 1) 1 (* n (fact (- n 1))))), but using heap
pushing and popping instead of the function stack. It takes as input "x", and
returns the result in "result". "b" is simply used to mark the bottom of the stack.
(Seq (Assign "b" 0%Z)
(Seq PushHeap
(Seq (Assign "b" 1%Z)
(Seq (Assign "x" 4%Z)
(Seq (While "x"
     (Seq PushHeap
     (Assign "x" (Add "x" -1%Z))))
(Seq (Assign "result" 1%Z)
(Seq (While "b"
     (Seq (Assign "result" (Mul "x" "result"))
     (PopHeap "result"))))))))))
*)*)


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
  match s with
  | Skip => true
  | _ => false
  end.

(* [Problem 6] *)
(* Prove isSkip correct in the true case. *)
Lemma isSkip_t:
  forall s, isSkip s = true -> s = Skip.
Proof.
  intro. destruct s; auto; discriminate.
Qed.

(* [Problem 7] *)
(* Prove isSkip correct in the false case. *)
Lemma isSkip_f:
  forall s, isSkip s = false -> s <> Skip.
intro. destruct s; discriminate.
Qed.

(* [Problem 8] *)
(* Implement step as a function. *)
(* Hint: Z.eq_dec decides if a Z is equal to 0. *)
Check Z.eq_dec. 
Fixpoint step (l: list Heap) (h: Heap) (s: Stmt) :
  option (list Heap * Heap * Stmt) :=
  match s with
  | Skip => None
  | (Seq s1 s2) => 
    if isSkip s1 then
      Some (l,h, s2)
    else 
      match step l h s1 with
      | Some (l', h', s1') => Some (l', h', (Seq s1' s2))
      | None => None
      end
  | Assign v e => Some (l, ((v,(eval h e))::h), Skip)
  | Cond e s1 s2 =>
    if Z.eq_dec (eval h e) 0%Z then
      Some (l, h, s2)
    else
      Some (l, h, s1)
  | While e s =>
    if Z.eq_dec (eval h e) 0%Z then
      Some (l, h, Skip)
    else
      Some (l, h, (Seq s (While e s)))
  | PushHeap => Some (h::l, h, Skip)
  | PopHeap v =>
    match l with
    | nil => Some (l, h, Skip)
    | h'::hs => Some(hs, (v,(lkup v h))::h', Skip)
    end
  end.

(* [Problem 9] *)
(* Prove that only Skip cannot step. *)
Lemma step_None_Skip:
  forall l h s, step l h s = None -> s = Skip.
intros. induction s.
  { reflexivity. }
  { discriminate. }
  { simpl in H. destruct (isSkip s1) eqn:?.
    { discriminate. }
    { apply isSkip_f in Heqb. destruct (step l h s1) eqn:?.
      { destruct p. destruct p. discriminate H. }
      { apply IHs1 in H. contradiction. } } }
  { simpl in H. destruct (Z.eq_dec (eval h e) 0%Z) eqn:?.
    { discriminate. }
    { discriminate. } }
  { simpl in H. destruct (Z.eq_dec (eval h e) 0%Z) eqn:?.
    { discriminate. }
    { discriminate. } }
  { discriminate. }
  { simpl in H. destruct l.
    { discriminate. }
    { discriminate. } }
Qed.

(* [Problem 10] *)
(* Prove that your step function is SOUND with respect to the Step relation. *)
Lemma step_Step:
  forall l h s l' h' s',
  step l h s = Some (l', h', s') -> Step l h s l' h' s'.
Proof.
intro. intro. intro. induction s.
  { discriminate. }
  { intros. simpl in H. inversion H. constructor. apply Eval_eval'. }
  { intros. simpl in *. destruct (isSkip s1) eqn:?.
    { apply isSkip_t in Heqb. inversion H. rewrite -> Heqb. constructor. }
    { apply isSkip_f in Heqb. destruct (step l h s1).
      { destruct p. destruct p. inversion H. subst. constructor. auto. }
      { discriminate. } } }
  { intros. simpl in *. destruct (Z.eq_dec (eval h e) 0) eqn:?.
    { clear Heqs. inversion H. subst. apply eval_Eval in e0. econstructor.
      { eauto. }
      { reflexivity. } }
    { clear Heqs. inversion H. subst. remember (eval h' e).
      symmetry in Heqz. apply eval_Eval in Heqz.
      econstructor.
      { eauto. }
      { assumption. } } }
  { intros. simpl in H. destruct (Z.eq_dec (eval h e) 0) eqn:?.
    { clear Heqs0. inversion H. subst. apply eval_Eval in e0. econstructor.
      { eauto. }
      { reflexivity. } }
    { clear Heqs0. inversion H. subst. remember (eval h' e).
      symmetry in Heqz. apply eval_Eval in Heqz.
      econstructor.
      { eauto. }
      { assumption. } } }
  { intros. simpl in H. inversion H. subst. constructor. }
  { intros. simpl in H. destruct l.
    { inversion H. subst. constructor. }
    { inversion H. subst. constructor. reflexivity.} }
Qed.

(* [Problem 11] *)
(* Prove that your step function is COMPLETE with respect to the step relation. *)
Lemma Step_step:
  forall l h s l' h' s',
  Step l h s l' h' s' -> step l h s = Some (l', h', s').
Proof.
intros. induction H.
{ simpl. reflexivity. }
{ simpl. apply Eval_eval in H. subst. reflexivity. }
{ simpl. destruct (isSkip s1) eqn:?.
  { apply isSkip_t in Heqb. subst. inversion H. }
  { rewrite IHStep. reflexivity. } }
{ simpl. destruct (Z.eq_dec (eval h e) 0) eqn:?. clear Heqs. apply Eval_eval in H. omega. reflexivity. }
{ simpl. destruct (Z.eq_dec (eval h e) 0).
  { reflexivity. }
  { apply Eval_eval in H. omega. } }
{ simpl. destruct (Z_eq_dec (eval h e) 0) eqn:?. clear Heqs0. apply Eval_eval in H. omega. reflexivity. }
{ simpl. destruct (Z.eq_dec (eval h e) 0) eqn:?. reflexivity. apply Eval_eval in H. omega. }
{ simpl. reflexivity. }
{ simpl. subst. reflexivity. }
{ simpl. reflexivity. }
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
    match n with
    | 0 => Some (l,h,s)
    | S m => match step l h s with
             | Some (l',h',s') => stepn l' h' s' m
             | None => None
             end
    end.

(* [Problem 13] *)
(* Prove your stepn function SOUND. *)
Lemma stepn_StepN:
  forall n l h s l' h' s',
  stepn l h s n = Some (l', h', s') ->
  StepN l h s n l' h' s'.
Proof.
  intro. induction n.
  { intros. simpl in H. inversion H. left. }
  { intros. simpl in H. destruct (step l h s) eqn:?.
    { destruct p. destruct p. apply step_Step in Heqo. econstructor.
      { eassumption. }
      { eauto. }
    }
    { discriminate. }
  }
Qed.

(* [Problem 14] *)
(* Prove your stepn function COMPLETE. *)
Lemma StepN_stepn:
  forall l h s n l' h' s',
  StepN l h s n l' h' s' ->
  stepn l h s n = Some (l', h', s').
intros. induction H.
  { reflexivity. }
  { simpl. destruct (step l h s) eqn:?.
    { destruct p. simpl. destruct p. apply Step_step in H. congruence. }
    { apply Step_step in H. congruence. } }
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
| StepStar_refl : forall hs h s,
  StepStar hs h s hs h s
| StepStar_step: forall hs h s hs' h' s' hs'' h'' s'',
  StepStar hs' h' s' hs'' h'' s'' ->
  Step hs h s hs' h' s' ->
  StepStar hs h s hs'' h'' s''
.

(* [Problem 16] *)
(* Prove that run is SOUND with respect to StepStar. *)
Lemma run_StepStar:
  forall n l h s l' h' s',
  run n l h s = (l', h', s') -> StepStar l h s l' h' s'.
Proof.
  intro. induction n.
  { intros. simpl in H. inversion H. left. }
  { intros. simpl in H. destruct (step l h s) eqn:?.
    { destruct p. destruct p. apply step_Step in Heqo. apply IHn in H. econstructor.
      { eassumption. }
      { eassumption. }
    }
    { inversion H. left. }
  }
Qed.

(* [Problem 17] *)
(* Prove that running a state that can't step gives that same state. *)
Lemma nostep_run_refl:
  forall l h s, step l h s = None ->
  forall n, run n l h s = (l, h, s).
Proof.
  intros. apply step_None_Skip in H. subst. induction n.
  { reflexivity. }
  { reflexivity. }
Qed.

(* [Problem 18] *)
(* Prove that two consecutive runs are the same as one bigger run. *)
Lemma run_combine:
  forall m n l h s l' h' s' l'' h'' s'',
  run m l h s = (l', h', s') ->
  run n l' h' s' = (l'', h'', s'') ->
  run (m + n) l h s = (l'', h'', s'').
intro. induction m.
  { intros. simpl. simpl in H. inversion H. assumption. }
  { intros. simpl. simpl in H. destruct (step l h s) eqn:?.
    { destruct p. destruct p. eauto. }
    { inversion H. subst. apply nostep_run_refl with ( n := n) in Heqo.  congruence. } }
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
  induction s ; intros.
  { inversion H. }
  { inversion H. constructor. }
  { inversion H. destruct s' ; auto.
    { inversion H0. subst.
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
  forall s x,
  equiv (Seq s (Assign x (Int 0%Z))
        (Seq PushHeap (Seq s (PopHeap x))).
Proof.
  (* TODO *)
  admit.
Qed.
