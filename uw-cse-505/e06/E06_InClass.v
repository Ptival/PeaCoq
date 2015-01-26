Require Import List.
Require Import String.
Require Import ZArith.

Definition var := string.

Set Implicit Arguments.

Definition injective A B (f: A -> B) :=
  forall x y, f x = f y -> x = y.

(* notree *)
Lemma retfalse_noninj:
  ~ (injective (fun x:bool => false)).
Proof.
  unfold injective. unfold not.
  intro. specialize (H true false).
  specialize (H (eq_refl false)).
  discriminate.
Qed.

Inductive foo :=
| Ctor : nat -> foo.

Lemma ctor_inj:
  forall x y, Ctor x = Ctor y -> x = y.
Proof.
  intros. inversion H. auto.
Qed.

(* expressions *)
Inductive Expr : Type :=
| Int : Z -> Expr
| Var : var -> Expr
| Add : Expr -> Expr -> Expr
| Mul : Expr -> Expr -> Expr.

(* statements *)
Inductive Stmt : Type :=
| Skip : Stmt
| Assign : var -> Expr -> Stmt
| Seq : Stmt -> Stmt -> Stmt
| Cond : Expr -> Stmt -> Stmt -> Stmt
| While : Expr -> Stmt -> Stmt.

Definition Heap := list (var * Z).

Fixpoint lkup (x: var) (h: Heap) :=
  match h with
    | nil => 0%Z
    | (k, v) :: h' => if string_dec x k then v else lkup x h'
  end.

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

Inductive Step : Heap -> Stmt -> Heap -> Stmt -> Prop :=
| SAssign : forall h v e c,
  Eval h e c ->
  Step h (Assign v e) ((v, c) :: h) Skip
| SSeq1 : forall h s,
  Step h (Seq Skip s) h s
| SSeq2 : forall h s1 h' s1' s2,
  Step h s1 h' s1' ->
  Step h (Seq s1 s2) h' (Seq s1' s2)
| SCondT : forall h e c s1 s2,
  Eval h e c ->
  c <> 0%Z ->
  Step h (Cond e s1 s2) h s1
| SCondF : forall h e c s1 s2,
  Eval h e c ->
  c = 0%Z ->
  Step h (Cond e s1 s2) h s2
| SWhileT : forall h e c s,
  Eval h e c ->
  c <> 0%Z ->
  Step h (While e s) h (Seq s (While e s))
| SWhileF : forall h e c s,
  Eval h e c ->
  c = 0%Z ->
  Step h (While e s) h Skip.

Inductive StepN : Heap -> Stmt -> nat ->
                  Heap -> Stmt -> Prop :=
| StepN_refl : forall h s,
  StepN h s 0 h s
| StepN_step : forall h s h' s' h'' s'' n,
  Step h s h' s' ->
  StepN h' s' n h'' s'' ->
  StepN h s (S n) h'' s''.

(** Divergence *)

(* notree *)
Lemma diverges_take1:
  forall h n, exists h', exists s',
  StepN h (While (Int 1) Skip) n h' s'.
Proof.
Admitted.
(*
  induction n.
  { exists h. exists (While (Int 1) Skip).
    constructor. }
  { firstorder. rename x into hX. 
    rename x0 into sX. 
*)

Definition w1 := While (Int 1) Skip.
Definition w2 := Seq Skip w1.

Lemma StepN_right:
  forall h s n h' s',
  StepN h s n h' s' ->
  forall h'' s'',
  Step h' s' h'' s'' ->
  StepN h s (S n) h'' s''.
Proof.
  induction 1. intros.
  { econstructor; eauto. econstructor; eauto. }
  { firstorder. repeat (econstructor; eauto). }
Qed. 

Lemma diverges:
  forall h n, exists s,
  StepN h w1 n h s /\
  (s = w1 \/ s = w2).
Proof.
  intros. induction n.
  { exists w1. constructor.
    constructor. left. reflexivity.
  }
  { firstorder. subst.
    exists w2. split.
    eapply StepN_right.
    { exact H. }
    { unfold w1, w2. apply SWhileT with (c := 1%Z). constructor. omega. }
  { auto. }
Admitted.

(** Interpreters *)

Locate "+".

Fixpoint eval (h: Heap) (e: Expr) : Z :=
  match e with
    | Int z => z
    | Var v => lkup v h
    | Add e1 e2 => Z.add (eval h e1) (eval h e2)
    | Mul e1 e2 => Z.mul (eval h e1) (eval h e2)
  end.

(* notree *)
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

(* notree *)
Lemma Eval_eval:
  forall h e c,
  Eval h e c -> eval h e = c.
Proof.
  intros. induction H.
  { reflexivity. }
  { reflexivity. }
  { subst. simpl. reflexivity. }
  { subst. reflexivity. }
Qed.

(* notree *)
Lemma Eval_eval':
  forall h e,
  Eval h e (eval h e).
Proof.
  intros. remember (eval h e) as c. apply eval_Eval. omega.
Qed.

Check Z.eq_dec.

Definition isSkip (s: Stmt) : bool :=
  match s with
    | Skip => true
    | _ => false
  end.

(* notree *)
Lemma isSkip_t:
  forall s, isSkip s = true -> s = Skip.
Proof.
  intros. destruct s.
  { reflexivity. }
  { discriminate. }
  { discriminate. }
  { discriminate. }
  { discriminate. }
Qed.

(* notree *)
Lemma isSkip_f:
  forall s, isSkip s = false -> s <> Skip.
Proof.
  intros. destruct s.
  { discriminate. }
  { discriminate. }
  { discriminate. }
  { discriminate. }
  { discriminate. }
Qed.

Fixpoint step (h: Heap) (s: Stmt) :
  option (Heap * Stmt) :=
  match s with
    | Skip => None
    | Assign v e =>
      Some ((v, eval h e)::h, Skip)
    | Seq s1 s2 =>
      if isSkip s1 then
        Some (h, s2)
      else
        match step h s1 with
          | Some (h', s1') =>
            Some (h', Seq s1' s2)
          | None => None
        end
    | Cond e s1 s2 =>
        if Z.eq_dec (eval h e) 0%Z then
          Some (h, s2)
        else
          Some (h, s1)
    | While e s =>
        if Z.eq_dec (eval h e) 0%Z then
          Some (h, Skip)
        else
          Some (h, Seq s (While e s))
  end.

(* notree *)
Lemma step_None_Skip:
  forall h s, step h s = None -> s = Skip.
Proof.
  intros. induction s.
  { reflexivity. }
  { simpl in *. inversion H. }
  { simpl in *. destruct (isSkip s1) eqn:?.
    { discriminate. }
    { destruct (step h s1) eqn:?.
      { destruct p. discriminate. }
      { firstorder. apply isSkip_f in Heqb. firstorder. }
    }
  }
  { simpl in *. destruct (Z.eq_dec (eval h e) 0) eqn:?.
    { discriminate. }
    { discriminate. }
  }
  { simpl in *. destruct (Z.eq_dec (eval h e) 0) eqn:?.
    { discriminate. }
    { discriminate. }
  }
Qed.

(* notree *)
Lemma step_Step:
  forall h s h' s',
  step h s = Some (h', s') -> Step h s h' s'.
Proof.
  intro. intro. induction s.
  { discriminate. }
  { intros. simpl in *. inversion H. constructor. apply Eval_eval'. }
  { intros. simpl in *. destruct (isSkip s1) eqn:?.
    { apply isSkip_t in Heqb. inversion H. subst. constructor. }
    { apply isSkip_f in Heqb. destruct (step h s1) eqn:?.
      { destruct p. inversion H. subst. constructor. firstorder. }
      { discriminate. }
    }
  }
  { intros. simpl in *. destruct (Z.eq_dec (eval h e) 0) eqn:?.
    { clear Heqs. inversion H. subst. apply eval_Eval in e0.
      econstructor.
      { eauto. }
      { reflexivity. }
    }
    { clear Heqs. inversion H. subst. remember (eval h' e).
      symmetry in Heqz. apply eval_Eval in Heqz.
      econstructor.
      { eauto. }
      { assumption. }
    }
  }
  { intros. simpl in *. destruct (Z.eq_dec (eval h e) 0) eqn:?.
    { clear Heqs0. inversion H. subst. apply eval_Eval in e0.
      econstructor.
      { eauto. }
      { reflexivity. }
    }
    { clear Heqs0. inversion H. subst. remember (eval h' e).
      symmetry in Heqz. apply eval_Eval in Heqz.
      econstructor.
      { eauto. }
      { assumption. }
    }
  }
Qed.

(* notree *)
Lemma Step_step:
  forall h s h' s',
  Step h s h' s' -> step h s = Some (h', s').
Proof.
  intros. induction H.
  { simpl. apply Eval_eval in H. subst. constructor. }
  { constructor. }
  { simpl. destruct (isSkip s1) eqn:?.
    { apply isSkip_t in Heqb. subst. inversion H. }
    { rewrite IHStep. reflexivity. }
  }
  { simpl. destruct (Z.eq_dec (eval h e) 0) eqn:?.
    { apply Eval_eval in H. omega. }
    { reflexivity. }
  }
  { simpl. destruct (Z.eq_dec (eval h e) 0) eqn:?.
    { reflexivity. }
    { apply Eval_eval in H. omega. }
  }
  { simpl. destruct (Z.eq_dec (eval h e) 0) eqn:?.
    { apply Eval_eval in H. omega. }
    { reflexivity. }
  }
  { simpl. destruct (Z.eq_dec (eval h e) 0) eqn:?.
    { reflexivity. }
    { apply Eval_eval in H. omega. }
  }
Qed.

Fixpoint stepn (h: Heap)  (s: Stmt) (n: nat) : option (Heap * Stmt) :=
  match n with
    | O => Some (h, s)
    | S m =>
      match step h s with
        | Some st' => stepn (fst st') (snd st') m
        | None => None
      end
  end.

(* notree *)
Lemma stepn_StepN:
  forall n h s h' s',
  stepn h s n = Some (h', s') ->
  StepN h s n h' s'.
Proof.
  intro. induction n.
  { intros. simpl in *. inversion H. subst. constructor. }
  { intros. simpl in *. destruct (step h s) eqn:?.
    { destruct p. simpl in *. econstructor.
      { apply step_Step. eassumption. }
      { apply IHn. eassumption. }
    }
    { discriminate. }
  }
Qed.

(* notree *)
Lemma StepN_stepn:
  forall h s n h' s',
  StepN h s n h' s' ->
  stepn h s n = Some (h', s').
Proof.
  intros. induction H.
  { simpl. reflexivity. }
  { simpl. destruct (step h s) eqn:?.
    { destruct p. simpl. apply Step_step in H. congruence. }
    { apply Step_step in H. congruence. }
  }
Qed.

Fixpoint run (n: nat) (h: Heap)  (s: Stmt) : Heap * Stmt :=
  match n with
    | O => (h, s)
    | S m =>
      match step h s with
        | Some (h', s') => run m h' s'
        | None => (h, s)
      end
  end.

Inductive StepStar : Heap -> Stmt -> Heap -> Stmt -> Prop :=
| StepStar_refl : forall h s,
  StepStar h s h s
| StepStar_step : forall h s h' s' h'' s'',
  Step h s h' s' ->
  StepStar h' s' h'' s'' ->
  StepStar h s h'' s''.

(* notree *)
Lemma run_StepStar:
  forall n h s h' s',
  run n h s = (h', s') -> StepStar h s h' s'.
Proof.
  intro. induction n.
  { intros. simpl in *. inversion H. subst. constructor. }
  { intros. simpl in *. destruct (step h s) eqn:?.
    { destruct p. econstructor.
      { apply step_Step. eassumption. }
      { apply IHn. assumption. }
    }
    { inversion H. subst. constructor. }
  }
Qed.

(* notree *)
Lemma nostep_run_refl:
  forall h s, step h s = None ->
  forall n, run n h s = (h, s).
Proof.
  intros. destruct n.
  { simpl. reflexivity. }
  { simpl. rewrite H. reflexivity. }
Qed.

(* notree *)
Lemma run_combine:
  forall m n h s h' s' h'' s'',
  run m h s = (h', s') ->
  run n h' s' = (h'', s'') ->
  run (m + n) h s = (h'', s'').
Proof.
  intro. induction m.
  { intros. simpl in *. inversion H. subst. assumption. }
  { intros. simpl in *. destruct (step h s) eqn:?.
    { destruct p. eapply IHm.
      { eauto. }
      { eauto. }
    }
    { inversion H. subst. apply nostep_run_refl with (n := n) in Heqo.
      congruence.
    }
  }
Qed.


    










Definition canStep h s :=
  exists h', exists s', Step h s h' s'.

Definition notSkip s :=
  match s with
  | Skip => False
  | _ => True
  end.

Lemma notSkip_canStep:
  forall h s, notSkip s -> canStep h s.
Admitted.

