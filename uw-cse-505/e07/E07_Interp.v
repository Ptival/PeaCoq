Require Import List.
Require Import String.
Require Import ZArith.

Set Implicit Arguments.

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

Definition var := string.

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
    | (k, v) :: h' =>
      if string_dec x k then
        v
      else
        lkup x h'
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

Inductive Step : Heap -> Stmt ->
                 Heap -> Stmt -> Prop :=
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

(** Interpreters *)

Locate "+".

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
  { simpl. intros. subst. constructor. }
  { simpl. intros. subst. constructor. }
  { simpl. intros. subst. econstructor.
    { auto. }
    { auto. }
    { reflexivity. }
  }
  { simpl. intros. subst. econstructor.
    { auto. }
    { auto. }
    { reflexivity. }
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
  intros. apply eval_Eval. reflexivity.
Qed.

Check Z.eq_dec.

Definition isSkip (s: Stmt) : bool :=
  match s with
    | Skip => true
    | _ => false
  end.

Lemma isSkip_t:
  forall s, isSkip s = true -> s = Skip.
Proof.
  intro. destruct s.
  { reflexivity. }
  { discriminate. }
  { discriminate. }
  { discriminate. }
  { discriminate. }
Qed.

Lemma isSkip_f:
  forall s, isSkip s = false -> s <> Skip.
Proof.
  intro. destruct s.
  { discriminate. }
  { discriminate. }
  { discriminate. }
  { discriminate. }
  { discriminate. }
Qed.

Fixpoint step (h: Heap) (s: Stmt)
  : option (Heap * Stmt) :=
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

Lemma step_None_Skip:
  forall h s,
  step h s = None ->
  s = Skip.
Proof.
  intros. induction s.
  { reflexivity. }
  { discriminate. }
  { simpl in *. break_if.
    { discriminate. }
    { break_if.
      { destruct p. discriminate. }
      { apply isSkip_f in Heqb. firstorder. }
    }
  }
  { simpl in *. break_if.
    { discriminate. }
    { discriminate. }
  }
  { simpl in *. break_if.
    { discriminate. }
    { discriminate. }
  }
Qed.

Lemma step_Step:
  forall h s h' s',
  step h s = Some (h', s') ->
  Step h s h' s'.
Proof.
  intro. intro. induction s.
  { discriminate. }
  { intros. simpl in *. inversion H.
    constructor. apply Eval_eval'. }
  { intros. simpl in *. break_if.
    { apply isSkip_t in Heqb.
     inversion H. subst.
     constructor. }
    { apply isSkip_f in Heqb. break_if.
      { destruct p. inversion H. subst.
        constructor. firstorder. }
      { discriminate. }
    }
  }
  { intros. simpl in *. break_if.
    { inversion H. subst.
      clear Heqs. apply eval_Eval in e0.
      econstructor.
      { eauto. }
      { reflexivity. }
    }
    { inversion H. subst. remember (eval h' e).
      symmetry in Heqz. apply eval_Eval in Heqz.
      econstructor.
      { eauto. }
      { assumption. }
    }
  }
  { intros. simpl in *. break_if.
    { inversion H. subst.
      clear Heqs0. apply eval_Eval in e0.
      econstructor.
      { eauto. }
      { reflexivity. }
    }
    { inversion H. subst.
      remember (eval h' e).
      symmetry in Heqz. apply eval_Eval in Heqz.
      econstructor.
      { eauto. }
      { assumption. }
    }
  }
Qed.

Lemma Step_step:
  forall h s h' s',
  Step h s h' s' -> step h s = Some (h', s').
Proof.
  intros. induction H.
  { simpl. apply Eval_eval in H.
    subst. constructor. }
  { constructor. }
  { simpl. break_if.
    { apply isSkip_t in Heqb. subst.
      inversion H. }
    { rewrite IHStep. reflexivity. }
  }
  { simpl. break_if.
    { apply Eval_eval in H. omega. }
    { reflexivity. }
  }
  { simpl. break_if.
    { reflexivity. }
    { apply Eval_eval in H. omega. }
  }
  { simpl. break_if.
    { apply Eval_eval in H. omega. }
    { reflexivity. }
  }
  { simpl. break_if.
    { reflexivity. }
    { apply Eval_eval in H. omega. }
  }
Qed.

Fixpoint stepn (h: Heap) (s: Stmt) (n: nat)
  : option (Heap * Stmt) :=
  match n with
    | O => Some (h, s)
    | S m =>
      match step h s with
        | Some (h', s') => stepn h' s' m
        | None => None
      end
  end.

Lemma stepn_StepN:
  forall n h s h' s',
  stepn h s n = Some (h', s') ->
  StepN h s n h' s'.
Proof.
  intro. induction n.
  { intros. simpl in *. 
    inversion H. subst.
    constructor. }
  { intros. simpl in *. break_if.
    { destruct p. simpl in *. econstructor.
      { apply step_Step. eassumption. }
      { apply IHn. eassumption. }
    }
    { discriminate. }
  }
Qed.

Lemma StepN_stepn:
  forall h s n h' s',
  StepN h s n h' s' ->
  stepn h s n = Some (h', s').
Proof.
  intros. induction H.
  { simpl. reflexivity. }
  { simpl. break_if.
    { destruct p. simpl.
      apply Step_step in H. congruence. }
    { apply Step_step in H. congruence. }
  }
Qed.

Fixpoint run (n: nat) (h: Heap) (s: Stmt)
  : Heap * Stmt :=
  match n with
    | O => (h, s)
    | S m =>
      match step h s with
        | Some (h', s') => run m h' s'
        | None => (h, s)
      end
  end.

Inductive StepStar : Heap -> Stmt ->
                     Heap -> Stmt -> Prop :=
| StepStar_refl : forall h s,
  StepStar h s h s
| StepStar_step : forall h s h' s' h'' s'',
  Step h s h' s' ->
  StepStar h' s' h'' s'' ->
  StepStar h s h'' s''.

Lemma run_StepStar:
  forall n h s h' s',
  run n h s = (h', s') -> StepStar h s h' s'.
Proof.
  intro. induction n.
  { intros. simpl in *.
    inversion H. subst. constructor. }
  { intros. simpl in *. break_if.
    { destruct p. econstructor.
      { apply step_Step. eassumption. }
      { apply IHn. assumption. }
    }
    { inversion H. subst. constructor. }
  }
Qed.

Lemma nostep_run_refl:
  forall h s, step h s = None ->
  forall n, run n h s = (h, s).
Proof.
  intros. destruct n.
  { simpl. reflexivity. }
  { simpl. rewrite H. reflexivity. }
Qed.

Lemma run_combine:
  forall m n h s h' s' h'' s'',
  run m h s = (h', s') ->
  run n h' s' = (h'', s'') ->
  run (m + n) h s = (h'', s'').
Proof.
  intro. induction m.
  { intros. simpl in *.
    inversion H. subst. assumption. }
  { intros. simpl in *. break_if.
    { destruct p. eapply IHm.
      { eauto. }
      { eauto. }
    }
    { inversion H. subst.
      apply nostep_run_refl
        with (n := n) in Heqo.
      congruence.
    }
  }
Qed.

(** Divergance *)

Inductive CanStep : Heap -> Stmt -> Prop :=
| CanStep_step: forall h s h' s',
  Step h s h' s' ->
  CanStep h s.

Lemma notSkip_canStep:
  forall h s, s <> Skip -> CanStep h s.
Proof.
  intros. remember (step h s).
  destruct o as [] eqn:?.
  { symmetry in Heqo. destruct p.
    apply step_Step in Heqo.
    econstructor. eassumption. }
  { symmetry in Heqo.
    apply step_None_Skip in Heqo. subst.
    congruence. }
Qed.

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

Lemma diverges_take1:
  forall h n, exists h', exists s',
  StepN h (While (Int 1) Skip) n h' s'.
Proof.
  intro. intro. induction n.
  { eexists. eexists. econstructor. }
  { firstorder. eexists. eexists.
    eapply StepN_right.
    { eassumption. }
    { (* STUCK! what if x = Skip ? *)
Abort.

Lemma diverges_take2:
  forall h n, exists h', exists s',
  StepN h (While (Int 1) Skip) n h' s' /\
  s' <> Skip.
Proof.
  intro. intro. induction n.
  { eexists. eexists. split.
    { econstructor. }
    { congruence. }
  }
  { firstorder. 
    apply notSkip_canStep with (h := x) in H0.
    inversion H0. subst.
    exists h'. exists s'. split.
    { eapply StepN_right.
      { eassumption. }
      { eassumption. }
    }
    { (* STUCK! what if s' is Skip? *)
Abort.

Lemma diverges_take3:
  forall h n,
  StepN h (While (Int 1) Skip) n
        h (While (Int 1) Skip).
Proof.
  intro. intro. induction n.
  { econstructor; eauto. }
  { econstructor; eauto.
    { (* OOPS! simply false! *)
Abort.
  
Definition w1 := While (Int 1) Skip.
Definition w2 := Seq Skip w1.

Lemma diverges_take4:
  forall h n, exists s,
  StepN h (While (Int 1) Skip) n h s /\
  (s = w1 \/ s = w2).
Proof.
  intro. intro. induction n.
  { eexists. split.
    { econstructor. }
    { auto. }
  }
  { firstorder.
    { subst. exists w2. split.
      { eapply StepN_right.
        { eassumption. }
        { unfold w1, w2. econstructor.
          apply Eval_eval'. simpl. omega. }
      }
      { auto. }
    }
    { subst. exists w1. split.
      { eapply StepN_right.
        { eassumption. }
        { unfold w1, w2. econstructor. }
      }
      { auto. }
    }
  }
Qed.

(** Denotation *)

Fixpoint expr_denote (e: Expr) : Heap -> Z :=
  match e with
    | Int z => fun _ => z
    | Var x => fun h => lkup x h
    | Add e1 e2 =>
      let d1 := expr_denote e1 in
      let d2 := expr_denote e2 in
      fun h => Z.add (d1 h) (d2 h)
    | Mul e1 e2 =>
      let d1 := expr_denote e1 in
      let d2 := expr_denote e2 in
      fun h => Z.mul (d1 h) (d2 h)
  end.

Lemma expr_denote_Expr:
  forall h e c,
  (expr_denote e) h = c ->
  Eval h e c.
Proof.
  intro. intro. induction e.
  { intros. subst. simpl. constructor. }
  { intros. subst. simpl. constructor. }
  { intros. subst. simpl. econstructor.
    { auto. }
    { auto. }
    { reflexivity. }
  }
  { intros. subst. simpl. econstructor.
    { auto. }
    { auto. }
    { reflexivity. }
  }
Qed.

(** Nonneg *)

SearchAbout Z.le.

Inductive NonegHeap : Heap -> Prop :=
| NNH_nil :
  NonegHeap nil
| NNH_cons : forall k v h,
  (0 <= v)%Z ->
  NonegHeap h ->
  NonegHeap ((k, v) :: h).

Definition zleb (z1 z2: Z) : bool :=
  if Z_le_dec z1 z2 then true else false.

Fixpoint noneg_heap (h: Heap) : bool :=
  match h with
    | nil => true
    | (k, v) :: h' =>
      andb (zleb 0%Z v) (noneg_heap h')
  end.

Inductive NonegExpr : Expr -> Prop :=
| NNE_Int : forall i,
  (0 <= i)%Z ->
  NonegExpr (Int i)
| NNE_Var : forall v,
  NonegExpr (Var v)
| NNE_Add : forall e1 e2,
  NonegExpr e1 ->
  NonegExpr e2 ->
  NonegExpr (Add e1 e2)
| NNE_Mul : forall e1 e2,
  NonegExpr e1 ->
  NonegExpr e2 ->
  NonegExpr (Mul e1 e2).

Fixpoint noneg_expr (e: Expr) : bool :=
  match e with
    | Int i => zleb 0%Z i
    | Var v => true
    | Add e1 e2 => andb (noneg_expr e1)
                        (noneg_expr e2)
    | Mul e1 e2 => andb (noneg_expr e1)
                        (noneg_expr e2)
  end.

Inductive NonegStmt : Stmt -> Prop :=
| NNS_Skip :
  NonegStmt Skip
| NNS_Assign : forall v e,
  NonegExpr e ->
  NonegStmt (Assign v e)
| NNS_Seq : forall s1 s2,
  NonegStmt s1 ->
  NonegStmt s2 ->
  NonegStmt (Seq s1 s2)
| NNS_Cond : forall e s1 s2,
  NonegStmt s1 ->
  NonegStmt s2 ->
  NonegStmt (Cond e s1 s2)
| NNS_While : forall e s1,
  NonegStmt s1 ->
  NonegStmt (While e s1).

Fixpoint noneg_stmt (s: Stmt) : bool :=
  match s with
    | Skip => true
    | Assign v e => noneg_expr e
    | Seq s1 s2 => andb (noneg_stmt s1)
                        (noneg_stmt s2)
    | Cond e s1 s2 => andb (noneg_stmt s1)
                           (noneg_stmt s2)
    | While e s => noneg_stmt s
  end.

Lemma NNH_ok:
  forall h, NonegHeap h ->
  forall v, (0 <= lkup v h)%Z.
Proof.
  intros. induction H.
  { simpl. omega. }
  { simpl. break_if.
    { assumption. }
    { assumption. }
  }
Qed.

Lemma NNE_ok:
  forall h e c,
  NonegHeap h ->
  NonegExpr e ->
  Eval h e c ->
  (0 <= c)%Z.
Proof.
  intro. intro. induction e; intros.
  { inversion H0. subst.
    inversion H1. subst.
    assumption. }
  { inversion H1. subst.
    apply NNH_ok with (v := v) in H.
    assumption. }
  { inversion H0. subst.
    inversion H1. subst.
    firstorder. }
  { inversion H0. subst.
    inversion H1. subst.
    firstorder. }
Qed.

Lemma NNS_ok:
  forall h s h' s',
  NonegHeap h ->
  NonegStmt s ->
  Step h s h' s' ->
  NonegHeap h' /\ NonegStmt s'.
Proof.
  intros. induction H1.
  { split.
    { inversion H0. subst.
      eapply NNE_ok in H3; eauto.
      constructor; auto. }
    { constructor. }
  }
  (* ... *)
Abort.

      