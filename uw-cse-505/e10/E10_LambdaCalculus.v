Require Import List.
Require Import String.
Open Scope string_scope.

Definition var := string.

Inductive Expr : Set :=
| Var : var -> Expr
| App : Expr -> Expr -> Expr
| Lam : var -> Expr -> Expr.

Notation "'V' x" := (Var x) (at level 48).
Notation "e1 @ e2" := (App e1 e2) (at level 49).
Notation "\ x , t" := (Lam x t) (at level 50).

Check (\"x", \"y", V"x").
Check (\"x", \"y", V"y").
Check ((\"x", V"x" @ V"x") @ (\"x", V"x" @ V"x")).

(* e1[e2/x] = e3 *)
Inductive Subst : Expr -> Expr -> var ->
                  Expr -> Prop :=
| SubstVar_same : forall e x,
  Subst (V x) e x e
| SubstVar_diff : forall e x1 x2,
  x1 <> x2 ->
  Subst (V x1) e x2 (V x1)
| SubstApp : forall eA eB e x eA' eB',
  Subst eA e x eA' ->
  Subst eB e x eB' ->
  Subst (eA @ eB) e x (eA' @ eB')
| SubstLam_same : forall eA e x,
  Subst (\x, eA) e x (\x, eA)
| SubstLam_diff : forall eA e x1 x2 eA',
  x1 <> x2 ->
  Subst eA e x2 eA' ->
  Subst (\x1, eA) e x2 (\x1, eA').

Lemma subst_test_1:
  Subst (\"x", V"y") (V"z") "y" (\"x", V"z").
Proof.
  constructor.
  { discriminate. }
  { constructor. }
Qed.

Lemma subst_test_2:
  Subst (\"x", V"x") (V"z") "x"
        (\"x", V"x").
Proof.
  constructor.
Qed.

(**
Small Step:
<<
       e1 --> e1'
  ---------------------
    e1 e2 --> e1' e2

  -----------------------------
    (\x. e1) e2 --> e1[e2/x]
>>
*)

Inductive SStep : Expr -> Expr -> Prop :=
| Scrunch : forall e1 e1' e2,
  SStep e1 e1' ->
  SStep (e1 @ e2) (e1' @ e2)
| Ssubst : forall x e1 e2 e1',
  Subst e1 e2 x e1' ->
  SStep ((\x, e1) @ e2) e1'.

Notation "e1 --> e2" := (SStep e1 e2) (at level 51).

Lemma sstep_test_1:
  (\"x", V"x") @ V"z" --> V"z".
Proof.
  apply Ssubst.
  apply SubstVar_same.
Qed.

Lemma Lam_nostep:
  forall x e1 e2,
  ~ (\x, e1 --> e2).
Proof.
  intros. intro. inversion H.
Qed.

Lemma Subst_det:
  forall e1 e2 x e3 e3',
  Subst e1 e2 x e3 ->
  Subst e1 e2 x e3' ->
  e3 = e3'.
Proof.
  intros. induction H.
  - inversion H0; subst.
    + reflexivity.
    + congruence.
  - inversion H0; subst.
    + congruence.
    + reflexivity.
  - inversion H0; subst.
    (* stuck, IH not strong enough... *)
Abort.

Lemma Subst_det:
  forall e1 e2 x e3,
  Subst e1 e2 x e3 ->
  forall e3',
  Subst e1 e2 x e3' ->
  e3 = e3'.
Proof.
  induction 1; intros.
  { inversion H; subst; auto.
    congruence.
  }
  { inversion H0; subst; auto.
    congruence.
  }
  { inversion H1; subst; auto.
    f_equal; auto.
  }
  { inversion H; subst; auto.
    congruence.
  }
  { inversion H1; subst; auto.
    { congruence. }
    { f_equal; auto. }
  }
Qed.

Lemma SStep_det:
  forall e e1,
  e --> e1 ->
  forall e2,
  e --> e2 ->
  e1 = e2.
Proof.
  intro. intro. intro. induction H.
  { intros. inversion H0.
    { subst. f_equal. auto. }
    { subst. apply Lam_nostep in H. contradiction. }
  }
  { intros. inversion H0.
    { subst. apply Lam_nostep in H4. contradiction. }
    { subst. eapply Subst_det in H5.
      { eassumption. }
      { assumption. }
    }
  }
Qed.
