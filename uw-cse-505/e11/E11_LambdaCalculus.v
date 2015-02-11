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

(**
Big Step:
<<
       
  ---------------------
    \x. e ==> \x. e

    e1 ==> \x.e1'   e1'[e2/x] ==> v      
  ------------------------------------
            e1 e2 ==> v
>>
*)

Inductive BStep : Expr -> Expr -> Prop :=
| BSval : forall x e,
  BStep (\x, e) (\x, e)
| BSsubst : forall e1 e2 x e1' e2' v,
  BStep e1 (\x, e1') ->
  Subst e1' e2 x e2' ->
  BStep e2' v ->
  BStep (e1 @ e2) v.

Notation "e1 ==> e2" := (BStep e1 e2) (at level 51).

Lemma bstep_test_1:
  (\"x", V"x") @ (\"y", V"y") ==> (\"y", V"y").
Proof.
  econstructor.
  { left. }
  { constructor. }
  { left. }
Qed.

Lemma bstep_test_2:
  forall e,
  ~ (V"x" ==> e).
Proof.
  intro. intro. inversion H.
Qed.

Lemma bstep_lam_inv:
  forall x1 e1 x2 e2,
  \x1, e1 ==> \x2, e2 ->
  x1 = x2 /\ e1 = e2.
Proof.
  intros. inversion H. auto.
Qed.

Lemma bstep_test_3:
  forall e1,
  e1 = (\"x", V"x" @ V"x") @ (\"x", V"x" @ V"x") ->
  forall e2,
  ~ (e1 ==> e2).
Proof.
  intros. intro. induction H0.
  { discriminate. }
  { inversion H. subst. inversion H0_. subst. inversion H0. subst. inversion H3.
    { subst. inversion H7.
      { subst. auto. }
      { auto. }
    }
    { auto. }
  }
Qed.

Lemma bstep_det:
  forall e e1,
  e ==> e1 ->
  forall e2,
  e ==> e2 ->
  e1 = e2.
Proof.
  intro. intro. intro. induction H.
  { intros. inversion H. reflexivity. }
  { intros. inversion H2. subst. apply IHBStep1 in H5. inversion H5. subst. replace e2'0 with e2' in *.
    { auto. }
    { eapply Subst_det.
      { eassumption. }
      { assumption. }
    }
  }
Qed.

Inductive SSstar : Expr -> Expr -> Prop :=
| SSrefl : forall e,
  SSstar e e
| SSstep : forall e e' e'',
  SStep e e' ->
  SSstar e' e'' ->
  SSstar e e''.

Notation "e1 -->* e2" := (SSstar e1 e2) (at level 51).

Lemma SStar_app:
  forall e1 e2 e3,
  e1 -->* e2 ->
  e2 -->* e3 ->
  e1 -->* e3.
Proof.
  intros. induction H.
  { assumption. }
  { econstructor.
    { eassumption. }
    { auto. }
  }
Qed.

Lemma BStep_SSstar:
  forall e1 e2,
  e1 ==> e2 ->
  e1 -->* e2.
(*
intros. induction H.
  { left. }
  { destruct e1.
    { inversion H. }
    { eapply SStar_app in IHBStep1.
      { admit. }
      { admit. } }
    { admit. } }
*)
(*
intros. induction H.
  { left. }
  { destruct e1.
    { inversion H. }
    { admit. }
    { admit. } }
*)
Proof.

  
