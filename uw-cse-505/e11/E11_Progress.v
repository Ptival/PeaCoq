Require Import List.
Require Import String.
Require Import ZArith.
Open Scope string_scope.

Definition var := string.

Inductive Expr : Set :=
| Bool : bool -> Expr
| Int : Z -> Expr
| Var : var -> Expr
| App : Expr -> Expr -> Expr
| Lam : var -> Expr -> Expr.

Notation "'B' b" := (Bool b) (at level 48).
Notation "'I' i" := (Int i) (at level 48).
Notation "'V' x" := (Var x) (at level 48).
Notation "e1 @ e2" := (App e1 e2) (at level 49).
Notation "\ x , t" := (Lam x t) (at level 50).

Check (\"x", \"y", V"x").
Check (\"x", \"y", I 5).
Check ((\"x", V"x" @ V"x") @ (\"x", V"x" @ V"x")).

(* e1[e2/x] = e3 *)
Inductive Subst : Expr -> Expr -> var ->
                  Expr -> Prop :=
| SubstBool : forall b e x,
  Subst (B b) e x (B b)
| SubstInt : forall i e x,
  Subst (I i) e x (I i)
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

Inductive SSstar : Expr -> Expr -> Prop :=
| SSrefl : forall e,
  SSstar e e
| SSstep : forall e e' e'',
  SStep e e' ->
  SSstar e' e'' ->
  SSstar e e''.

Notation "e1 -->* e2" := (SSstar e1 e2) (at level 51).

(* ----------- *)

Inductive Value : Expr -> Prop :=
| VBool : forall b,
  Value (B b)
| VInt : forall i,
  Value (I i)
| VLam : forall x e,
  Value (\x, e).

Inductive Typ :=
| TBool : Typ
| TInt : Typ
| TFun : Typ -> Typ -> Typ.

Notation "t1 ~> t2" := (TFun t1 t2) (at level 52).

Definition Env := var -> option Typ.

Definition Empty : Env := fun _ => None.

Definition extend (env: Env) x t :=
  fun y => if string_dec x y then Some t else env y.

Inductive WellTyped : Env -> Expr -> Typ -> Prop :=
| WTBool : forall env b,
  WellTyped env (B b) TBool
| WTInt : forall env i,
  WellTyped env (I i) TInt
| WTVar : forall env x t,
  env x = Some t ->
  WellTyped env (V x) t
| WTLam : forall env x e t1 t2,
  WellTyped (extend env x t1) e t2 ->
  WellTyped env (\x, e) (t1 ~> t2)
| WTApp : forall env e1 e2 t1 t2,
  WellTyped env e1 (t1 ~> t2) ->
  WellTyped env e2 t1 ->
  WellTyped env (e1 @ e2) t2.

Lemma test_WT_1:
  WellTyped Empty
    ((\"x", V"x") @ (\"y", V"y"))
    (TInt ~> TInt).
Proof.
  econstructor.
  { constructor. constructor. reflexivity. }
  { constructor. constructor. reflexivity. }
Qed.

Lemma test_WT_2:
  WellTyped Empty
    ((\"x", V"x") @ (\"y", V"y"))
    (TBool ~> TBool).
Proof.
  econstructor.
  { constructor. constructor. reflexivity. }
  { constructor. constructor. reflexivity. }
Qed.

Lemma canon_bool:
  forall e,
  Value e ->
  WellTyped Empty e TBool ->
  exists b, e = B b.
Proof.
  intros. inversion H.
  { eauto. }
  { subst. inversion H0. }
  { subst. inversion H0. }
Qed.

Lemma canon_int:
  forall e,
  Value e ->
  WellTyped Empty e TInt ->
  exists i, e = I i.
Proof.
Admitted.


Lemma cannon_lam:
  forall e t1 t2,
  Value e ->
  WellTyped Empty e (t1 ~> t2) ->
  exists x, exists e', e = \x, e'.
Proof.
Admitted.

Lemma Subst_exists:
  forall e1 e2 x,
  exists e3, Subst e1 e2 x e3.
Proof.
  intros. induction e1.
  { econstructor. constructor. }
  { econstructor. constructor. }
  { destruct (string_dec v x).
    { subst. econstructor. constructor. }
    { econstructor. constructor. assumption. }
  }
  { firstorder. econstructor. constructor.
    { eassumption. }
    { eassumption. }
  }
  { destruct (string_dec v x).
    { subst. econstructor. constructor. }
    { firstorder. econstructor. constructor.
      { assumption. }
      { eassumption. }
    }
  }
Qed.

Lemma progress:
  forall env e t,
  env = Empty ->
  WellTyped env e t ->
  ((exists e', e --> e') \/ Value e).
Proof.
  intros. induction H0.
  { right. constructor. }
  { right. constructor. }
  { subst. discriminate. }
  { right. constructor. }
  { subst. destruct IHWellTyped1.
    { reflexivity. }
    { destruct H. left. econstructor. left. eassumption. }
    { left. eapply cannon_lam in H.
      { destruct H. destruct H. subst.
        destruct (Subst_exists x0 e2 x).
        econstructor. right. eassumption. }
      { eassumption. }
    }
  }
Qed.