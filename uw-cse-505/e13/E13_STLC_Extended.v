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
| Cond : Expr -> Expr -> Expr -> Expr
| Prod : Expr -> Expr -> Expr
| ProjL : Expr -> Expr
| ProjR : Expr -> Expr
| SumL : Expr -> Expr
| SumR : Expr -> Expr
| Match : Expr -> var -> Expr -> var -> Expr -> Expr
| Lam : var -> Expr -> Expr.

Notation "'B' b" := (Bool b) (at level 48).
Notation "'I' i" := (Int i) (at level 48).
Notation "'V' x" := (Var x) (at level 48).
Notation "e1 @ e2" := (App e1 e2) (at level 49).
Notation "'WHEN' e1 'THEN' e2 'ELSE' e3" := (Cond e1 e2 e3) (at level 49).
Notation "<( e1 , e2 )>" := (Prod e1 e2) (at level 49).
Notation "'PL' e" := (ProjL e) (at level 49).
Notation "'PR' e" := (ProjR e) (at level 49).
Notation "'SL' e" := (SumL e) (at level 49).
Notation "'SR' e" := (SumR e) (at level 49).
Notation "'MATCH' e1 'WITH' 'L' v2 ===> e2 | 'R' v3 ===> e3" :=
  (Match e1 v2 e2 v3 e3) (at level 49).
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
| SubstCond : forall e1 e2 e3 e x e1' e2' e3',
  Subst e1 e x e1' ->
  Subst e2 e x e2' ->
  Subst e3 e x e3' ->
  Subst (WHEN e1 THEN e2 ELSE e3) e x
        (WHEN e1' THEN e2' ELSE e3')
| SubstProd: forall e1 e2 e x e1' e2',
  Subst e1 e x e1' ->
  Subst e2 e x e2' ->
  Subst (<(e1, e2)>) e x (<(e1', e2')>)
| SubstProjL: forall e1 e x e1',
  Subst e1 e x e1' ->
  Subst (PL e1) e x (PL e1')
| SubstProjR: forall e1 e x e1',
  Subst e1 e x e1' ->
  Subst (PR e1) e x (PL e1')
| SubstSumL: forall e1 e x e1',
  Subst e1 e x e1' ->
  Subst (SL e1) e x (SL e1')
| SubstSumR: forall e1 e x e1',
  Subst e1 e x e1' ->
  Subst (SR e1) e x (SR e1')
| SubstMatch_ls_rs:
  forall em el er e x em',
  Subst em e x em' ->
  Subst (MATCH em WITH L x ===> el | R x ===> er) e x
        (MATCH em' WITH L x ===> el | R x ===> er)
| SubstMatch_ls_rd:
  forall em el vr er e x em' er',
  x <> vr ->
  Subst em e x em' ->
  Subst er e x er' ->
  Subst (MATCH em WITH L x ===> el | R vr ===> er) e x
        (MATCH em' WITH L x ===> el | R vr ===> er')
| SubstMatch_ld_rs:
  forall em vl el er e x em' el',
  x <> vl ->
  Subst em e x em' ->
  Subst el e x el' ->
  Subst (MATCH em WITH L vl ===> el | R x ===> er) e x
        (MATCH em' WITH L vl ===> el' | R x ===> er)
| SubstMatch_ld_rd:
  forall em vl el vr er e x em' el' er',
  x <> vl ->
  x <> vr ->
  Subst em e x em' ->
  Subst el e x el' ->
  Subst er e x er' ->
  Subst (MATCH em WITH L vl ===> el | R vr ===> er) e x
        (MATCH em' WITH L vl ===> el' | R vr ===> er')
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
  SStep ((\x, e1) @ e2) e1'
| SCond_crunch : forall e1 e1' e2 e3,
  SStep e1 e1' ->
  SStep (WHEN e1 THEN e2 ELSE e3)
        (WHEN e1' THEN e2 ELSE e3)
| SCond_true : forall e2 e3,
  SStep (WHEN (B true) THEN e2 ELSE e3) e2
| SCond_false : forall e2 e3,
  SStep (WHEN (B false) THEN e2 ELSE e3) e3
| SProjL_crunch : forall e e',
  SStep e e' ->
  SStep (PL e) (PL e')
| SProjL_proj : forall e1 e2,
  SStep (PL <(e1, e2)>) e1
| SProjR_crunch : forall e e',
  SStep e e' ->
  SStep (PR e) (PR e')
| SProjR_proj : forall e1 e2,
  SStep (PR <(e1, e2)>) e2
| SMatch_crunch : forall e e' vl el vr er,
  SStep e e' ->
  SStep (MATCH e WITH L vl ===> el | R vr ===> er)
        (MATCH e' WITH L vl ===> el | R vr ===> er)
| SMatch_l : forall e vl el vr er el',
  Subst el e vl el' ->
  SStep (MATCH SL e WITH L vl ===> el | R vr ===> er) el'
| SMatch_r : forall e vl el vr er er',
  Subst er e vr er' ->
  SStep (MATCH SR e WITH L vl ===> el | R vr ===> er) er'.


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
  Value (\x, e)
| VProd : forall e1 e2,
  Value (<(e1, e2)>)
| VSumL : forall e,
  Value (SL e)
| VSumR : forall e,
  Value (SR e).

Inductive Typ :=
| TBool : Typ
| TInt : Typ
| TFun : Typ -> Typ -> Typ
| TProd : Typ -> Typ -> Typ
| TSum : Typ -> Typ -> Typ.

Notation "t1 ~~> t2" := (TFun t1 t2) (at level 52, right associativity).
Notation "t1 *** t2" := (TProd t1 t2) (at level 52).
Notation "t1 +++ t2" := (TSum t1 t2) (at level 52).

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
  WellTyped env (\x, e) (t1 ~~> t2)
| WTApp : forall env e1 e2 t1 t2,
  WellTyped env e1 (t1 ~~> t2) ->
  WellTyped env e2 t1 ->
  WellTyped env (e1 @ e2) t2
| WTCond : forall env e e1 e2 t,
  WellTyped env e TBool ->
  WellTyped env e1 t ->
  WellTyped env e2 t ->
  WellTyped env (WHEN e THEN e1 ELSE e2) t
| WTProd : forall env e1 t1 e2 t2,
  WellTyped env e1 t1 ->
  WellTyped env e2 t2 ->
  WellTyped env (<(e1, e2)>) (t1 *** t2)
| WTProjL : forall env e t1 t2,
  WellTyped env e (t1 *** t2) ->
  WellTyped env (PL e) t1
| WTProjR : forall env e t1 t2,
  WellTyped env e (t1 *** t2) ->
  WellTyped env (PR e) t2
| WTSumL : forall env e t1 t2,
  WellTyped env e t1 ->
  WellTyped env (SL e) (t1 +++ t2)
| WTSumR : forall env e t1 t2,
  WellTyped env e t2 ->
  WellTyped env (SR e) (t1 +++ t2)
| WTMatch : forall env e vl el vr er t1 t2 t3,
  WellTyped env e (t1 +++ t2) ->
  WellTyped (extend env vl t1) el t3 ->
  WellTyped (extend env vr t2) er t3 ->
  WellTyped env (MATCH e WITH L vl ===> el
                            | R vr ===> er) t3.

Lemma test_WT_1:
  WellTyped Empty
    ((\"x", V"x") @ (\"y", V"y"))
    (TInt ~~> TInt).
Proof.
  econstructor.
  { constructor. constructor. reflexivity. }
  { constructor. constructor. reflexivity. }
Qed.

Lemma test_WT_2:
  WellTyped Empty
    ((\"x", V"x") @ (\"y", V"y"))
    (TBool ~~> TBool).
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
  intros.
  inversion H; subst;
    inversion H0; subst.
  eauto.
Qed.

Lemma canon_int:
  forall e,
  Value e ->
  WellTyped Empty e TInt ->
  exists i, e = I i.
Proof.
  intros.
  inversion H; subst;
    inversion H0; subst.
  eauto.
Qed.

Lemma cannon_lam:
  forall e t1 t2,
  Value e ->
  WellTyped Empty e (t1 ~~> t2) ->
  exists x, exists e', e = \x, e'.
Proof.
  intros.
  inversion H; subst;
    inversion H0; subst.
  eauto.
Qed.

Lemma canon_prod:
  forall e t1 t2,
  Value e ->
  WellTyped Empty e (t1 *** t2) ->
  exists e1, exists e2, e = <(e1, e2)>.
Proof.
  intros.
  inversion H; subst;
    inversion H0; subst.
  eauto.
Qed.

Lemma canon_sum:
  forall e t1 t2,
  Value e ->
  WellTyped Empty e (t1 +++ t2) ->
  exists e', e = SL e' \/ e = SR e'.
Proof.
  intros.
  inversion H; subst;
    inversion H0; subst.
  eauto. eauto.
Qed.

Lemma Subst_exists:
  forall e1 e2 x,
  exists e3, Subst e1 e2 x e3.
Proof.
  intros. induction e1; firstorder;
    try (econstructor; constructor; eauto; fail).
  - destruct (string_dec v x); subst;
    econstructor; constructor; eauto.
  - destruct (string_dec v x);
    destruct (string_dec v0 x); subst;
    econstructor; constructor; eauto.
  - destruct (string_dec v x); subst;
    econstructor; constructor; eauto.
Qed.

Lemma progress:
  forall e t,
  WellTyped Empty e t ->
  ((exists e', e --> e') \/ Value e).
Proof.
  intros. remember Empty.
  induction H; subst;
    try (right; constructor; auto; fail);
    left.
  - discriminate.
  - destruct IHWellTyped1; auto.
    + destruct H1. econstructor.
      constructor; eauto.
    + apply cannon_lam in H; auto.
      destruct H. destruct H. subst.
      destruct (Subst_exists x0 e2 x).
      econstructor. eapply Ssubst; eauto.
  - destruct IHWellTyped1; auto.
    + destruct H2. econstructor.
      constructor; eauto.
    + apply canon_bool in H; auto.
      destruct H; subst. destruct x.
      * econstructor. eapply SCond_true; eauto.
      * econstructor. eapply SCond_false; eauto.
  - destruct IHWellTyped; auto.
    + destruct H0. econstructor.
      constructor; eauto.
    + apply canon_prod in H; auto.
      destruct H. destruct H. subst.
      econstructor; eapply SProjL_proj; eauto.
  - destruct IHWellTyped; auto.
    + destruct H0. econstructor.
      constructor; eauto.
    + apply canon_prod in H; auto.
      destruct H. destruct H. subst.
      econstructor; eapply SProjR_proj; eauto.
  - destruct IHWellTyped1; auto.
    + destruct H2. econstructor.
      constructor; eauto.
    + apply canon_sum in H; auto.
      destruct H. destruct H; subst.
      * destruct (Subst_exists el x vl); auto.
        econstructor. eapply SMatch_l; eauto.
      * destruct (Subst_exists er x vr); auto.
        econstructor. eapply SMatch_r; eauto.
Qed.

Lemma lkup_extend_same:
  forall env x t,
  (extend env x t) x = Some t.
Proof.
  unfold extend; intros.
  destruct (string_dec x x); auto.
  congruence.
Qed.

Lemma lkup_extend_diff:
  forall env x1 x2 t,
  x1 <> x2 ->
  (extend env x1 t) x2 = env x2.
Proof.
  unfold extend; intros.
  destruct (string_dec x1 x2); auto.
  congruence.
Qed.  

Definition env_equiv (e1 e2: Env) :=
  forall x, e1 x = e2 x.

Lemma env_equiv_extend:
  forall env1 env2,
  env_equiv env1 env2 ->
  forall x t,
  env_equiv (extend env1 x t)
            (extend env2 x t).
Proof.
  unfold env_equiv, extend; intros.
  destruct (string_dec x x0); auto.
Qed.

Lemma env_equiv_overwrite:
  forall env x t0 t1,
  env_equiv (extend env x t1)
            (extend (extend env x t0) x t1).
Proof.
  unfold env_equiv, extend; intros.
  destruct (string_dec x x0); auto.
Qed.

Lemma env_equiv_extend_diff:
  forall env x1 t1 x2 t2,
  x1 <> x2 ->
  env_equiv (extend (extend env x1 t1) x2 t2)
            (extend (extend env x2 t2) x1 t1).
Proof.
  unfold env_equiv, extend; intros.
  destruct (string_dec x2 x); subst; auto.
  destruct (string_dec x1 x); subst; auto.
  congruence.
Qed.

Lemma env_equiv_symmetry:
  forall env1 env2,
  env_equiv env1 env2 ->
  env_equiv env2 env1.
Proof.
  congruence.
Qed.

Lemma env_equiv_wt:
  forall env1 e te,
  WellTyped env1 e te ->
  forall env2,
  env_equiv env2 env1 ->
  WellTyped env2 e te.
Proof.
  induction 1; intros;
    try (econstructor; eauto; fail).
  - constructor; auto. congruence.
  - constructor; auto.
    apply IHWellTyped.
    apply env_equiv_extend; auto.
  - econstructor; eauto.
    + apply IHWellTyped2.
      apply env_equiv_extend; auto.
    + apply IHWellTyped3.
      apply env_equiv_extend; auto.
Qed.

Inductive Free : Expr -> var -> Prop :=
| FVar : forall x,
  Free (Var x) x
| FAppL : forall e1 e2 x,
  Free e1 x ->  Free (App e1 e2) x
| FAppR : forall e1 e2 x,
  Free e2 x ->  Free (App e1 e2) x
| FLam : forall x1 e1 x,
  Free e1 x ->
  x <> x1 ->
  Free (Lam x1 e1) x
| FCond_cond : forall e1 e2 e3 x,
  Free e1 x ->
  Free (WHEN e1 THEN e2 ELSE e3) x
| FCond_then : forall e1 e2 e3 x,
  Free e2 x ->
  Free (WHEN e1 THEN e2 ELSE e3) x
| FCond_else : forall e1 e2 e3 x,
  Free e3 x ->
  Free (WHEN e1 THEN e2 ELSE e3) x
| FProdl : forall e1 e2 x,
  Free e1 x ->
  Free (<(e1, e2)>) x
| FProdr : forall e1 e2 x,
  Free e2 x ->
  Free (<(e1, e2)>) x
| FProjL : forall e x,
  Free e x ->
  Free (PL e) x
| FProjR : forall e x,
  Free e x ->
  Free (PR e) x
| FSumL : forall e x,
  Free e x ->
  Free (SL e) x
| FSumR : forall e x,
  Free e x ->
  Free (SR e) x
| FMatchM : forall e vl el vr er x,
  Free e x ->
  Free (MATCH e WITH L vl ===> el | R vr ===> er) x
| FMatchL : forall e vl el vr er x,
  x <> vl ->
  Free el x ->
  Free (MATCH e WITH L vl ===> el | R vr ===> er) x
| FMatchR : forall e vl el vr er x,
  x <> vr ->
  Free er x ->
  Free (MATCH e WITH L vl ===> el | R vr ===> er) x.

Lemma not_free_app_inv:
  forall e1 e2 x,
  ~ Free (e1 @ e2) x ->
  ~ Free e1 x /\ ~ Free e2 x.
Proof.
  intros. split.
  - intro. apply H.
    apply FAppL; auto.
  - intro. apply H.
    apply FAppR; auto.
Qed.

Lemma not_free_cond_inv:
  forall e1 e2 e3 x,
  ~ Free (WHEN e1 THEN e2 ELSE e3) x ->
  (~ Free e1 x) /\ (~ Free e2 x) /\ (~ Free e3 x).
Proof.
  unfold not; firstorder.
  - apply H; apply FCond_cond; auto.
  - apply H; apply FCond_then; auto.
  - apply H; apply FCond_else; auto.
Qed.

Lemma not_free_prod_inv:
  forall e1 e2 x,
  ~ Free (<(e1, e2)>) x ->
  ~ Free e1 x /\ ~ Free e2 x.
Proof.
  unfold not; firstorder.
  - apply H; apply FProdl; auto.
  - apply H; apply FProdr; auto.
Qed.

Lemma not_free_pl_inv:
  forall e x,
  ~ Free (PL e) x ->
  ~ Free e x.
Proof.
  unfold not; firstorder.
  apply H. apply FProjL; auto.
Qed.

Lemma not_free_pr_inv:
  forall e x,
  ~ Free (PR e) x ->
  ~ Free e x.
Proof.
  unfold not; firstorder.
  apply H. apply FProjR; auto.
Qed.

Lemma not_free_sl_inv:
  forall e x,
  ~ Free (SL e) x ->
  ~ Free e x.
Proof.
  unfold not; firstorder.
  apply H. apply FSumL; auto.
Qed.

Lemma not_free_sr_inv:
  forall e x,
  ~ Free (SR e) x ->
  ~ Free e x.
Proof.
  unfold not; firstorder.
  apply H. apply FSumR; auto.
Qed.

Lemma not_free_match_inv:
  forall e1 v2 e2 v3 e3 x,
  ~ Free (MATCH e1 WITH L v2 ===> e2 | R v3 ===> e3) x ->
  (~ Free e1 x) /\
  (v2 <> x -> ~ Free e2 x) /\
  (v3 <> x -> ~ Free e3 x).
Proof.
  unfold not; firstorder.
  - apply H; apply FMatchM; auto.
  - apply H; apply FMatchL; auto.
  - apply H; apply FMatchR; auto.
Qed.

(*
Lemma strengthen:
  forall e x,
  ~ Free e x ->
  forall env tx te,
  WellTyped (extend env x tx) e te ->
  WellTyped env e te.
Proof.
  induction e; intros;
    inversion H0; subst;
    try (econstructor; eauto; fail).
  - constructor. unfold extend in H3.
    destruct (string_dec x v); subst; auto.
    destruct H. constructor.
  - apply not_free_app_inv in H. destruct H.
    econstructor; eauto.
  - apply not_free_cond_inv in H.
    destruct H. destruct H1.
    econstructor; eauto.
  - apply not_free_prod_inv in H. destruct H.
    econstructor; eauto.
  - apply not_free_pl_inv in H.
    econstructor; eauto.
  - apply not_free_pr_inv in H.
    econstructor; eauto.
  - apply not_free_sl_inv in H.
    econstructor; eauto.
  - apply not_free_sr_inv in H.
    econstructor; eauto.
  - apply not_free_match_inv in H.
    destruct H. destruct H1.
    econstructor; eauto.
    +


XXX HERE XXX 

    destruct (string_dec v x); subst.
      + econstructor; eauto.
        * eapply env_equiv_wt; eauto.
          apply env_equiv_overwrite.
        * 
      *


    econstructor; eauto.
      * apply H1 in n. econstructor; eauto.
      


  induction e; intros;
    inversion H0; subst.
  - constructor.
  - constructor.
  - constructor.
    unfold extend in H3.
    destruct (string_dec x v); subst.
    + destruct H. constructor.
    + assumption. 
  - apply not_free_app_inv in H. destruct H.
    econstructor; eauto.
  - constructor.
    destruct (string_dec v x); subst.
    + eapply env_equiv_wt; eauto.
      apply env_equiv_overwrite.
    + eapply IHe; eauto.
      * intro. apply H.
        constructor; auto.
        eassumption.
      * eapply env_equiv_wt; eauto.
        apply env_equiv_extend_diff; auto.
Qed.

Lemma weaken:
  forall e x,
  ~ Free e x ->
  forall env tx te,
  WellTyped env e te ->
  WellTyped (extend env x tx) e te.
Proof.
  induction e; intros;
    inversion H0; subst.
  - constructor.
  - constructor.
  - constructor.
    unfold extend.
    destruct (string_dec x v); subst.
    + destruct H. constructor.
    + assumption. 
  - apply not_free_app_inv in H. destruct H.
    econstructor; eauto.
  - constructor.
    destruct (string_dec v x); subst.
    + eapply env_equiv_wt; eauto.
      apply env_equiv_symmetry.
      apply env_equiv_overwrite.
    + eapply IHe in H5; eauto.
      * eapply env_equiv_wt; eauto.
        apply env_equiv_extend_diff; auto.
      * intro. apply H.
        constructor; auto.
Qed.

Lemma subst_preserve_wt:
  forall e1 e2 x e1',
  Subst e1 e2 x e1' ->
  forall env te2 te1,
    WellTyped (extend env x te2) e1 te1 ->
    WellTyped env e2 te2 ->
    (forall v, ~ Free e2 v) ->
    WellTyped env e1' te1.
Proof.
  induction 1; intros.
  - inversion H; subst.
    constructor; auto.
  - inversion H; subst.
    constructor; auto.
  - inversion H; subst.
    rewrite lkup_extend_same in H4.
    inversion H4; subst. auto.
  - inversion H0; subst.
    rewrite lkup_extend_diff in H5; auto.
    constructor; auto.
  - inversion H1; subst.
    econstructor; eauto.
  - inversion H; subst.
    constructor; auto.
    eapply env_equiv_wt; eauto.
    apply env_equiv_overwrite.
  - inversion H1; subst.
    constructor; auto.
    eapply IHSubst; eauto.
    + eapply env_equiv_wt; eauto.
      eapply env_equiv_extend_diff; auto.
    + eapply weaken; eauto.
Qed.

Definition closed e :=
  forall v, ~ Free e v.

Lemma closed_app_inv:
  forall e1 e2,
  closed (e1 @ e2) ->
  closed e1 /\ closed e2.
Proof.
  unfold closed; split; intros; intro.
  - edestruct H; eauto.
    apply FAppL; eauto.
  - edestruct H; eauto.
    apply FAppR; eauto.
Qed.

Lemma closed_app_intro:
  forall e1 e2,
  closed e1 ->
  closed e2 ->
  closed (e1 @ e2).
Proof.
  unfold closed; intros; intro.
  inversion H1; subst.
  - firstorder.
  - firstorder.
Qed.

Lemma free_in_env:
  forall env e t,
  WellTyped env e t ->
  forall v, Free e v ->
  env v <> None.
Proof.
  induction 1; intros; intro.
  - inversion H.
  - inversion H.
  - inversion H0. subst.
    rewrite H in H1. discriminate.
  - inversion H0. subst.
    destruct IHWellTyped with (v := v); auto.
    rewrite lkup_extend_diff; auto.
  - inversion H1; subst.
    + destruct IHWellTyped1 with (v := v); auto.
    + destruct IHWellTyped2 with (v := v); auto.
Qed.

Lemma empty_closed:
  forall e t,
  WellTyped Empty e t ->
  closed e.
Proof.
  unfold closed; intros; intro.
  apply free_in_env with (v := v) in H; auto.
Qed.

Lemma preserve:
  forall env e t,
  WellTyped env e t ->
  closed e ->
  forall e',
  e --> e' ->
  WellTyped env e' t.
Proof.
  induction 1; intros.
  - inversion H0.
  - inversion H0.
  - inversion H1.
  - inversion H1.
  - apply closed_app_inv in H1; destruct H1.
    inversion H2; subst.
    + econstructor; eauto.
    + inversion H; subst.
      eapply subst_preserve_wt; eauto.
Qed.

Lemma not_free_subst:
  forall e1 e2 x e1',
  Subst e1 e2 x e1' ->
  forall v,
  ~ Free (\x, e1) v ->
  ~ Free e2 v ->
  ~ Free e1' v.
Proof.
  induction 1; intros; intro.
  - inversion H1.
  - inversion H1.
  - contradiction.
  - inversion H2; subst.
    apply H0. constructor; auto.
  - inversion H3; subst.
    + edestruct IHSubst1; eauto.
      intros; intro. inversion H4; subst.
      apply H1. constructor; auto.
      apply FAppL; auto.
    + edestruct IHSubst2; eauto.
      intros; intro. inversion H4; subst.
      apply H1. constructor; auto.
      apply FAppR; auto.
  - inversion H1; subst.
    apply H. constructor; auto.
  - inversion H3; subst.
    edestruct IHSubst; eauto.
    intros; intro. inversion H4; subst.
    apply H1.
    constructor; auto.
    constructor; auto.
Qed.

Lemma closed_subst:
  forall e1 e2 x e1',
  Subst e1 e2 x e1' ->
  closed (\x, e1) ->
  closed e2 ->
  closed e1'.
Proof.
  unfold closed; intros; intro.
  edestruct not_free_subst; eauto.
Qed.

Lemma closed_step:
  forall e e',
  e --> e' ->
  closed e ->
  closed e'.
Proof.
  induction 1; intros.
  - apply closed_app_inv in H0; destruct H0.
    apply closed_app_intro; auto.
  - apply closed_app_inv in H0; destruct H0.
    eapply closed_subst; eauto.
Qed.

Lemma preserve_star:
  forall e e',
  e -->* e' ->
  closed e ->
  forall env t,
  WellTyped env e t ->
  WellTyped env e' t.
Proof.
  induction 1; intros.
  - auto.
  - apply IHSSstar.
    + eapply closed_step; eauto.
    + eapply preserve; eauto.
Qed.

Lemma soundness:
  forall e t,
  WellTyped Empty e t ->
  forall e',
  e -->* e' ->
  (exists e'', e' --> e'') \/ Value e'.
Proof.
  intros. induction H0.
  - eapply progress. eassumption.
  - destruct IHSSstar; auto.
    + eapply preserve; eauto.
      eapply empty_closed; eauto.
Qed.










      { eassumption. }
    }
  }
Qed.

Lemma lkup_extend_same:
  forall env x t,
  (extend env x t) x = Some t.
Proof.
  unfold extend; intros.
  destruct (string_dec x x); auto.
  congruence.
Qed.

Lemma lkup_extend_diff:
  forall env x1 x2 t,
  x1 <> x2 ->
  (extend env x1 t) x2 = env x2.
Proof.
  unfold extend; intros.
  destruct (string_dec x1 x2); auto.
  congruence.
Qed.  

Definition env_equiv (e1 e2: Env) :=
  forall x, e1 x = e2 x.

Lemma env_equiv_extend:
  forall env1 env2,
  env_equiv env1 env2 ->
  forall x t,
  env_equiv (extend env1 x t)
            (extend env2 x t).
Proof.
  unfold env_equiv, extend; intros.
  destruct (string_dec x x0); auto.
Qed.

Lemma env_equiv_overwrite:
  forall env x t0 t1,
  env_equiv (extend env x t1)
            (extend (extend env x t0) x t1).
Proof.
  unfold env_equiv, extend; intros.
  destruct (string_dec x x0); auto.
Qed.

Lemma env_equiv_extend_diff:
  forall env x1 t1 x2 t2,
  x1 <> x2 ->
  env_equiv (extend (extend env x1 t1) x2 t2)
            (extend (extend env x2 t2) x1 t1).
Proof.
  unfold env_equiv, extend; intros.
  destruct (string_dec x2 x); subst; auto.
  destruct (string_dec x1 x); subst; auto.
  congruence.
Qed.

Lemma env_equiv_symmetry:
  forall env1 env2,
  env_equiv env1 env2 ->
  env_equiv env2 env1.
Proof.
  congruence.
Qed.

Lemma env_equiv_wt:
  forall env1 e te,
  WellTyped env1 e te ->
  forall env2,
  env_equiv env2 env1 ->
  WellTyped env2 e te.
Proof.
  induction 1; intros env2 Hequiv.
  - constructor; auto.
  - constructor; auto.
  - constructor; auto.
    congruence.
  - constructor; auto.
    apply IHWellTyped.
    apply env_equiv_extend; auto.
  - econstructor; eauto.
Qed.

Inductive Free : Expr -> var -> Prop :=
| FVar : forall x,
  Free (Var x) x
| FAppL : forall e1 e2 x,
  Free e1 x ->  Free (App e1 e2) x
| FAppR : forall e1 e2 x,
  Free e2 x ->  Free (App e1 e2) x
| FLam : forall x1 e1 x,
  Free e1 x ->
  x <> x1 ->
  Free (Lam x1 e1) x.

Lemma not_free_app_inv:
  forall e1 e2 x,
  ~ Free (e1 @ e2) x ->
  ~ Free e1 x /\ ~ Free e2 x.
Proof.
  intros. split.
  - intro. apply H.
    apply FAppL; auto.
  - intro. apply H.
    apply FAppR; auto.
Qed.

Lemma strengthen:
  forall e x,
  ~ Free e x ->
  forall env tx te,
  WellTyped (extend env x tx) e te ->
  WellTyped env e te.
Proof.
  induction e; intros;
    inversion H0; subst.
  - constructor.
  - constructor.
  - constructor.
    unfold extend in H3.
    destruct (string_dec x v); subst.
    + destruct H. constructor.
    + assumption. 
  - apply not_free_app_inv in H. destruct H.
    econstructor; eauto.
  - constructor.
    destruct (string_dec v x); subst.
    + eapply env_equiv_wt; eauto.
      apply env_equiv_overwrite.
    + eapply IHe; eauto.
      * intro. apply H.
        constructor; auto.
        eassumption.
      * eapply env_equiv_wt; eauto.
        apply env_equiv_extend_diff; auto.
Qed.

Lemma weaken:
  forall e x,
  ~ Free e x ->
  forall env tx te,
  WellTyped env e te ->
  WellTyped (extend env x tx) e te.
Proof.
  induction e; intros;
    inversion H0; subst.
  - constructor.
  - constructor.
  - constructor.
    unfold extend.
    destruct (string_dec x v); subst.
    + destruct H. constructor.
    + assumption. 
  - apply not_free_app_inv in H. destruct H.
    econstructor; eauto.
  - constructor.
    destruct (string_dec v x); subst.
    + eapply env_equiv_wt; eauto.
      apply env_equiv_symmetry.
      apply env_equiv_overwrite.
    + eapply IHe in H5; eauto.
      * eapply env_equiv_wt; eauto.
        apply env_equiv_extend_diff; auto.
      * intro. apply H.
        constructor; auto.
Qed.

Lemma subst_preserve_wt:
  forall e1 e2 x e1',
  Subst e1 e2 x e1' ->
  forall env te2 te1,
    WellTyped (extend env x te2) e1 te1 ->
    WellTyped env e2 te2 ->
    (forall v, ~ Free e2 v) ->
    WellTyped env e1' te1.
Proof.
  induction 1; intros.
  - inversion H; subst.
    constructor; auto.
  - inversion H; subst.
    constructor; auto.
  - inversion H; subst.
    rewrite lkup_extend_same in H4.
    inversion H4; subst. auto.
  - inversion H0; subst.
    rewrite lkup_extend_diff in H5; auto.
    constructor; auto.
  - inversion H1; subst.
    econstructor; eauto.
  - inversion H; subst.
    constructor; auto.
    eapply env_equiv_wt; eauto.
    apply env_equiv_overwrite.
  - inversion H1; subst.
    constructor; auto.
    eapply IHSubst; eauto.
    + eapply env_equiv_wt; eauto.
      eapply env_equiv_extend_diff; auto.
    + eapply weaken; eauto.
Qed.

Definition closed e :=
  forall v, ~ Free e v.

Lemma closed_app_inv:
  forall e1 e2,
  closed (e1 @ e2) ->
  closed e1 /\ closed e2.
Proof.
  unfold closed; split; intros; intro.
  - edestruct H; eauto.
    apply FAppL; eauto.
  - edestruct H; eauto.
    apply FAppR; eauto.
Qed.

Lemma closed_app_intro:
  forall e1 e2,
  closed e1 ->
  closed e2 ->
  closed (e1 @ e2).
Proof.
  unfold closed; intros; intro.
  inversion H1; subst.
  - firstorder.
  - firstorder.
Qed.

Lemma free_in_env:
  forall env e t,
  WellTyped env e t ->
  forall v, Free e v ->
  env v <> None.
Proof.
  induction 1; intros; intro.
  - inversion H.
  - inversion H.
  - inversion H0. subst.
    rewrite H in H1. discriminate.
  - inversion H0. subst.
    destruct IHWellTyped with (v := v); auto.
    rewrite lkup_extend_diff; auto.
  - inversion H1; subst.
    + destruct IHWellTyped1 with (v := v); auto.
    + destruct IHWellTyped2 with (v := v); auto.
Qed.

Lemma empty_closed:
  forall e t,
  WellTyped Empty e t ->
  closed e.
Proof.
  unfold closed; intros; intro.
  apply free_in_env with (v := v) in H; auto.
Qed.

Lemma preserve:
  forall env e t,
  WellTyped env e t ->
  closed e ->
  forall e',
  e --> e' ->
  WellTyped env e' t.
Proof.
  induction 1; intros.
  - inversion H0.
  - inversion H0.
  - inversion H1.
  - inversion H1.
  - apply closed_app_inv in H1; destruct H1.
    inversion H2; subst.
    + econstructor; eauto.
    + inversion H; subst.
      eapply subst_preserve_wt; eauto.
Qed.

Lemma not_free_subst:
  forall e1 e2 x e1',
  Subst e1 e2 x e1' ->
  forall v,
  ~ Free (\x, e1) v ->
  ~ Free e2 v ->
  ~ Free e1' v.
Proof.
  induction 1; intros; intro.
  - inversion H1.
  - inversion H1.
  - contradiction.
  - inversion H2; subst.
    apply H0. constructor; auto.
  - inversion H3; subst.
    + edestruct IHSubst1; eauto.
      intros; intro. inversion H4; subst.
      apply H1. constructor; auto.
      apply FAppL; auto.
    + edestruct IHSubst2; eauto.
      intros; intro. inversion H4; subst.
      apply H1. constructor; auto.
      apply FAppR; auto.
  - inversion H1; subst.
    apply H. constructor; auto.
  - inversion H3; subst.
    edestruct IHSubst; eauto.
    intros; intro. inversion H4; subst.
    apply H1.
    constructor; auto.
    constructor; auto.
Qed.

Lemma closed_subst:
  forall e1 e2 x e1',
  Subst e1 e2 x e1' ->
  closed (\x, e1) ->
  closed e2 ->
  closed e1'.
Proof.
  unfold closed; intros; intro.
  edestruct not_free_subst; eauto.
Qed.

Lemma closed_step:
  forall e e',
  e --> e' ->
  closed e ->
  closed e'.
Proof.
  induction 1; intros.
  - apply closed_app_inv in H0; destruct H0.
    apply closed_app_intro; auto.
  - apply closed_app_inv in H0; destruct H0.
    eapply closed_subst; eauto.
Qed.

Lemma preserve_star:
  forall e e',
  e -->* e' ->
  closed e ->
  forall env t,
  WellTyped env e t ->
  WellTyped env e' t.
Proof.
  induction 1; intros.
  - auto.
  - apply IHSSstar.
    + eapply closed_step; eauto.
    + eapply preserve; eauto.
Qed.

Lemma soundness:
  forall e t,
  WellTyped Empty e t ->
  forall e',
  e -->* e' ->
  (exists e'', e' --> e'') \/ Value e'.
Proof.
  intros. induction H0.
  - eapply progress. eassumption.
  - destruct IHSSstar; auto.
    + eapply preserve; eauto.
      eapply empty_closed; eauto.
Qed.
*)
