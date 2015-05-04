(* one little note - I'm not sure if this runs in peacoq, but it works fine in my 
 * proof-general. Is that a coq version thing?
 * For me peacoq fails in the if f is a value case in probelm 13. *)

Require Import List.
Require Import String.
Open Scope string_scope.

Definition var := string.

(** Lambda calculus syntax.

 We have variables, application, and abstraction. These are all we
 need in order to write programs to compute every computable function.
 *)
Inductive Expr : Set :=
| EConst                        (* The one and only constant     *)
| EVar (v : var)                (* Variables                     *)
| EApp (e1 : Expr) (e2 : Expr)  (* Application, e1 applied to e2 *)
| EAbs (x : var) (body : Expr). (* Abstraction, \x -> body       *)

Notation "'V' x" := (EVar x) (at level 48, only parsing).
Notation "e1 @ e2" := (EApp e1 e2) (at level 49, only parsing).
Notation "\ x , t" := (EAbs x t) (at level 50, only parsing).

Check (\"x", \"y", V"x").
Check (\"x", \"y", V"y").
Check ((\"x", V"x" @ V"x") @ (\"x", V"x" @ V"x")).

(**

In this homework you will implement call by value semantics of
lambda calculus. This means that when evaluating a function
application, (e1 e2) you will:

  1. evaluate e1 down as far as possible (it had better end up an abstraction)

  2. next, evaluate e2 down to a VALUE.
      NOTE: in our simple lambda calculus, abstractions and constants are values

  3. next, substitute the value we got for e2 into the simplified form of e1
      NOTE: we define a relation for what it means to be a well formed substitution below

*)

(* Here we formally define what it means to be a value (not able to be evaluated any more) *)
Definition isValue (e : Expr) : Prop :=
  match e with
    | EVar _ => False
    | EAbs _ _ => True
    | EConst => True
    | EApp _ _ => False
  end.

(**

Here we introduce what is called a decidability lemma.
Essentially we are saying that for any expression you have, it's either a value or not.
We need this because we can write down undecidable things as Props.

*)
Lemma isValueDec :
  forall e,
    { isValue e } + {~ isValue e}.
Proof.
  intros. destruct e; simpl; auto.
Defined.

(* Here we define what it means for a particular substitution to be valid *)
(* e1[e2/x] = e3 *)
Inductive Subst : Expr -> Expr -> var -> Expr -> Prop :=
| SubstConst : forall e x, (* substituting into a const is just that const *)
  Subst EConst e x EConst
| SubstVar_same : forall e x, (* substitute an expression in for a variable *)
  Subst (EVar x) e x e 
| SubstVar_diff : forall e x1 x2,
  x1 <> x2 ->
  Subst (EVar x1) e x2 (EVar x1)
| SubstApp : forall eA eB e x eA' eB',
  Subst eA e x eA' ->
  Subst eB e x eB' ->
  Subst (EApp eA eB) e x (EApp eA' eB')
| SubstAbs_same : forall eA e x,
  Subst (EAbs x eA) e x (EAbs x eA)
| SubstAbs_diff : forall eA e x1 x2 eA',
  x1 <> x2 ->
  Subst eA e x2 eA' ->
  Subst (EAbs x1 eA) e x2 (EAbs x1 eA').

(* Here we give semantics to our simple language *)
Inductive Step : Expr -> Expr -> Prop :=
| ScrunchLeft :
    forall e1 e1' e2,
      Step e1 e1' ->
      Step (EApp e1 e2) (EApp e1' e2)
| ScrunchRight :
    forall e1 e2 e2',
      isValue e1 ->
      Step e2 e2' ->
      Step (EApp e1 e2) (EApp e1 e2')
| Ssubst :
    forall x e1 e2 e1',
      isValue e2 ->
      Subst e1 e2 x e1' ->
      Step (EApp (EAbs x e1) e2) e1'.

(* Here we define the transitive closure of a step relation. Note that
we are able to define this once for any step relation, which is just
kinda cool *)
Inductive star (step : Expr -> Expr -> Prop) : Expr -> Expr -> Prop :=
 | star_refl :
     forall e,
       star step e e
 | star_right :
     forall e1 e2 e3,
       star step e1 e2 ->
       step e2 e3 ->
       star step e1 e3.

(* [Problem 1] *)
(* Implement a function to perform substitution *)
(* e1[e2/x] = e3 *)
(* Given e1, e2, and x, produce e3 *)
(* Your function should be a total function (no option in the return type *)
(* Hint: for equality of vars, use "string_dec" *)
Fixpoint subst e1 e2 x : Expr :=
  match e1 with
    | EConst => EConst
    | EVar y => if string_dec x y then e2 else EVar y 
    | EAbs y e1' => if string_dec x y then EAbs y e1' else EAbs y (subst e1' e2 x)
    | EApp el er => EApp (subst el e2 x) (subst er e2 x)
  end.

Definition e_test := \"x", \"y", V"x".

Check e_test.

Eval cbv in (subst (e_test) (V"yo") ("x")).

(* [Problem 2] *)
(* Prove that, given a valid term of the Subst relation, your function *)
(* from problem 1 will produce the same substitution. *)
Lemma Subst_subst:
  forall e1 e2 x e3,
    Subst e1 e2 x e3 -> subst e1 e2 x = e3.
Proof.
  intros. induction H.
  { reflexivity. }
  { simpl. destruct (string_dec x x).
    reflexivity.
    congruence. }
  (* why the hell doesn't anything work here *)
  { simpl. destruct (string_dec x2 x1).
    rewrite e0 in H. destruct H. reflexivity. 
    reflexivity. }
  { simpl. rewrite IHSubst1. rewrite IHSubst2. reflexivity. }
  { simpl. destruct (string_dec x x).
    reflexivity.
    congruence. }
  { simpl. destruct (string_dec x2 x1).
    rewrite e0 in H. destruct H. reflexivity.
    rewrite IHSubst. reflexivity. }
Qed.

(* [Problem 3] *)
(* Prove that if your function from problem 1 produces a substitution, *)
(* it's modeled by the Subst relation *)
(* This should look like problem 2 with the hypothesis and conclusion flipped *)
Lemma subst_Subst:
  forall e1 e2 x e3,
    subst e1 e2 x = e3 -> Subst e1 e2 x e3.
Proof.
  intro. induction e1.
  { intros. simpl in *. inversion H. constructor. }
  { intros. simpl in *. inversion H. destruct (string_dec x v).
    rewrite e. constructor.
    constructor. auto. }
  { intros. simpl in *. destruct e3; try discriminate. inversion H.
    specialize (IHe1_1 e2 x e3_1). specialize (IHe1_2 e2 x e3_2).
    rewrite H1. rewrite H2. constructor; auto. }
  { intros. simpl in *. destruct (string_dec x0 x).
    rewrite e. symmetry in H. rewrite H. constructor.
    symmetry in H. rewrite H. constructor; auto. }
Qed.

(* [Problem 4] *)
(* Define a step function *)
(* The skeleton of one has been provided *)
Fixpoint step (e : Expr) : option Expr :=
  match e with
    | EApp e1 e2 => 
      if isValueDec e1 then 
        if isValueDec e2 then
          match e1 with
            | EAbs x e1' => Some (subst e1' e2 x)
            | _ => None
          end
        else 
          match step e2 with 
              | Some e2' => Some (EApp e1 e2')
              | _ => None (* only happens for malformed terms *)
          end
      else
        match step e1 with
            | Some e1' => Some (EApp e1' e2)
            | _ => None (* only happens for malformed terms *)
        end
    | _ => None
  end.

(**
 * The proof of step_Step fails for this implementation
 * because we can't show that the e1 was a value, as we
 * require instead that it steps to something, and that direction
 * isn't provable for untyped terms.
 *) 
(**
  match e with
    | EApp e1 e2 => 
      match step e1 with
        | Some e1' => Some (EApp e1' e2)
        | None =>
          match step e2 with
            | Some e2' => Some (EApp e1 e2')
            | None =>
              match e1 with
                | EAbs x e1' => Some (subst e1' e2 x)
                | _ => None
              end
          end
      end
    | _ => None
  end.
**)    

(* In lambda calculus, we like to reason about what values can take
steps, and can't. We would love to know that if we have a value,
i.e. something that we have decided is the end result of a
computation, then it can't take a step *)

(* [Problem 5] *)
(* Prove that any value cannot take a step *)
Lemma value_no_step:
  forall e,
    isValue e -> step e = None.
Proof.
  intros. destruct e; auto. destruct H.
Qed.

(* Both ways are pretty easy to prove *)
Lemma value_no_Step:
  forall e,
    isValue e -> 
    forall e', 
      (~ (Step e e')).
Proof.
  intro. destruct e; intros; auto; intro; inversion H0.
Qed.

(* We have step function, and a Step relation *)
(* That means we can prove them equivalent *)
(* Let's make sure the step function is implemented correctly *)

(* In proving the next two lemmas, you may find bugs in your step *)
(* function. Change it all you need. Don't modify the Step relation. *)

(* When you've proven the next two lemmas, you will know that you got *)
(* your step function right *)

(* [Problem 6] *)
(* Prove that if the Step relation says e1 can step to e2, then your *)
(* step function will take e1 and produce "Some e2" *)
Lemma Step_step:
  forall e1 e2,
    Step e1 e2 -> step e1 = Some e2.
Proof.
(* I apologize for the messy subgoal organization in some of my proofs. *)
(* Let me try to make this one a little better. *)
  intros. induction H.
  { simpl in *. destruct (isValueDec e1). 
    - apply value_no_step in i. congruence.
    - destruct (step e1). 
      + inversion IHStep. reflexivity. 
      + discriminate. }
  { simpl in *. destruct (isValueDec e1); try contradiction. (* go away *)
    destruct (isValueDec e2).
    - apply value_no_step in i0. congruence.
    - destruct (step e2). 
      + inversion IHStep. reflexivity.
      + discriminate. }
  { simpl in *. destruct (isValueDec e2).
    - apply Subst_subst in H0. rewrite H0. reflexivity.
    - contradiction. }
Qed.

(* [Problem 7] *)
(* Prove that if your step function produces "Some", that the Step *)
(* relation models that step *)
Lemma step_Step:
  forall e1 e2,
    step e1 = Some e2 -> Step e1 e2.
Proof.
  (* For some reason I like putting curly braces around the top level goals
   * under my induction, but here those all get killed off by discriminate.
   * So, sadly, no curly braces. *)
  intro. induction e1; intros; simpl in *; try discriminate.
  destruct (isValueDec e1_1) in H.
  - destruct (isValueDec e1_2) in H.
    + destruct e1_1; try discriminate.
      inversion H. constructor; auto. 
      apply subst_Subst in H1. inversion H. rewrite H2. assumption.
    + destruct (step e1_2); try discriminate.
      inversion H. constructor; auto.
  - destruct (step e1_1); try discriminate.
    inversion H. constructor. auto. 
Qed.

(* That's awesome, we defined relations and functions for evaluation *)
(* Now, we were able to prove that if something is a value, it can't take a step *)
(* What if we were to try to prove the other way, that if something
   can't take a step, then it's not a value? *)

Lemma no_step_value :
  forall v,
    step v = None ->
    isValue v.
Proof.

Abort.

(* Turns out we can have malformed expressions, which can't step, but aren't values. *)

(* [Problem 8] *)
(* Explain in English how we can have expressions that both can't step and aren't values *)

(* [Problem 9] *)
(* Prove the following lemma in Coq to show you have a counterexample *)
Lemma no_step_and_not_value :
  exists e,
    step e = None /\ ~ isValue e.
Proof.
  exists (EApp EConst EConst). auto.
Qed.

(* How do we solve this? With types! *)

(* Here we define the types for the simply typed lambda calculus *)
Inductive SimpleType :=
  | TUnit
  | TFun (arg : SimpleType) (res : SimpleType).

(* Here we define what a type environment is *)
(* Simply a mapping from variables to types *)
Definition Env := var -> option SimpleType.

(* Here is how we extend a typing environment with another variable binding *)
Definition extend (env : Env) x t :=
  fun y => if string_dec x y then Some t else env y.

(* What it means for a lambda expression to be well typed *)
(* These are the type rules for STLC *)
(* You will frequently see them in the literature with horizontal lines *)
Inductive WellTyped : Env -> Expr -> SimpleType -> Prop :=
  | WtConst :
      forall env,
        WellTyped env EConst TUnit
  | WtVar :
      forall env x t,
        env x = Some t ->
        WellTyped env (EVar x) t
  | WtAbs :
      forall env x t exp t',
        WellTyped (extend env x t) exp t' ->
        WellTyped env (EAbs x exp) (TFun t t')
  | WtApp :
      forall env f arg t t',
        WellTyped env arg t ->
        WellTyped env f (TFun t t') ->
        WellTyped env (EApp f arg) t'.

(* [Problem 10] *)

(* Explain in English why we will run into trouble if we try to write *)
(* a typechecker as a function. For everything else, we write a relation *)
(* and a function, and prove the two equivalent. Why, in this particular *)
(* case, can we not simply write the "well_typed" function, of type *)
(* Env -> Expr -> SimpleType -> Bool? *)

(**
 * The problem (having tried to do this, see below) is that we don't carry
 * along enough information to figure out the types of abstractions.
 * If we try to check the type of an application, we don't know what type
 * to give to the argument when we check that term, nor the type of the
 * function itself, as we only have the return type.
 *
 * We might hope to fix this by writing another function that infers types
 * to figure out what type the argument has, but this fails for the same reason.
 * We can't infer the type of an abstraction because we don't know what argument
 * type it wants.
 *
 * It seems like we have to annotate abstractions with their types to get 
 * around this.
 *
 * It seems we *can* still write a typechecker function, but only in a very
 * roundabout way. We could perform general HM type inference to get
 * the most general type of the term, then see if that general type can be
 * specialized to the type we want to check against.
 * 
 * Of course this is really complicated, and I think still counts as trouble,
 * because we effectively had to solve the second bonus problem to pull it off.
 *)

(* Here's another decidability lemma for types *)
Lemma st_eq_dec :
  forall (t1 t2 : SimpleType),
    {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Qed.

(*
Fixpoint get_type env e : option SimpleType :=
  match e with 
    | EConst => Some TUnit
    | EVar x => env x
    | EAbs x e' => TFun ??? (get_type (extend env x ???) e')
    | ...

Fixpoint well_typed env e t : bool :=
  match e with
    | EConst =>
      match t with
        | TUnit => true 
        | _ => false 
      end
    | EVar x =>
      match env x with
        | Some t' => if st_eq_dec t t' then true else false
        | None => false
      end
    | EAbs x e' =>
      match t with 
        | Tfun t1 t2 => well_typed (extend env x t1) e' t2
        | _ => false.
      end
    | EApp e1 e2 => (andb (well_typed env e1 (TFun ??? t))
                          (well_typed env e2 ???))
  end.
*)

(* The empty environment *)
Definition Empty : Env := fun x => None.

(* [Problem 11] *)
(* Here's what we call a "canonical forms" lemma *)
(* We want to say that if something has a type of a value in an empty *)
(* context, it is in its "canonical form" *)
Lemma canonical_const :
  forall e,
    isValue e ->
    WellTyped Empty e TUnit ->
    e = EConst.
Proof.
  intros. destruct e; simpl in *; try contradiction.
  reflexivity.
  inversion H0.
Qed.

(* [Problem 12] *)
(* Here's something more interesting. Canonical forms for functions *)
Lemma canonical_abs :
  forall e t t',
    isValue e ->
    WellTyped Empty e (TFun t t') ->
    exists x body,
      e = EAbs x body.
Proof.
  intros. destruct e; simpl in *; try contradiction.
  inversion H0.
  exists x. exists e. reflexivity.
Qed.

(* [Problem 13] *)
(* In order to prove type soundness, we destructure the proof into two lemmas *)
(* The first one is called progress *)
(* If I have a well typed term, it can either take a step, or is a value *)
(* Prove the progress lemma *)
(* Hint: before inducting, use "remember Empty as env" to preserve the *)
(* knowledge that the environment is Empty *)
(* Hint: you will need one of your canonical forms lemmas from above *)
Lemma type_progress :
  forall e t,
    WellTyped Empty e t ->
    ((exists e', Step e e') \/ isValue e).
Proof.
  intros. remember Empty as env. induction H.
  { right. simpl. exact I. }
  { rewrite Heqenv in H. unfold Empty in H. discriminate. }
  { right. simpl. exact I. }
  { left. rewrite Heqenv in H0.  
    destruct (isValueDec f).
    (* if f is a value... *)
    - apply canonical_abs in H0; try assumption.
      destruct H0. destruct H0. rewrite H0.
      destruct (isValueDec arg).
      (* subgoal 1: assume arg is a value *)
      + exists (subst x0 arg x). 
        constructor; try assumption.
        apply subst_Subst. reflexivity.
      (* subgoal 2: assume arg isn't a value *)
      + destruct IHWellTyped1; try assumption. 
        * destruct H1. exists (EApp (EAbs x x0) x1).
          constructor; try assumption.
          simpl. exact I.
        * contradiction.
    (* if f isn't a value, then step it *)
    - destruct IHWellTyped2; try assumption.
      destruct H1. exists (EApp x arg).
      constructor; try assumption.
      contradiction. }
Qed.
