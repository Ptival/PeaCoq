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

(* [Problem 2] *)
(* Prove that, given a valid term of the Subst relation, your function *)
(* from problem 1 will produce the same substitution. *)

(* [Problem 3] *)
(* Prove that if your function from problem 1 produces a substitution, *)
(* it's modeled by the Subst relation *)
(* This should look like problem 2 with the hypothesis and conclusion flipped *)

(* [Problem 4] *)
(* Define a step function *)
(* The skeleton of one has been provided *)
Fixpoint step (e : Expr) : option Expr := None.

(* In lambda calculus, we like to reason about what values can take
steps, and can't. We would love to know that if we have a value,
i.e. something that we have decided is the end result of a
computation, then it can't take a step *)

(* [Problem 5] *)
(* Prove that any value cannot take a step *)

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

(* [Problem 7] *)
(* Prove that if your step function produces "Some", that the Step *)
(* relation models that step *)

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
  admit.
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

(* Here's another decidability lemma for types *)
Lemma st_eq_dec :
  forall (t1 t2 : SimpleType),
    {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
Qed.

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
  admit.
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
  admit.
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
  admit.
Qed.

(* The second lemma is called type preservation *)
(* In order to prove that, we're going to need a lot of auxiliary machinery *)
(* Don't worry, I'll walk you through it. *)

(* FROM THIS POINT ON *)
(* I may not tell you to use a lemma that you've previously proved *)
(* but you absolutely should *)

(* I give you the lemmas I think you need to succeed. If you need more *)
(* lemmas that's completely fine. If you try to do some of these proofs *)
(* without using the lemmas you've already proven, you will not have a *)
(* good time. *)

(* Here we define what it means for two environments to be extensionally equivalent *)
(* Extensional Equality for functions means they return the same result for every argument *)
(* for example, \x -> 1 + x and \x -> x + 1 are extensionally equivalent, but not the same function *)
Definition ext_equiv (env1 env2 : Env) : Prop :=
  forall x,
    env1 x = env2 x.

(* [Problem 14] *)
(* Prove a lemma about extending extensionally equivalent environments *)
Lemma extend_pres_ext_equiv :
  forall env env2,
    ext_equiv env env2 ->
    forall x t,
      ext_equiv (extend env x t) (extend env2 x t).
Proof.
  admit.
Qed.

(* [Problem 15] *)
(* Prove that if a term is well typed in an environment, it is also *)
(* well typed in any extensionally equivalent environment *)
(* Hint: Be careful with your induction *)
Lemma well_typed_ext_equiv :
  forall env1 e t,
    WellTyped env1 e t ->
    forall env2,
      ext_equiv env1 env2 ->
      WellTyped env2 e t.
Proof.
  admit.
Qed.

(* [Problem 16] *)
(* Prove that extending an environment with the same variable twice is *)
(* the same as extending it once *)
(* Hint: use well_typed_ext_equiv *)
Lemma extend_same:
  forall env x t t' e t'',
    WellTyped (extend (extend env x t) x t') e t'' <->
    WellTyped (extend env x t') e t''.
Proof.
  admit.
Qed.

(* [Problem 17] *)
(* Prove that extending an environment with two different variables is *)
(* ok to do in either order *)
Lemma extend_different:
  forall e t env x1 x2 t1 t2,
    x1 <> x2 ->
    (WellTyped (extend (extend env x2 t2) x1 t1) e t <->
    WellTyped (extend (extend env x1 t1) x2 t2) e t).
Proof.
  admit.
Qed.

(* Here we define what free variables exist in an expression *)
(* Intuitively, these are all the variables which exist, but are not *)
(* bound by an abstraction *)
Fixpoint free_variables (e : Expr) : list var :=
  match e with
    | EConst => nil
    | EVar x => x :: nil
    | EAbs x body => remove string_dec x (free_variables body)
    | EApp e1 e2 => app (free_variables e1) (free_variables e2)
  end.

(* [Problem 18] *)
(* This may seem to be an obvious lemma about remove and lists *)
(* It does not happen to be in the standard library *)
(* Let's go prove it *)
Lemma remove_different :
  forall {A} (eq_dec : forall (a b : A), {a = b} + {a <> b}) l x y,
    x <> y ->
    (In x l <->
    In x (remove eq_dec y l)).
Proof.
  admit.
Qed.

(* [Problem 19] *)
(* Here we prove what's called weakening *)
(* If a variable isn't in the free variables of an expression, *)
(* we can extend the context with that variable, and produce the same *)
(* typing derivation *)
Lemma weakening :
  forall e env t x t',
    ~ (In x (free_variables e)) ->
    (WellTyped (extend env x t') e t <->
    WellTyped env e t).
Proof.
  admit.
Qed.

(* [Problem 20] *)
(* Here we prove that a correct substitution preserves typing *)
(* This one's a bit tricky, but remember to use inversion where *)
(* necessary, and to use previously proven lemmas *)
Lemma subst_type_pres :
  forall e e' e'' x,
    Subst e' e x e'' ->
    forall env t t',
      WellTyped env e t ->
      free_variables e = nil ->
      WellTyped (extend env x t) e' t' ->
      WellTyped env e'' t'.
Proof.
  admit.
Qed.

(* [Problem 21] *)
(* Here we prove that if we have free variables in an expression, we *)
(* need them in the type environment if that is well typed *)
Lemma env_vars_required :
  forall env e t,
    WellTyped env e t ->
    (forall x, In x (free_variables e) -> env x <> None).
Proof.
  admit.
Qed.

(* [Problem 22] *)
(* Here we prove that something that's well typed in the empty *)
(* environment has no free variables *)
(* Hint: Use a previously proven lemma *)
Lemma no_free_vars_empty :
  forall e t,
    WellTyped Empty e t ->
    free_variables e = nil.
Proof.
  admit.
Qed.

(* [Problem 23] *)
(* We finally have enough lemmas to prove type preservation, the other *)
(* lemma necessary for type soundness. It says that if we have a well *)
(* typed term, and take a step, then the result is still well typed with *)
(* the same type. *)
Lemma type_preservation :
  forall e t,
    WellTyped Empty e t ->
    forall e',
      Step e e' ->
      WellTyped Empty e' t.
Proof.
  admit.
Qed.

(* [Problem 24] *)
(* Prove type preservation over any sequence of steps *)
(* The lemma should look almost identical to the previous problem *)

(* [Problem 25] *)
(* Prove that our simple type system for lambda calculus is sound *)
(* Prove that any term reachable from any well typed term can either *)
(* take a step, or is a value *)
Theorem type_soundness :
  forall e t,
    WellTyped Empty e t ->
    forall e',
      star Step e e' ->
      (exists e'', Step e' e'') \/ isValue e'.
Proof.
  admit.
Qed.

(* Crowning Achievement *)
(* [Problem 26] *)
(* Prove the lemma we originally set out to prove, but with the *)
(* additional hypothesis of the term being well typed *)
Lemma no_step_value_typed :
  forall e t,
    WellTyped Empty e t ->
    step e = None ->
    isValue e.
Proof.
  admit.
Qed.
  
(* Bonus Problem 1 *)
(* Hint: you will need strong induction on the size of the type *)
(* which means you will need to define what the size of the type means *)
(* Theorem strong_normalization : *)
(*   forall t e, *)
(*     WellTyped Empty e t -> *)
(*     exists v, *)
(*       star Step e v /\ isValue v. *)
(* Proof. *)
(* Note: the implication of this is interesting. This says that every *)
(* well typed term will halt. *)


(* Bonus Problem 2 *)
(* Construct your own definitions of the simply typed lambda calculus *)
(* that allow you to write a typechecker as a function (i.e. to get *)
(* around the problem you describe above) *)


