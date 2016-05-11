Require Import Coq.Lists.List.
Import ListNotations.
(* Heterogeneous lists *)
(***********************)
Section hlist.
(* Heterogeneous lists are lists where the elements of the
 * list can have different types. In Coq, we can define
 * heterogeneous lists by indexing an inductive type by
 * a list of types, one for each element. For convenience
 * in the future however, we will index our type by an
 * a type [iT] and a function (F) that computes a type from
 * [iT]. This will make our definition a little bit easier
 * to use in the next exercise.
 *)
Variable iT : Type.
Variable F : iT -> Type.

Inductive hlist : list iT -> Type :=
| Hnil : hlist nil
| Hcons : forall {T Ts}, F T -> hlist Ts -> hlist (T :: Ts).

(* Exercise: Implement the head and tail functions for hlists.
 *)
Definition hlist_hd {T Ts} (h : hlist (T :: Ts)) : F T :=
  match h with
  | Hcons x _ => x
  | Hnil => tt
  end.

Definition hlist_tl {T Ts} (h : hlist (T :: Ts)) : hlist Ts :=
  match h with
  | Hcons _ xs => xs
  | Hnil => tt
  end.


(* An alternative solution is to build an inductive
 * type that carries the information about the value that
 * we find at a particular location in the list.
 *)
Inductive mem {T : Type} (t : T) : list T -> Type :=
| MO : forall {ts}, mem t (t :: ts)
| MS : forall {t' ts}, mem t ts -> mem t (t' :: ts).

Arguments MO {_ _ _}.
Arguments MS {_ _ _ _} _.

(* Exercise: Implement hlist_nth with the following type.
 *)
Fixpoint hlist_nth {T Ts} (h : hlist Ts) (n : mem T Ts) : F T :=
  match n in mem _ Ts return hlist Ts -> F T with
  | MO => hlist_hd
  | MS m => fun h => hlist_nth (hlist_tl h) m
  end h.

End hlist.

Arguments hlist {_} _ _.
Arguments hlist_hd {_ _ _ _} _.
Arguments hlist_tl {_ _ _ _} _.
Arguments hlist_nth {_ _ _ _} _ _.
Arguments Hnil {_ _}.
Arguments Hcons {_ _ _ _} _ _.

Arguments MO {_ _ _}.
Arguments MS {_ _ _ _} _.

Section mem_dec.
  Variable T : Type.
  (* In order to implement decidable equality for [mem], we
   * need decidable equality for the type T. The reason for
   * this is a little bit unintuitive but it turns out to be
   * true.
   *)
  Variable T_dec : forall a b : T, a = b \/ a <> b.

  Lemma MS_inj : forall t t' ts (m m' : mem t ts),
      @MS T t t' ts m = MS m' ->
      m = m'.
  Proof.
    intros.
    refine
      match H in _ = M
            return match M in mem _ ts return mem _ (tl ts) -> Prop with
                   | MO => fun _ => True
                   | MS m'' => fun m => m = m''
                   end m
      with
      | eq_refl => eq_refl
      end.
  Defined.

  (* A theorem in Coq tells us that decidable equality on
   * a type [T] implies proof irrelevence for proofs of equality
   * of values of type [T].
   *)
  Require Import Coq.Logic.Eqdep_dec.

  Fixpoint mem_dec {ts : list T} {t : T} (a : mem t ts)
  : forall b : mem t ts, {a = b} + {a <> b}.
  refine
    match a as a in mem _ ts
          return forall b : mem t ts, {a = b} + {a <> b}
    with
    | MO => fun b =>
      match b as b in mem _ ts
            return match ts as ts return mem t ts -> Type with
                   | nil => fun _ => unit
                   | t' :: ts => fun b =>
                                   forall pf : t' = t,
                                     {MO = match pf with
                                           | eq_refl => b
                                           end} +
                                     {MO <> match pf with
                                            | eq_refl => b
                                            end}
                   end b
      with
      | MO => fun _ => left _
      | MS m'' => fun _ => right _
      end eq_refl
    | @MS _ _ t' ts' m' => fun (b : mem t (t' :: ts')) =>
      match b as b in mem _ ts
            return forall m' : mem t (tl ts),
          (forall b, {m' = b} + {m' <> b}) ->
          match ts as ts return mem t ts -> mem t (tl ts) -> Type with
          | nil => fun _ _ => unit
          | t'' :: ts'' => fun (b : mem t (t'' :: ts'')) m' =>
                             {MS m' = b} +
                             {MS m' <> b}
          end b m'
      with
      | MO => fun _ _ => right _
      | MS m'' => fun _ rec =>
                        match rec m'' with
                        | left _ => left _
                        | right _ => right _
                        end
      end m' (fun b => mem_dec _ _ m' b)
    end.
  Proof.
  { eapply K_dec with (p := e); auto. }
  { subst. intro. inversion H. }
  { clear. red; intro. inversion H. }
  { f_equal. assumption. }
  { clear - n. intro. apply n.
    eapply MS_inj in H. assumption. }
  Defined.
End mem_dec.

Arguments mem_dec {_} _ {_ _} _ _.

(* A simple Lambda-calculus *)
(****************************)

(* We can use dependent types to describe "well-typed" terms.
 * We start with a type of types.
 *)
Inductive type : Type :=
| Nat
| Bool
| Arr (d c : type)
.

(* I've started a simple definition with just constants, addition
 * and variables.
 *)
Inductive expr (ts : list type) : type -> Type :=
| ConstNat  : nat -> expr ts Nat
| Plus      : expr ts Nat -> expr ts Nat -> expr ts Nat
| ConstBool : bool -> expr ts Bool
| If        : forall t, expr ts Bool -> expr ts t -> expr ts t -> expr ts t
| App       : forall d c, expr ts (Arr d c) -> expr ts d -> expr ts c
| Abs       : forall d c, expr (d :: ts) c -> expr ts (Arr d c)
| Var       : forall {t}, mem t ts -> expr ts t
| PlusE     : expr ts (Arr Nat (Arr Nat Nat)).

Arguments ConstNat {_} _.
Arguments Plus {_} _ _.
Arguments ConstBool {_} _.
Arguments If {_ _} _ _ _.
Arguments App {_ _ _} _ _.
Arguments Abs {_ _ _} _.
Arguments Var {_ _} _.
Arguments PlusE {_}.

(* We can now write functions that map the syntactic definitions
 * into semantic ones.
 *)
Fixpoint typeD (t : type) : Type :=
  match t with
  | Nat => nat
  | Bool => bool
  | Arr l r => typeD l -> typeD r
  end.

Fixpoint exprD {ts : list type} {t : type} (e : expr ts t)
: hlist typeD ts -> typeD t :=
  match e in expr _ t return hlist typeD ts -> typeD t with
  | ConstNat n => fun _ => n
  | Plus a b => let aD := exprD a in let bD := exprD b in
                fun env => aD env + bD env
  | ConstBool b => fun _ => b
  | If t tr fa => let tD := exprD t in
                    let trD := exprD tr in
                    let faD := exprD fa in
                    fun env =>
                      if tD env then trD env else faD env
  | App f x => let fD := exprD f in
                   let xD := exprD x in
                   fun env => (fD env) (xD env)
  | Abs body => let bodyD := exprD body in
                    fun env => (fun x => bodyD (Hcons x env))
  | Var v => fun e => hlist_nth e v
  | PlusE => fun e => plus
  end.

Eval simpl in exprD (ConstNat 3) Hnil.
Eval simpl in exprD (Plus (ConstNat 3) (ConstNat 6)) Hnil.
Eval simpl in fun x : typeD Nat =>
                  exprD (Plus (Var MO) (ConstNat 6)) (Hcons x Hnil).

(* Exercise: Implement semi-decidable equality for this type.
 * (We can implement decidable equality, but it is a bit annoying
 *  due to constructing proofs of disequality.)
 * Avoid using tactics except to construct values whose type is
 * in Prop, i.e. only use tactics to prove equalities and
 * disequalities.
 *)
Definition type_dec (t1 t2 : type) : {t1 = t2} + {t1 <> t2}.
decide equality.
Defined.

Definition nat_dec : forall a b : nat, {a = b} + {a <> b}.
decide equality.
Defined.

Definition bool_dec : forall a b : bool, {a = b} + {a <> b}.
decide equality.
Defined.

Definition type_decidable (t1 t2 : type) : (t1 = t2) \/ (t1 <> t2) :=
  match type_dec t1 t2 with
  | left pf => or_introl pf
  | right pf => or_intror pf
  end.

Definition domain (t : type) : type :=
  match t with
  | Arr a _ => a
  | _ => t
  end.

Definition codomain (t : type) : type :=
  match t with
  | Arr _ b => b
  | _ => t
  end.

Definition expr_match_Nat {ts}
           (P : expr ts Nat -> Type)
           (doConst : forall n, P (ConstNat n))
           (doPlus : forall a b, P (Plus a b))
           (doIf : forall t tr fa, P (If t tr fa))
           (doApp : forall d' f x, P (@App ts d' Nat f x))
           (doVar : forall m, P (Var m))
: forall e : expr ts Nat, P e.
refine (fun e =>
  match e as e in expr _ X
        return match X as X return expr ts X -> Type with
               | Nat => fun e =>
                 forall (doConst : forall n, P (ConstNat n))
                        (doPlus : forall a b, P (Plus a b))
                        (doIf : forall t tr fa, P (If t tr fa))
                        (doApp : forall d' f x, P (@App ts d' Nat f x))
                        (doVar : forall m, P (Var m)),
                   P e
               | _ => fun _ => unit
               end e
  with
  | ConstNat n => fun doConst _ _ _ _ => doConst n
  | _ => _
  end doConst doPlus doIf doApp doVar);
  try solve [ intros; exact tt
            | eauto
            | destruct t; try exact tt; eauto
            | destruct t0; try exact tt; eauto ].
Defined.

Definition expr_match_Bool {ts}
           (P : expr ts Bool -> Type)
           (doConst : forall b, P (ConstBool b))
           (doIf : forall t tr fa, P (If t tr fa))
           (doApp : forall d' f x, P (@App ts d' Bool f x))
           (doVar : forall m, P (Var m))
: forall e : expr ts Bool, P e.
refine (fun e =>
  match e as e in expr _ X
        return match X as X return expr ts X -> Type with
               | Bool => fun e =>
                 forall (doConst : forall n, P (ConstBool n))
                        (doIf : forall t tr fa, P (If t tr fa))
                        (doApp : forall d' f x, P (@App ts d' Bool f x))
                        (doVar : forall m, P (Var m)),
                   P e
               | _ => fun _ => unit
               end e
  with
  | ConstBool n => fun doConst _ _ _ => doConst n
  | _ => _
  end doConst doIf doApp doVar);
  try solve [ intros; exact tt
            | eauto
            | destruct t; try exact tt; eauto
            | destruct t0; try exact tt; eauto ].
Defined.

Definition expr_match_Arr {ts} {d c : type}
           (P : forall d c, expr ts (Arr d c) -> Type)
           (doIf : forall t tr fa, @P d c (If t tr fa))
           (doApp : forall d' f x, @P d c (@App ts d' (Arr d c) f x))
           (doAbs : forall body, P d c (Abs body))
           (doVar : forall m, P d c (Var m))
           (doPlusE : P Nat (Arr Nat Nat) PlusE)
: forall e : expr ts (Arr d c), P d c e.
refine (fun e =>
  match e as e in expr _ X
        return
          match X as X return expr ts X -> Type with
          | Arr d c => fun e =>
            forall (doIf : forall t tr fa, @P d c (If t tr fa))
                   (doApp : forall d' f x, @P d c (@App ts d' (Arr d c) f x))
                   (doAbs : forall body, P d c (Abs body))
                   (doVar : forall m, P d c (Var m))
                   (doPlusE : P Nat (Arr Nat Nat) PlusE), P d c e
          | _ => fun _ => unit
          end e
  with
  | ConstNat _ => tt
  | ConstBool _ => tt
  | Plus _ _ => tt
  | If t tr fa => _
  | _ => _
  end doIf doApp doAbs doVar doPlusE);
  try solve [ intros; exact tt
            | eauto
            | destruct t0; try exact tt; auto
            | destruct t; try exact tt; eauto ].
Defined.

Definition expr_match_Arr' {ts} {d c : type}
           (P : forall d c, expr ts (Arr d c) -> Type)
           (doIf : forall t tr fa, @P d c (If t tr fa))
           (doApp : forall d' f x, @P d c (@App ts d' (Arr d c) f x))
           (doAbs : forall body, P d c (Abs body))
           (doVar : forall m, P d c (Var m))
           (doPlusE : P Nat (Arr Nat Nat) PlusE)
: forall e : expr ts (Arr d c), P d c e.
refine (fun e =>
  match e as e in expr _ X
        return
        forall (doIf : match X return Type with
                       | Arr d c => forall t tr fa, @P d c (If t tr fa)
                       | _ => unit
                       end)
               (doApp : match X return Type with
                        | Arr d c => forall d' f x, @P d c (@App ts d' (Arr d c) f x)
                        | _ => unit
                        end)
               (doAbs : match X return Type with
                        | Arr d c => forall body, P d c (Abs body)
                        | _ => unit
                        end)
               (doVar : match X return Type with
                        | Arr d c => forall m, P d c (Var m)
                        | _ => unit
                        end)
               (doPlusE : P Nat (Arr Nat Nat) PlusE),
          match X as X return expr ts X -> Type with
          | Arr d c => fun e => P d c e
          | _ => fun _ => unit
          end e
  with
  | ConstNat _ => _
  | ConstBool _ => _
  | Plus _ _ => _
  | If t tr fa => _
  | _ => _
  end doIf doApp doAbs doVar doPlusE);
  try solve [ intros; exact tt
            | eauto
            | destruct t0; try exact tt; eauto
            | destruct t; try exact tt; eauto ].
Defined.

Fixpoint expr_dec {ts t} (e1 : expr ts t)
: forall e2 : expr ts t, option (e1 = e2).
refine
  match e1 as e1 in expr _ t
        return forall e2 : expr ts t, option (e1 = e2)
  with
  | ConstNat n => fun e2 =>
    match e2 as e2 in expr _ t
          return option (match t as t return expr ts t -> Prop with
                         | Nat => fun e2 => ConstNat n = e2
                         | _ => fun _ => False
                         end e2) with
    | ConstNat m =>
      match nat_dec n m with
      | left pf => Some match pf with
                        | eq_refl => eq_refl
                        end
      | right _ => None
      end
    | _ => None
    end
  | Plus l r => fun e2 =>
    match e2 as e2 in expr _ t
          return forall a b : expr ts Nat,
        option (match t as t return expr ts t -> Prop with
                | Nat => fun e2 => Plus a b = e2
                | _ => fun _ => False
                end e2)
    with
    | Plus l' r' => fun l r =>
      match expr_dec _ _ l l' , expr_dec _ _ r r' with
      | Some pf1 , Some pf2 => Some match pf1 , pf2 with
                                    | eq_refl , eq_refl => eq_refl
                                    end
      | _ , _ => None
      end
    | _ => fun _ _ => None
    end l r
  | ConstBool b => fun e2 =>
    match e2 as e2 in expr _ t
          return option (match t as t return expr ts t -> Prop with
                         | Bool => fun e2 => ConstBool b = e2
                         | _ => fun _ => False
                         end e2)
    with
    | ConstBool m =>
      match bool_dec b m with
      | left pf => Some match pf with
                        | eq_refl => eq_refl
                        end
      | right _ => None
      end
    | _ => None
    end
  | If t tr fa => fun e2 =>
    match e2 as e2 in expr _ T
          return forall (t : expr ts Bool) (tr fa : expr ts T),
        option (If t tr fa = e2)
    with
    | If t' tr' fa' => fun t tr fa =>
      match expr_dec _ _ t t'
          , expr_dec _ _ tr tr'
          , expr_dec _ _ fa fa'
      with
      | Some pf , Some pf' , Some pf'' =>
        Some match pf , pf' , pf'' with
             | eq_refl , eq_refl , eq_refl => eq_refl
             end
      | _ , _ , _ => None
      end
    | _ => fun _ _ _ => None
    end t tr fa
  | @App _ d c f x => fun e2 =>
    match e2 as e2 in expr _ t
          return forall (f : expr ts (Arr d t))
                        (x : expr ts d)
                        (rec_f : forall e, option (f = e))
                        (rec_x : forall e, option (x = e)),
        option (App f x = e2)
    with
    | @App _ d' c' f' x' =>
      match type_dec d' d with
      | right _ => fun _ _ _ _ => None
      | left pf =>
        match pf in _ = X
              return forall f' x'
                            (f : expr ts (Arr X c'))
                            (x : expr ts X)
                            (rec_f : forall e, option (f = e))
                            (rec_x : forall e, option (x = e)),
            option (App f x = App f' x')
        with
        | eq_refl => fun f' x' _ _ rec_f rec_x =>
                       match rec_f f' , rec_x x' with
                       | Some pf , Some pf' =>
                         Some match pf , pf' with
                              | eq_refl , eq_refl => eq_refl
                              end
                       | _ , _ => None
                       end
        end f' x'
      end
    | _ => fun _ _ _ _ => None
    end f x (fun y => expr_dec _ _ f y) (fun y => expr_dec _ _ x y)
  | @Abs _ d c body => fun e2 =>
    match e2 as e2 in expr _ t
          return forall (body : expr (domain t :: ts) (codomain t))
                        (rec : forall e, option (body = e)),
        option (match t as t
                      return expr (domain t :: ts) (codomain t) -> expr ts t -> Prop
                with
                | Arr d' c' => fun body e2 => Abs body = e2
                | _ => fun _ _ => False
                end body e2)
    with
    | @Abs _ d' c' body' => fun _ rec =>
                           match rec body' with
                           | None => None
                           | Some pf => Some match pf with
                                             | eq_refl => eq_refl
                                             end
                           end
    | _ => fun _ _ => None
    end body (fun y => expr_dec _ _ body y)
  | Var v => fun e2 =>
    match e2 as e2 in expr _ t
          return forall v : mem t ts, option (Var v = e2)
    with
    | Var v' => fun v =>
      match mem_dec type_decidable v v' with
      | left pf => Some match pf in _ = X with
                        | eq_refl => eq_refl
                        end
      | right _ => None
      end
    | _ => fun _ => None
    end v
  | PlusE => fun e2 : expr ts (Arr Nat (Arr Nat Nat)) =>
    match e2 as e2 in expr _ t
          return option (match t as t return expr ts t -> Prop with
                         | Arr Nat (Arr Nat Nat) => fun e2 => PlusE = e2
                         | _ => fun _ => False
                         end e2)
    with
    | PlusE => Some eq_refl
    | _ => None
    end
  end.
Defined.


Fixpoint expr_dec' {ts t} (e1 : expr ts t)
: forall e2 : expr ts t, option (e1 = e2).
refine
  match e1 as e1 in expr _ t
        return forall e2 : expr ts t, option (e1 = e2)
  with
  | ConstNat n =>
    expr_match_Nat (fun e2 => option (ConstNat n = e2))
                   (fun m =>
                      match nat_dec n m with
                      | left pf => Some match pf with
                                        | eq_refl => eq_refl
                                        end
                      | right _ => None
                      end)
                   (fun _ _ => None)
                   (fun _ _ _ => None)
                   (fun _ _ _ => None)
                   (fun _ => None)
  | Plus l r =>
    expr_match_Nat (fun e2 => option (Plus l r = e2))
                   (fun _ => None)
                   (fun l' r' =>
                      match expr_dec' _ _ l l' , expr_dec' _ _ r r' with
                      | Some pf1 , Some pf2 =>
                        Some match pf1 , pf2 with
                             | eq_refl , eq_refl => eq_refl
                             end
                      | _ , _ => None
                      end)
                   (fun _ _ _ => None)
                   (fun _ _ _ => None)
                   (fun _ => None)
  | ConstBool b =>
    expr_match_Bool (fun e2 => option (ConstBool b = e2))
                    (fun b' =>
                       match bool_dec b b' with
                       | left pf => Some match pf with
                                         | eq_refl => eq_refl
                                         end
                       | right _ => None
                       end)
                    (fun _ _ _ => None)
                    (fun _ _ _ => None)
                    (fun _ => None)
  | If t tr fa => fun e2 =>
    match e2 as e2 in expr _ T
          return forall (t : expr ts Bool) (tr fa : expr ts T),
        option (If t tr fa = e2)
    with
    | If t' tr' fa' => fun t tr fa =>
      match expr_dec' _ _ t t'
          , expr_dec' _ _ tr tr'
          , expr_dec' _ _ fa fa'
      with
      | Some pf , Some pf' , Some pf'' =>
        Some match pf , pf' , pf'' with
             | eq_refl , eq_refl , eq_refl => eq_refl
             end
      | _ , _ , _ => None
      end
    | _ => fun _ _ _ => None
    end t tr fa
  | @App _ d c f x => _
  | @Abs _ d c body => fun e2 =>
    expr_match_Arr (fun d c e2 => forall body,
                        (forall e, option (body = e)) ->
                        option (Abs body = e2))
                   (fun _ _ _ _ _ => None)
                   (fun _ _ _ _ _ => None)
                   (fun body' _ rec_body =>
                      match rec_body body' with
                      | Some pf => Some match pf with
                                        | eq_refl => eq_refl
                                        end
                      | None => None
                      end)
                   (fun _ _ _ => None)
                   (fun _ _ => None)
                   e2 body (fun e => expr_dec' _ _ body e)
  | Var v => fun e2 =>
    match e2 as e2 in expr _ t
          return forall v : mem t ts, option (Var v = e2)
    with
    | Var v' => fun v =>
      match mem_dec type_decidable v v' with
      | left pf => Some match pf in _ = X with
                        | eq_refl => eq_refl
                        end
      | right _ => None
      end
    | _ => fun _ => None
    end v
  | PlusE =>
    expr_match_Arr (fun d c e => option (PlusE = e))
                   _ _ _ _ _
  end.

Defined.



(* Exercise: Implement a function that simplifies expressions.
 *)
Definition reduce1 {ts t} (e : expr ts t) : expr ts t :=
  match e in expr _ t return expr ts t -> expr ts t with
  | Plus (ConstNat x) (ConstNat y) => fun _ => ConstNat (x + y)
  | App Nat Nat (App Nat (Arr Nat Nat) PlusE (ConstNat x)) (ConstNat y) =>
    fun _ => ConstNat (x + y)
  | If _ (ConstBool true) tr _ => fun _ => tr
  | If _ (ConstBool false) _ fa => fun _ => fa
  | If _ t tr fa => fun e =>
    if expr_dec tr fa then tr else e
  | _ => fun x => x
  end e.

Lemma if_same : forall T (x : bool) (a : T),
    (if x then a else a) = a.
Proof. destruct x; reflexivity. Qed.

Lemma expr_case_Arr : forall d c ts (e : expr ts (Arr d c)),
    (exists body, e = Abs body) \/
    (exists test tr fa, e = If test tr fa) \/
    (exists d' f x, e = @App ts d' (Arr d c) f x) \/
    (exists m, e = Var m) \/
    (exists (pf : Nat = d) (pf' : Arr Nat Nat = c),
        e = match pf , pf' with
            | eq_refl , eq_refl => PlusE
            end).
Proof.
  intros.
  refine
    match e as e in expr _ t
          return match t as t return expr ts t -> Prop with
                 | Arr d c => fun e =>
                                (exists body : expr (d :: ts) c, e = Abs body) \/
                                (exists (test : expr ts Bool) (tr fa : expr ts (Arr d c)),
                                    e = If test tr fa) \/
                                (exists (d' : type) (f : expr ts (Arr d' (Arr d c)))
                                        (x : expr ts d'), e = App f x) \/
                                (exists m : mem (Arr d c) ts, e = Var m) \/
                                (exists (pf : Nat = d) (pf' : Arr Nat Nat = c),
                                    e =
                                    match pf in (_ = t) return (expr ts (Arr t c)) with
                                    | eq_refl =>
                                      match pf' in (_ = t) return (expr ts (Arr Nat t)) with
                                      | eq_refl => PlusE
                                      end
                                    end)
                 | _ => fun _ => True
                 end e
    with
    | ConstNat _ => I
    | Plus _ _ => I
    | ConstBool _ => I
    | _ => _
    end.
  { destruct t; eauto 10. }
  { destruct c0; eauto 10. }
  { eauto. }
  { destruct t; eauto 10. }
  { repeat right. exists eq_refl. exists eq_refl. reflexivity. }
Qed.

Theorem reduce1_sound : forall ts t (e : expr ts t),
    forall env, exprD (reduce1 e) env = exprD e env.
Proof.
  destruct e; simpl; auto.
  { refine
      match e1 as e1 in expr _ X1
          , e2 as e2 in expr _ X2
            return match X1 as X1 , X2 as X2
                         return expr ts X1 -> expr ts X2 -> Prop
                   with
                   | Nat , Nat => fun e1 e2 =>
                                    forall env : hlist typeD ts,
                                      exprD
                                        (match e1 with
                                         | ConstNat a =>
                                           match e2 with
                                           | ConstNat b => fun _ : expr ts Nat => ConstNat (a + b)
                                           | _ => fun e' : expr ts Nat => e'
                                           end
                                         | _ => fun e' : expr ts Nat => e'
                                         end (Plus e1 e2)) env =
                                      exprD e1 env + exprD e2 env
                   | _ , _ => fun _ _ => True
                   end e1 e2
      with
      | ConstNat _ , ConstNat _ => fun _ => eq_refl
      | _ , _ => _
      end; try solve [ reflexivity | destruct t; reflexivity ].
    destruct c; trivial. destruct c; trivial. }
  { refine
      match e1 as e1 in expr _ X1
            return match X1 as X1 return expr ts X1 -> Prop with
                   | Bool => fun e1 => forall env : hlist typeD ts,
                       exprD
                         (match e1 with
                          | ConstNat _ => fun e : expr ts t => if expr_dec e2 e3 then e2 else e
                          | Plus _ _ => fun e4 : expr ts t => if expr_dec e2 e3 then e2 else e4
                          | ConstBool true => fun _ : expr ts t => e2
                          | ConstBool false => fun _ : expr ts t => e3
                          | If _ _ _ _ => fun e5 : expr ts t => if expr_dec e2 e3 then e2 else e5
                          | App _ _ _ _ => fun e : expr ts t => if expr_dec e2 e3 then e2 else e
                          | Abs _ _ _ => fun e : expr ts t => if expr_dec e2 e3 then e2 else e
                          | Var _ _ => fun e : expr ts t => if expr_dec e2 e3 then e2 else e
                          | PlusE => fun e : expr ts t => if expr_dec e2 e3 then e2 else e
                          end (If e1 e2 e3)) env =
                       (if exprD e1 env then exprD e2 env else exprD e3 env)
                   | _ => fun _ => True
                   end e1
      with
      | ConstBool true => fun _ => eq_refl
      | ConstBool false => fun _ => eq_refl
      | ConstNat _ => I
      | Plus _ _ => I
      | Abs _ _ _ => I
      | _ => _
      end;
    repeat (match goal with
            | |- match ?X with _ => _ end _ => destruct X
            end; trivial; simpl; intros);
    destruct (expr_dec e2 e3); simpl; subst; try rewrite if_same; reflexivity. }
  { (* This case is a little bit ugly due to the deep pattern matching.
     * A more modular optimization approach simplifies this case substantially.
     *)
    specialize (expr_case_Arr _ _ _ e1); intros;
    repeat match goal with
           | H : _ \/ _ |- _ => destruct H
           | H : exists x, _ |- _ => destruct H
           end; subst; try solve [ simpl; auto | destruct c; auto ].
    { destruct d; auto. destruct c; auto. }
    { destruct d; auto. destruct c; auto. }
    { specialize (expr_case_Arr _ _ _ x0); intros;
      repeat match goal with
             | H : _ \/ _ |- _ => destruct H
             | H : exists x, _ |- _ => destruct H
             end; subst; simpl.
      { destruct d; auto. destruct c; auto. destruct x; auto. }
      { destruct d; auto. destruct c; auto. destruct x; auto. }
      { destruct d; auto. destruct c; auto. destruct x; auto. }
      { destruct d; auto. destruct c; auto. destruct x; auto. }
      { inversion x3. subst.
        eapply K_dec with (p:=x3). eapply type_decidable.
        simpl. clear.
        refine
          match x1 as e1 in expr _ X1
                            , e2 as e2 in expr _ X2
                return match X1 as X1 , X2 as X2
                             return expr ts X1 -> expr ts X2 -> Prop
                       with
                       | Nat , Nat => fun e1 e2 =>
                         exprD
                           (match e1 with
                            | ConstNat a =>
                              match e2 with
                              | ConstNat b => fun _ : expr ts Nat => ConstNat (a + b)
                              | _ => fun e' : expr ts Nat => e'
                              end
                            | _ => fun e' : expr ts Nat => e'
                            end (App (App PlusE e1) e2)) env =
                         exprD e1 env + exprD e2 env
                       | _ , _ => fun _ _ => True
                       end e1 e2
          with
          | ConstNat _ , ConstNat _ => _
          | _ , _ => _
          end; try solve [ reflexivity | destruct c ; auto | destruct t; auto ]. } }
    { destruct d; auto. destruct c; auto. } }
Qed.

Fixpoint simplify {ts t} (e : expr ts t) : expr ts t :=
  reduce1
    match e in expr _ t return expr ts t with
    | ConstNat n => ConstNat n
    | Plus a b => Plus (simplify a) (simplify b)
    | ConstBool b => ConstBool b
    | If _ a b c => If (simplify a) (simplify b) (simplify c)
    | App _ _ f x => App (simplify f) (simplify x)
    | Abs _ _ body => Abs (simplify body)
    | Var _ v => Var v
    | PlusE => PlusE
    end.

(* For example, you should optimize (1 + (2 + 3)) to 6. *)

Eval compute in simplify (ts:=[]) (Plus (ConstNat 1) (Plus (ConstNat 2) (ConstNat 3))).

(* Hint: It will be helpful to write a separate function that
 * performs simplification and use the simplify function to
 * apply this function recursively.
 *)

(* Exercise: The dependent types tell us that [simplify] preserves
 * typedness. Can you prove that it also preserves semantic meaning.
 *)
Theorem simplify_sound : forall ts t (e : expr ts t),
    forall env, exprD (simplify e) env = exprD e env.
Proof.
  Opaque reduce1.
  induction e; simpl; intros; auto; try rewrite reduce1_sound; simpl;
  repeat match goal with
         | H : _ |- _ => rewrite H
         end; try reflexivity.
  Require Coq.Logic.FunctionalExtensionality.
  apply FunctionalExtensionality.functional_extensionality.
  auto.
  Transparent reduce1.
Qed.

(* Exercise: Enrich the type language with booleans and the
 * expression language with boolean constants and if expressions.
 * Re-do all of the above functions/proofs.
 *
 * Note: expr_dec becomes a bit more complicated especially in the
 * constant cases.
 *
 * The simplifier should do simplifications of conditionals, i.e.
 *     [If (ConstBool true) tr fa] = [tr]
 *     [If (ConstBool false) tr fa] = [fa]
 *     [If test tr tr] = [tr]
 *)
