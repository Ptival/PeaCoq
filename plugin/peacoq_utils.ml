open Constr
open Constrexpr
open Globnames
open Glob_term
open Libnames
open Notation
open Notation_term
open Ppextend

let quote_switch = false

let quote s =
  if quote_switch
  then "&quot;" ^ s ^ "&quot;"
  else "\"" ^ s ^ "\""

let new_switch = true

let mk_new s =
  if new_switch
  then "new " ^ s
  else s

let string_of_inductive (mi, i) =
  mk_new (
      "Inductive(" ^ quote(Names.MutInd.to_string mi) ^ ", " ^ string_of_int i ^ ")"
    )

let string_of_list string_of_elt l =
  "[" ^ String.concat ", " (List.map string_of_elt l) ^ "]"

let string_of_array string_of_elt a =
  "[" ^ String.concat "," (List.map string_of_elt (Array.to_list a)) ^ "]"

(** Printing [constr] **)

let string_of_instance u =
  Pp.string_of_ppcmds (Univ.Instance.pr Univ.Level.pr u)

let string_of_universe u =
  Pp.string_of_ppcmds (Univ.Universe.pr u)

let string_of_evar e = string_of_int (Evar.repr e)

let string_of_contents c =
  mk_new (
      match c with
      | Sorts.Pos -> "Pos()"
      | Sorts.Null -> "Null()"
    )

let string_of_sort s =
  mk_new (
      match s with
      | Sorts.Prop(c) -> "Prop(" ^ string_of_contents c ^ ")"
      | Sorts.Type(u) -> "Type(" ^ string_of_universe u ^ ")"
    )

let string_of_id id = Names.Id.to_string id

let string_of_constant c = Names.Constant.to_string c

let string_of_name n =
  mk_new (
      match n with
      | Names.Name.Name(id) -> "Name(" ^ quote(string_of_id id) ^ ")"
      | Names.Name.Anonymous -> "Anonymous()"
    )

let rec string_of_constr c =
  mk_new (
      begin match kind c with
            | Rel(i) -> "Rel(" ^ string_of_int i ^ ")"
            | Var(id) -> "Var(" ^ quote(string_of_id id) ^ ")"
            | Meta(i) -> "Meta(" ^ string_of_int i ^ ")"
            | Evar((ek, a)) ->
               "Evar((" ^ string_of_evar ek
               ^ ", " ^ string_of_list string_of_constr (Array.to_list a) ^ ")"
            | Sort(s) -> "Sort(" ^ string_of_sort s ^ ")"
            | Cast(_, _, _) -> "Cast"
            | Prod(n, a, b) ->
               "Prod(" ^ string_of_name n
               ^ ", " ^ string_of_constr a
               ^ ", " ^ string_of_constr b
               ^ ")"
            | Lambda(_, _, _) -> "Lambda"
            | LetIn(_, _, _, _) -> "LetIn"
            | App(c, a) ->
               "App(" ^ string_of_constr c
               ^ ", " ^ string_of_list string_of_constr (Array.to_list a) ^ ")"
            | Const((c, _)) ->
               "Const(" ^ quote(string_of_constant c) ^ ")"
            | Ind((i, _)) ->
               "Ind(" ^ string_of_inductive(i) ^ ")"
            | Construct((((m, i), j), u)) ->
               "Construct(" ^ quote(Names.MutInd.to_string m)
               ^ ", " ^ string_of_int i
               ^ ", " ^ string_of_int j ^ ")"
            | Case(_, _, _, _) -> "Case"
            | Fix(_) -> "Fix"
            | CoFix(_) -> "CoFix"
            | Proj(_, _) -> "Proj"
      end
    )

(** Printing [constr_expr] **)

let string_of_parenRelation pr =
  mk_new (
      match pr with
      | E -> "E()"
      | L -> "L()"
      | Prec n -> "Prec(" ^ string_of_int n ^ ")"
      | Any -> "Any()"
    )

let string_of_ppcut p =
  mk_new (
      match p with
      | PpBrk(a, b) -> "PpBrk(" ^ string_of_int a ^ ", " ^ string_of_int b ^ ")"
      | PpTbrk(a, b) -> "PpTBrk(" ^ string_of_int a ^ ", " ^ string_of_int b ^ ")"
      | PpTab -> "PpTab()"
      | PpFnl -> "PpFnl()"
    )


let string_of_ppbox p =
  mk_new (
      match p with
      | PpHB(a) -> "PpHB(" ^ string_of_int a ^ ")"
      | PpHOVB(a) -> "PpHOVB(" ^ string_of_int a ^ ")"
      | PpHVB(a) -> "PpHVB(" ^ string_of_int a ^ ")"
      | PpVB(a) -> "PpVB(" ^ string_of_int a ^ ")"
      | PpTB -> "PpTB()"
    )

let rec string_of_unparsing u =
  mk_new (
      match u with
      | UnpMetaVar(i, p) ->
         "UnpMetaVar(" ^ string_of_int i ^ ", " ^ string_of_parenRelation p ^ ")"
      | UnpListMetaVar(i, p, l) ->
         "UnpListMetaVar(" ^ string_of_int i ^ ", " ^ string_of_parenRelation p ^ ", "
         ^ string_of_unparsing_list l ^ ")"
      | UnpBinderListMetaVar(i, b, l) ->
         "UnpBinderListMetaVar(" ^ string_of_int i ^ ", " ^ string_of_bool b ^ ", "
         ^ string_of_unparsing_list l ^ ")"
      | UnpTerminal(s) -> "UnpTerminal(" ^ quote(s) ^ ")"
      | UnpBox(b, l) ->
         "UnpBox(" ^ string_of_ppbox b ^ ", " ^ string_of_unparsing_list l ^ ")"
      | UnpCut(c) -> "UnpCut(" ^ string_of_ppcut c ^ ")"
    )
and string_of_unparsing_list l = string_of_list string_of_unparsing l

let string_of_prim_token t =
  mk_new (
      match t with
      | Numeral(i) -> "Numeral(" ^ Bigint.to_string i ^ ")"
      | String(s) -> "PrimTokenString(" ^ quote(s) ^ ")"
    )

let string_of_binding_kind bk =
  mk_new (
      match bk with
      | Decl_kinds.Explicit -> quote("Explicit()")
      | Decl_kinds.Implicit -> quote("Implicit()")
    )

let string_of_binder_kind bk =
  mk_new (
      match bk with
      | Default(bk) -> "Default(" ^ string_of_binding_kind bk ^ ")"
      | Generalized(bk1, bk2, b) ->
         "Generalized(" ^ string_of_binding_kind bk1
         ^ ", " ^ string_of_binding_kind bk2
         ^ ", " ^ string_of_bool b ^ ")"
    )

let string_of_located string_of_x (_, x) = string_of_x x

let string_of_reference r =
  mk_new (
      match r with
      | Qualid(ql) ->
         "Qualid("
         ^ string_of_located (fun x -> quote (Libnames.string_of_qualid x)) ql
         ^ ", " ^ string_of_located
             (fun x -> quote (Pp.string_of_ppcmds (pr_qualid x))) ql
         ^ ")"
      | Ident(il) -> "Ident(" ^ string_of_located string_of_id il ^ ")"
    )

let rec string_of_constr_expr ce =
  mk_new (
      match ce with
      | CApp(_, (_, c), l) ->
         "CApp(" ^ string_of_constr_expr c
         ^ ", " ^ string_of_list string_of_constr_expr (List.map fst l)
         ^ ")"
      | CNotation(_, notation, (cel, cell, lbll)) ->
         let (unp, prec) = Notation.find_notation_printing_rule notation in
         "CNotation(" ^ quote(notation)
         ^ ", " ^ string_of_list string_of_constr_expr cel
         ^ ", " ^ string_of_list (string_of_list string_of_constr_expr) cell
         ^ ", " ^ string_of_int prec
         ^ ", " ^ string_of_unparsing_list unp
         ^ ")"
      | CPrim(_, t) -> "CPrim(" ^ string_of_prim_token t ^ ")"
      | CProdN(_, bl, c) ->
         "CProdN(" ^ string_of_list string_of_binder_expr bl
         ^ ", " ^ string_of_constr_expr c ^ ")"
      | CRef(r, _) -> "CRef(" ^ string_of_reference r ^ ")"
      | _ -> "string_of_constr_expr_TODO"
    )
    and
      string_of_binder_expr (nll, bk, c) =
      mk_new (
          "BinderExpr(" ^ string_of_list string_of_name (List.map snd nll)
          ^ ", " ^ string_of_binder_kind bk
          ^ ", " ^ string_of_constr_expr c
          ^ ")"
        )

let string_of_option string_of_elt = function
  | None -> "null"
  | Some(elt) -> string_of_elt elt

let string_of_interp_rule ir =
  mk_new (
      match ir with
      | NotationRule(scope_name_option, notation) ->
         let (unp, prec) = Notation.find_notation_printing_rule notation in
         "NotationRule("
         ^ string_of_option quote scope_name_option
         ^ ", " ^ quote(notation)
         ^ ", " ^ string_of_unparsing_list unp
         ^ ", " ^ string_of_int prec
         ^ ")"
      | SynDefRule(kernel_name) ->
         "SynDefRule(" ^ quote(Names.KerName.to_string kernel_name) ^ ")"
    )

let string_of_constructor (ind, i) =
  mk_new ("Constructor(" ^ string_of_inductive ind ^ ", " ^ string_of_int i ^ ")")

let string_of_global_reference gr =
  mk_new (
      match gr with
      | VarRef(v) -> "VarRef(" ^ string_of_id v ^ ")"
      | ConstRef(c) -> "ConstRef(" ^ quote(string_of_constant c) ^ ")"
      | IndRef(i) -> "IndRef(" ^ string_of_inductive i ^ ")"
      | ConstructRef(c) -> "ConstructRef(" ^ string_of_constructor c ^ ")"
    )

let rec string_of_notation_constr nc =
  mk_new (
      match nc with
      | NRef(gr) -> "NRef(" ^ string_of_global_reference gr ^ ")"
      | NVar(id) -> "NVar(" ^ quote(string_of_id id) ^ ")"
      | NApp(nc, ncl) ->
         "NApp(" ^ string_of_notation_constr nc
         ^ ", " ^ string_of_list string_of_notation_constr ncl ^ ")"
      | NHole(_, _, _) -> "NHole()"
      | NList (_, _, _, _, _) -> "NList()"
      | NLambda(_, _, _) -> "NLambda()"
      | NProd(name, nc1, nc2) ->
         "NProd(" ^ string_of_name name
         ^ ", " ^ string_of_notation_constr nc1
         ^ ", " ^ string_of_notation_constr nc2 ^ ")"
      | NBinderList(_, _, _, _) -> "NBinderList()"
      | NLetIn(_, _, _) -> "NLetIn()"
      | NCases(_, _, _, _) -> "NCases()"
      | NLetTuple(_, _, _, _) -> "NLetTuple()"
      | NIf(_, _, _, _) -> "NIf()"
      | NRec(_, _, _, _, _) -> "NRec()"
      | NSort(_) -> "NSort()"
      | NPatVar(_) -> "NPatVar()"
      | NCast(_, _) -> "NCast()"
    )

let string_of_subscopes (so, sl) =
  "[" ^ string_of_option quote so ^ ", " ^ string_of_list quote sl ^ "]"

let string_of_notation_var_instance_type nvit =
  mk_new (
      match nvit with
      | NtnTypeConstr -> "NtnTypeConstr()"
      | NtnTypeConstrList -> "NtnTypeConstrList()"
      | NtnTypeBinderList -> "NtnTypeBinderList()"
    )

let string_of_interpretation (l, notation_constr) =
  mk_new (
      "Interpretation("
      ^ string_of_list
          (fun (id, (subscopes, nvit)) ->
           "[" ^ quote (string_of_id id)
           ^ ", " ^ string_of_subscopes subscopes
           ^ ", " ^ string_of_notation_var_instance_type nvit
           ^ "]"
          ) l
      ^ ", " ^ string_of_notation_constr notation_constr ^ ")"
    )

let string_of_loc loc =
  let (start, stop) = Loc.unloc loc in
  mk_new ("Loc(" ^ string_of_int start ^ ", " ^ string_of_int stop ^ ")")

let string_of_glob_level l = "TODO"

let rec string_of_glob_constr gc =
  mk_new (
      match gc with
      | GRef(_, gr, gllo) ->
         "GRef(" ^ string_of_global_reference gr
         ^ ", " ^ string_of_option (string_of_list string_of_glob_level) gllo ^ ")"
      | GVar(_, id) -> "GVar(" ^ quote(string_of_id id) ^ ")"
      | GEvar(_, _, _) -> "GEvar(TODO)"
      | GPatVar(_, _) -> "GPatVar(TODO)"
      | GApp(_, gc, gcl) ->
         "GApp(" ^ string_of_glob_constr gc
         ^ ", " ^ string_of_list string_of_glob_constr gcl ^ ")"
      | GLambda(_, _, _, _, _) -> "GLambda(TODO)"
      | GProd(_, name, _, gc1, gc2) ->
         "GProd(" ^ string_of_name name
         ^ ", " ^ string_of_glob_constr gc1
         ^ ", " ^ string_of_glob_constr gc2 ^ ")"
      | GLetIn(_, _, _, _) -> "GLetIn(TODO)"
      | GCases(_, _, _, _, _) -> "GCases(TODO)"
      | GLetTuple(_, _, _, _, _) -> "GLetTuple(TODO)"
      | GIf(_, _, _, _, _) -> "GIf(TODO)"
      | GRec(_, _, _, _, _, _) -> "GRec(TODO)"
      | GSort(_, _) -> "GSort(TODO)"
      | GHole(_, _, _, _) -> "GHole(TODO)"
      | GCast(_, _, _) -> "GCast(TODO)"
    )

let map_option f = function
  | None -> None
  | Some(x) -> Some(f x)

let flatten_options = function
  | None -> None
  | Some(None) -> None
  | Some(Some(x)) -> Some(x)

(* map_may_fail : ('a -> 'b option) -> 'a list -> 'b list option *)
let map_may_fail f l =
  map_option List.rev
    (List.fold_left
       (fun acc elt ->
        flatten_options (
            map_option
              (fun acc -> map_option (fun felt -> felt :: acc) (f elt))
              acc
          )
       )
       (Some [])
       l
    )

(* : ('a -> 'b list option) -> 'a list -> 'b list option *)
let concatmap_may_fail f l =
  map_option List.flatten (map_may_fail f l)

(*
Given a (glob_constr, notation_constr) pair, figure out whether they match.
[None] is returned if they do not match, [Some(l)] is returned if they match,
where [l] is a list of (glob_constr, notation_constr) to be recursively
matched against each other.
 *)
let rec match_gn
        : ((glob_constr * notation_constr) as 'p) ->
          'p list option
  = function
  | GApp(_, gc, gcl), NApp(nc, ncl) ->
     begin match match_gn (gc, nc) with
     | None -> None
     | Some(_) -> concatmap_may_fail match_gn (List.combine gcl ncl)
     end
  | GRef(_, gr, _), NRef(gr') ->
     if Globnames.eq_gr gr gr' then Some([]) else None
  | GHole(_, ek, ipne, ggao), NHole(ek', ipne', ggao') ->
     (* TODO: check equality *)
     Some([])
  | _, NVar(_) as gcnc -> Some([gcnc])
  | g, n ->
     print_string "match_gn failed to unify:";
     print_newline ();
     print_string (string_of_glob_constr g);
     print_newline ();
     print_string (string_of_notation_constr n);
     print_newline ();
     None

let rec find_matching_notation glob_constr
        : notation_rule list ->
          (notation_rule * ((glob_constr * notation_constr) list)) option
  = function
  | [] -> None
  | ((_, (_, notation_constr), _) as rule) :: rest ->
     begin
       match match_gn (glob_constr, notation_constr) with
       | None -> find_matching_notation glob_constr rest
       | Some(submatches) ->
          Some((rule, submatches))
     end

       (*
let rec find_matching_notations glob_constr
        : ((notation_rule * 'a list) as 'a) option
  =
  let candidates = Notation.uninterp_notations glob_constr in
  match find_matching_notation glob_constr candidates with
  | None -> None
  | Some((rule, submatches)) ->
     begin match map_may_fail find_matching_notations submatches with
           | None -> None
           | Some(submatches') ->
              Some((rule, submatches'))
     end
        *)

(* pretty much glob_constr, but extensible and with only the information we want *)
type 'a preterm =
  | Ref      of 'a * global_reference * reference * Names.Id.t
  | Var      of 'a * Names.Id.t
  | Evar     of 'a
  | PatVar   of 'a
  | App      of 'a * 'a preterm * ('a preterm) list
  | Lambda   of 'a
  | Prod     of 'a * 'a preterm * 'a preterm
  | LetIn    of 'a
  | Cases    of 'a
  | LetTuple of 'a
  | If       of 'a
  | Rec      of 'a
  | Sort     of 'a
  | Hole     of 'a
  | Cast     of 'a
  (* Prim is like CPrim in constr_expr, shorter for the UI to deal with *)
  | Prim     of 'a * Constrexpr.prim_token

let mk_Ref (a, gr) =
  let name = Nametab.basename_of_global gr in
  let reference = Constrextern.extern_reference Loc.ghost Names.Id.Set.empty gr in
  Ref(a, gr, reference, name)

let rec string_of_preterm sa pt =
  mk_new (
      match pt with
      | Ref(a, gr, reference, name) ->
         "Ref(" ^ sa a
         ^ ", " ^ string_of_global_reference gr
         ^ ", " ^ string_of_reference reference
         ^ ", " ^ quote(string_of_id name)
         ^ ")"
      | Var(a, id) -> "Var(" ^ sa a ^ ", " ^ quote(string_of_id id) ^ ")"
      | Evar(a) -> "Evar(" ^ sa a ^ ")"
      | PatVar(a) -> "PatVar(" ^ sa a ^ ")"
      | App(a, t, tl) ->
         "App(" ^ sa a
         ^ ", " ^ string_of_preterm sa t
         ^ ", " ^ string_of_list (string_of_preterm sa) tl
         ^ ")"
      | Lambda(a) -> "Lambda(" ^ sa a ^ ")"
      | Prod(a, t1, t2) ->
         "Prod(" ^ sa a
         ^ ", " ^ string_of_preterm sa t1
         ^ ", " ^ string_of_preterm sa t2
         ^ ")"
      | LetIn(a) -> "LetIn(" ^ sa a ^ ")"
      | Cases(a) -> "Cases(" ^ sa a ^ ")"
      | LetTuple(a) -> "LetTuple(" ^ sa a ^ ")"
      | If(a) -> "If(" ^ sa a ^ ")"
      | Rec(a) -> "Rec(" ^ sa a ^ ")"
      | Sort(a) -> "Sort(" ^ sa a ^ ")"
      | Hole(a) -> "Hole(" ^ sa a ^ ")"
      | Cast(a) -> "Cast(" ^ sa a ^ ")"
      | Prim(a, t) ->
         "Prim(" ^ sa a
         ^ ", " ^ string_of_prim_token t
         ^ ")"
    )

type notation_marker =
  (* constr_notation_substitution =
    constr_expr list *      (** for constr subterms *)
    constr_expr list list * (** for recursive notations *)
    local_binder list list (** for binders subexpressions *)
   *)
  | NotationRoot of notation_rule * Constrexpr.constr_notation_substitution
  | NotationPiece
  | NotNotation

let string_of_notation_rule (interp_rule, interpretation, intoption) =
  mk_new (
      "Notation_Rule(" ^ string_of_interp_rule interp_rule
      ^ ", " ^ string_of_interpretation interpretation
      ^ ", " ^ string_of_option string_of_int intoption
      ^ ")"
    )

type term = notation_marker preterm

let rec first_some = function
  | [] -> None
  | None :: t -> first_some t
  | Some(x) :: _ -> Some(x)

(* I guess in the absence of laziness... *)
let rec first_some_map f = function
  | [] -> None
  | h :: t ->
     begin
       match f h with
       | None -> first_some_map f t
       | Some(fh) -> Some((h, fh))
     end

(*
notation_rule = interp_rule * interpretation * int option
interp_rule = | NotationRule of scope_name option * notation
              | SynDefRule of kernel_name
interpretation = (Id.t * (subscopes * notation_var_instance_type)) list * notation_constr
 *)

(*
let rec mk_term glob_constr : term =
  let candidate_rules = Notation.uninterp_notations glob_constr in
  let candidate_constrs = List.map (fun ((_, (_, c), _) as n) -> (n, c)) candidate_rules in
  match first_some_map (fun (n, c) -> try_unify ~root:(Some(n)) (glob_constr, c)) candidate_constrs with
  | Some((notation, term)) -> term
  | None -> skip_unify glob_constr

and notation root =
  match root with
  | None -> NotationPiece
  | Some(notation) -> NotationRoot(notation)

and try_unify ?root:(root=None) : (glob_constr * notation_constr) -> term option = function
  | GApp(_, gc, gcl), NApp(nc, ncl) ->
     begin
       let match_function = try_unify (gc, nc) in
       let match_arguments = map_may_fail try_unify (List.combine gcl ncl) in
       match match_function, match_arguments with
       | Some(f), Some(args) -> Some(App(notation root, f, args))
       | _, _ -> None
     end
  | GRef(_, gr, _), NRef(gr') ->
     if Globnames.eq_gr gr gr'
     then
       Some(mk_Ref(NotationPiece, gr))
     else None
  | GHole(_, ek, ipne, ggao), NHole(ek', ipne', ggao') ->
     (* TODO: check equality of some arguments? *)
     Some(Hole(NotationPiece))
  | GProd(_, n, bk, gc1, gc2), NProd(n', nc1, nc2) ->
     if Names.Name.equal n n'
     then
       let match1 = try_unify (gc1, nc1) in
       let match2 = try_unify (gc2, nc2) in
       match match1, match2 with
       | Some(t1), Some(t2) -> Some(Prod(notation root, t1, t2))
       | _, _ -> None
     else None
  | gc, NVar(_) ->
     Some(mk_term gc)

  (* these ones occur often *)
  | GVar(_), nc -> None
  | GApp(_), NProd(_) -> None

  | g, n ->
     print_string "\nFailed to unify:";
     print_newline ();
     print_string ("glob_constr:     " ^ string_of_glob_constr g);
     print_newline ();
     print_string ("notation_constr: " ^ string_of_notation_constr n);
     print_newline ();
     print_newline ();
     None

and skip_unify = function
  | GRef(_, gr, _) -> mk_Ref(NotNotation, gr)
  | GVar(_, id) -> Var(NotNotation, id)
  | GEvar(_, _, _) -> Evar(NotNotation)
  | GPatVar(_, _) -> PatVar(NotNotation)
  | GApp(_, gc, gcl) -> App(NotNotation, mk_term gc, List.map mk_term gcl)
  | GLambda(_, _, _, _, _) -> Lambda(NotNotation)
  | GProd(_, _, _, gc1, gc2) -> Prod(NotNotation, mk_term gc1, mk_term gc2)
  | GLetIn(_, _, _, _) -> LetIn(NotNotation)
  | GCases(_, _, _, _, _) -> Cases(NotNotation)
  | GLetTuple(_, _, _, _, _) -> LetTuple(NotNotation)
  | GIf(_, _, _, _, _) -> If(NotNotation)
  | GRec(_, _, _, _, _, _) -> Rec(NotNotation)
  | GSort(_, _) -> Sort(NotNotation)
  | GHole(_) -> Hole(NotNotation)
  | GCast(_, _, _) -> Cast(NotNotation)
 *)

let default_env () = {
  Notation_term.ninterp_var_type = Names.Id.Map.empty;
  ninterp_rec_vars = Names.Id.Map.empty;
  ninterp_only_parse = false;
}

let natInd = "Coq.Init.Datatypes.nat"

let isZero = function
  | GRef(_, (ConstructRef(((mutind, 0), 1)) as zero), _) ->
     if Names.MutInd.to_string mutind = natInd
     then Some(zero)
     else None
  | _ -> None

let isSuccOf = function
  | GApp(_, GRef(_, (ConstructRef(((mutind, 0), 2)) as s), _), [pred]) ->
     if Names.MutInd.to_string mutind = natInd then Some(s, pred) else None
  | _ -> None

let rec mkNat (n: Bigint.bigint) glob_constr: term =
  if Bigint.is_strictly_pos n
  then
    match isSuccOf glob_constr with
    | Some(s, pred) ->
       let pred = mkNat Bigint.(sub n one) pred in
       App(NotationPiece, mk_Ref(NotationPiece, s), [pred])
    | None -> failwith "mkNat succ"
  else
    match isZero glob_constr with
    | Some(zero) -> mk_Ref(NotationPiece, zero)
    | None -> failwith "mkNat zero"

let rec mk_term env (glob_constr, constr_expr): term =
  match constr_expr with
  | CNotation(_, notation, subst) ->
     let notation_constr =
       Notation_ops.notation_constr_of_glob_constr (default_env ()) glob_constr
     in
     let candidate_rules = Notation.uninterp_notations glob_constr in
     let correct_rule =
       List.find
         (fun (ir, _, _) ->
          match ir with
          | NotationRule(_, n) -> notation = n
          | _ -> false
         )
         candidate_rules
     in
     begin
       let term_option =
         mk_notation ~root:(Some(correct_rule, subst)) (glob_constr, notation_constr)
       in
       match term_option with
       | None -> failwith "mk_notation failed"
       | Some(term) -> term
     end
  | _ ->
     begin
       match glob_constr, constr_expr with
       | GRef(_, gr, _), _ ->
          mk_Ref(NotNotation, gr)
       | GVar(_, id), _ ->
          Var(NotNotation, id)
       | GEvar(_, _, _), _ ->
          Evar(NotNotation)
       | GPatVar(_, _), _ ->
          PatVar(NotNotation)
       | GApp(_, gc, gcl), CApp(_, (_, ce), cel) ->
          let cel = List.map (fun (c, _) -> c) cel in
          App(NotNotation, mk_term env (gc, ce), List.map (mk_term env) (List.combine gcl cel))
       | GLambda(_, _, _, _, _), _ ->
          Lambda(NotNotation)
       | GProd(_, _, _, gc1, gc2), CProdN(loc, bel, ce2) ->
          begin
            match bel with
            | [] -> mk_term env (glob_constr, ce2)
            | (_, _, ce1) :: bel ->
               Prod(NotNotation,
                    mk_term env (gc1, ce1),
                    mk_term env (gc2, CProdN(loc, bel, ce2)))
          end
       | GLetIn(_, _, _, _), _ ->
          LetIn(NotNotation)
       | GCases(_, _, _, _, _), _ ->
          Cases(NotNotation)
       | GLetTuple(_, _, _, _, _), _ ->
          LetTuple(NotNotation)
       | GIf(_, _, _, _, _), _ ->
          If(NotNotation)
       | GRec(_, _, _, _, _, _), _ ->
          Rec(NotNotation)
       | GSort(_, _), _ ->
          Sort(NotNotation)
       | GHole(_), _ ->
          Hole(NotNotation)
       | GCast(_, _, _), _ ->
          Cast(NotNotation)
       | g, CPrim(_, (Numeral(bi) as n)) ->
          (* here, g is supposed to match the Peano number n *)
          (* this will raise an exception if g does not correspond to expectations *)
          let _ = mkNat bi g in
          Prim(NotNotation, n)
       | _, _ ->
          failwith (
              "OOPS" ^ string_of_glob_constr glob_constr
              ^ ", " ^ string_of_constr_expr constr_expr
            )
     end

and notation root =
  match root with
  | None -> NotationPiece
  | Some(notation, subst) -> NotationRoot(notation, subst)

and mk_notation ?root:(root=None) (glob_constr, notation_constr): term option =
  match (glob_constr, notation_constr) with
  | GApp(_, gc, gcl), NApp(nc, ncl) ->
     begin
       let match_function = mk_notation (gc, nc) in
       let match_arguments = map_may_fail mk_notation (List.combine gcl ncl) in
       match match_function, match_arguments with
       | Some(f), Some(args) -> Some(App(notation root, f, args))
       | _, _ -> None
     end
  | GRef(_, gr, _), NRef(gr') ->
     if Globnames.eq_gr gr gr'
     then
       Some(mk_Ref(NotationPiece, gr))
     else None
  | GHole(_, ek, ipne, ggao), NHole(ek', ipne', ggao') ->
     (* TODO: check equality of some arguments? *)
     Some(Hole(NotationPiece))
  | GProd(_, n, bk, gc1, gc2), NProd(n', nc1, nc2) ->
     if Names.Name.equal n n'
     then
       let match1 = mk_notation (gc1, nc1) in
       let match2 = mk_notation (gc2, nc2) in
       match match1, match2 with
       | Some(t1), Some(t2) -> Some(Prod(notation root, t1, t2))
       | _, _ -> None
     else None
  | gc, NVar(_) ->
     None
  | _, _ -> failwith "TODO"

and string_of_term env = string_of_preterm (string_of_notation_marker env)

and string_of_constr_expr' env constr_expr =
  let glob_constr = Constrintern.intern_constr env constr_expr in
  string_of_term env (mk_term env (glob_constr, constr_expr))

and string_of_local_binder (env: Environ.env) lb =
  let s = string_of_constr_expr' env in
  mk_new (
      match lb with
      | LocalRawDef(ln, ce) ->
         "LocalRawDef(" ^ string_of_located string_of_name ln
         ^ ", " ^ s ce
         ^ ")"
      | LocalRawAssum(lnl, bk, ce) ->
         "LocalRawAssum(" ^ string_of_list (string_of_located string_of_name) lnl
         ^ ", " ^ string_of_binder_kind bk
         ^ ", " ^ s ce
         ^ ")"
    )

and string_of_subst env ((cel, cell, lbll) as subst) =
  let s = string_of_constr_expr' env in
  mk_new (
      "Substitutions(" ^ string_of_list s cel
      ^ ", " ^ string_of_list (string_of_list s) cell
      ^ ", " ^ string_of_list (string_of_list (string_of_local_binder env)) lbll
      ^ ")"
    )

and string_of_notation_marker env nm =
  mk_new (
      match nm with
      | NotationRoot(s, subst) ->
         "NotationRoot(" ^ string_of_notation_rule s
         ^ ", " ^ string_of_subst env subst
         ^ ")"
      | NotationPiece -> "NotationPiece()"
      | NotNotation -> "NotNotation()"
    )
