open Constr
open Constrexpr
open Decl_kinds
open Globnames
open Glob_term
open Libnames
open Misctypes
open Notation
open Notation_term
open Ppextend
open Proof

let quote_switch = false

let escape_backslash s =
  (* "\\\\\\\\" indeed produces two backslashes! *)
  Str.global_replace (Str.regexp "\\") "\\\\\\\\" s

let quote s =
  if quote_switch
  then "&quot;" ^ escape_backslash s ^ "&quot;"
  else "\"" ^  escape_backslash s ^ "\""

let new_switch = true

let string_of_list string_of_elt l =
  "[" ^ String.concat "," (List.map string_of_elt l) ^ "]"

let string_of_string_list l = string_of_list (fun s -> s) l

let string_of_object fields =
  "{"
  ^ String.concat "," (List.map (fun (f, v) -> "\"" ^ f ^ "\":" ^ v) fields)
  ^ "}"

let mk_new (name, args) =
  string_of_object
    [ ("constructorName", quote(name))
    ; ("constructorArgs", string_of_string_list args)
    ]

let string_of_option string_of_elt o =
  mk_new (
      match o with
      | None      -> ("nothing", [])
      | Some(elt) -> ("just", [string_of_elt elt])
    )

let string_of_pair string_of_a string_of_b (a, b) =
  string_of_string_list [string_of_a a; string_of_b b]

let string_of_inductive (mi, i) =
  mk_new (
      "Inductive",
      [ quote(Names.MutInd.to_string mi)
      ; string_of_int i
      ]
    )

let string_of_array string_of_elt a =
  string_of_string_list (List.map string_of_elt (Array.to_list a))

(** Printing [constr] **)

let string_of_instance u =
  Pp.string_of_ppcmds (Univ.Instance.pr Univ.Level.pr u)

let string_of_universe u =
  Pp.string_of_ppcmds (Univ.Universe.pr u)

let string_of_evar e = string_of_int (Evar.repr e)

let string_of_contents c =
  mk_new (
      match c with
      | Sorts.Pos -> ("Pos", [])
      | Sorts.Null -> ("Null", [])
    )

let string_of_sort s =
  mk_new (
      match s with
      | Sorts.Prop(c) -> ("Prop", [string_of_contents c])
      | Sorts.Type(u) -> ("Type", [string_of_universe u])
    )

let string_of_id id = quote(Names.Id.to_string id)

let string_of_constant c = Names.Constant.to_string c

let string_of_name n =
  mk_new (
      match n with
      | Names.Name.Name(id) -> ("Name", [string_of_id id])
      | Names.Name.Anonymous -> ("Anonymous", [])
    )

let rec string_of_constr c =
  mk_new (
      match kind c with
      | Rel(i) -> ("Rel", [string_of_int i])
      | Var(id) -> ("Var", [string_of_id id])
      | Meta(i) -> ("Meta", [string_of_int i])
      | Evar((ek, a)) ->
         ("Evar",
          [ string_of_evar ek
          ; string_of_list string_of_constr (Array.to_list a)
          ])
      | Sort(s) -> ("Sort", [string_of_sort s])
      | Cast(_, _, _) -> ("Cast", [])
      | Prod(n, a, b) ->
         ("Prod",
          [ string_of_name n
          ; string_of_constr a
          ; string_of_constr b
          ])
      | Lambda(_, _, _) -> ("Lambda", [])
      | LetIn(_, _, _, _) -> ("LetIn", [])
      | App(c, a) ->
         ("App",
          [ string_of_constr c
          ; string_of_list string_of_constr (Array.to_list a)
          ])
      | Const((c, _)) -> ("Const", [quote(string_of_constant c)])
      | Ind((i, _)) -> ("Ind", [string_of_inductive(i)])
      | Construct((((m, i), j), u)) ->
         ("Construct",
          [ quote(Names.MutInd.to_string m)
          ; string_of_int i
          ; string_of_int j
          ])
      | Case(_, _, _, _) -> ("Case", [])
      | Fix(_) -> ("Fix", [])
      | CoFix(_) -> ("CoFix", [])
      | Proj(_, _) -> ("Proj", [])
    )

(** Printing [constr_expr] **)

let string_of_parenRelation pr =
  mk_new (
      match pr with
      | E -> ("E", [])
      | L -> ("L", [])
      | Prec n -> ("Prec", [string_of_int n])
      | Any -> ("Any", [])
    )

let string_of_ppcut p =
  mk_new (
      match p with
      | PpBrk(a, b) -> ("PpBrk", [string_of_int a; string_of_int b])
      | PpTbrk(a, b) -> ("PpTBrk", [string_of_int a; string_of_int b])
      | PpTab -> ("PpTab", [])
      | PpFnl -> ("PpFnl", [])
    )

let string_of_ppbox p =
  mk_new (
      match p with
      | PpHB(a) -> ("PpHB", [string_of_int a])
      | PpHOVB(a) -> ("PpHoVB", [string_of_int a])
      | PpHVB(a) -> ("PpHVB", [string_of_int a])
      | PpVB(a) -> ("PpVB", [string_of_int a])
      | PpTB -> ("PpTB", [])
    )

let rec string_of_unparsing u =
  mk_new (
      match u with
      | UnpMetaVar(i, p) ->
         ("UnpMetaVar",
          [ string_of_int i
          ; string_of_parenRelation p
          ])
      | UnpListMetaVar(i, p, l) ->
         ("UnpListMetaVar",
          [ string_of_int i
          ; string_of_parenRelation p
          ; string_of_unparsing_list l
          ])
      | UnpBinderListMetaVar(i, b, l) ->
         ("UnpBinderListMetaVar",
          [ string_of_int i
          ; string_of_bool b
          ; string_of_unparsing_list l
          ])
      | UnpTerminal(s) -> ("UnpTerminal", [quote(s)])
      | UnpBox(b, l) ->
         ("UnpBox",
          [ string_of_ppbox b
          ; string_of_unparsing_list l
          ])
      | UnpCut(c) ->
         ("UnpCut", [ string_of_ppcut c ])
    )

and string_of_unparsing_list l = string_of_list string_of_unparsing l

let string_of_prim_token t =
  mk_new (
      match t with
      | Numeral(i) -> ("Numeral", [Bigint.to_string i])
      | String(s) -> ("PrimTokenString", [quote(s)])
    )

let string_of_binding_kind bk =
  mk_new (
      match bk with
      | Decl_kinds.Explicit -> ("Explicit", [])
      | Decl_kinds.Implicit -> ("Implicit", [])
    )

let string_of_binder_kind bk =
  mk_new (
      match bk with
      | Default(bk) -> ("Default", [string_of_binding_kind bk])
      | Generalized(bk1, bk2, b) ->
         ("Generalized",
          [ string_of_binding_kind bk1
          ; string_of_binding_kind bk2
          ; string_of_bool b
          ])
    )

let string_of_location loc =
  let (start, stop) = Loc.unloc loc in
  string_of_string_list
    [ string_of_int start
    ; string_of_int stop
    ]

let string_of_located string_of_x (loc, x) =
  string_of_string_list
    [ string_of_location loc
    ; string_of_x x
    ]

let string_of_module_ident = string_of_id

let string_of_dirpath p =
  string_of_list string_of_module_ident (Names.DirPath.repr p)

let string_of_qualid q =
  let (path, id) = Libnames.repr_qualid q in
  string_of_string_list
    [ string_of_dirpath path
    ; string_of_id id
    ]

let string_of_reference r =
  mk_new (
      match r with
      | Qualid(ql) -> ("Qualid", [string_of_located string_of_qualid ql])
      | Ident(il) -> ("Ident", [string_of_located string_of_id il])
    )

let string_of_glob_sort_gen string_of_x gs =
  mk_new (
      match gs with
      | GProp -> ("GProp", [])
      | GSet -> ("GSet", [])
      | GType(x) -> ("GType", [string_of_x x])
    )

let string_of_sort_info = string_of_list (string_of_located (fun s -> s))

let string_of_glob_sort gs = string_of_glob_sort_gen string_of_sort_info gs

let string_of_level_info = string_of_option (string_of_located (fun s -> s))

let string_of_glob_level = string_of_glob_sort_gen string_of_level_info

let string_of_instance_expr = string_of_list string_of_glob_level

let string_of_explicitation e =
  mk_new (
      match e with
      | ExplByPos(n, ido) ->
         ("ExplByPos",
          [ string_of_int n
          ; string_of_option string_of_id ido
          ])
      | ExplByName(name) ->
         ("ExplByName", [string_of_id name])
    )

let string_of_proj_flag = string_of_option string_of_int

let string_of_case_style cs =
  mk_new (
      match cs with
      | LetStyle -> ("LetStyle", [])
      | IfStyle -> ("IfStyle", [])
      | LetPatternStyle -> ("LetPatternStyle", [])
      | MatchStyle -> ("MatchStyle", [])
      | RegularStyle -> ("RegularStyle", [])
    )

let rec string_of_cases_pattern_expr e =
  mk_new (
      match e with
      | CPatAlias(_) -> ("TODO_CPatAlias", [])
      | CPatCstr(loc, r, cl1, cl2) ->
         ("CPatCstr",
          [ string_of_location loc
          ; string_of_reference r
          ; string_of_list string_of_cases_pattern_expr cl1
          ; string_of_list string_of_cases_pattern_expr cl2
          ])
      | CPatAtom(loc, ro) ->
         ("CPatAtom",
          [ string_of_location loc
          ; string_of_option string_of_reference ro
          ])
      | CPatOr(_) -> ("TODO_CPatOr", [])
      | CPatNotation(loc, n, cpns, cpel) ->
         let (unp, prec) =
           begin
             match n with
             | "( _ )" -> ([], 0)
             | _       -> Notation.find_notation_printing_rule n
           end
         in
         ("CPatNotation",
          [ string_of_location loc
          ; quote n
          ; string_of_pair
              (string_of_list string_of_cases_pattern_expr)
              (string_of_list (string_of_list string_of_cases_pattern_expr))
              cpns
          ; string_of_list string_of_cases_pattern_expr cpel
          (* added for PeaCoq *)
          ; string_of_int prec
          ; string_of_unparsing_list unp
          ])
      | CPatPrim(loc, tok) ->
         ("CPatPrim",
          [ string_of_location loc
          ; string_of_prim_token tok
          ])
      | CPatRecord(_) -> ("TODO_CPatRecord", [])
      | CPatDelimiters(loc, s, cases) ->
         ("CPatDelimiters",
          [ string_of_location loc
          ; quote(s)
          ; string_of_cases_pattern_expr cases
          ])
    )

let string_of_constructor (ind, i) =
  mk_new ("Constructor", [string_of_inductive ind; string_of_int i])

let string_of_global_reference gr =
  mk_new (
      match gr with
      | VarRef(v) -> ("VarRef", [string_of_id v])
      | ConstRef(c) -> ("ConstRef", [quote(string_of_constant c)])
      | IndRef(i) -> ("IndRef", [string_of_inductive i])
      | ConstructRef(c) -> ("ConstructRef", [string_of_constructor c])
    )

let rec string_of_glob_constr gc =
  mk_new (
      match gc with
      | GRef(_, gr, gllo) ->
         ("GRef",
          [ string_of_global_reference gr
          ; string_of_option (string_of_list string_of_glob_level) gllo
          ])
      | GVar(_, id) -> ("GVar", [string_of_id id])
      | GEvar(_, _, _) -> ("GEvarTODO", [])
      | GPatVar(_, _) -> ("GPatVarTODO", [])
      | GApp(_, gc, gcl) ->
         ("GApp",
          [ string_of_glob_constr gc
          ; string_of_list string_of_glob_constr gcl
          ])
      | GLambda(_, _, _, _, _) -> ("GLambdaTODO", [])
      | GProd(_, name, _, gc1, gc2) ->
         ("GProd",
          [ string_of_name name
          ; string_of_glob_constr gc1
          ; string_of_glob_constr gc2
          ])
      | GLetIn(_, _, _, _) -> ("GLetInTODO", [])
      | GCases(_, _, _, _, _) -> ("GCasesTODO", [])
      | GLetTuple(_, _, _, _, _) -> ("GLetTupleTODO", [])
      | GIf(_, _, _, _, _) -> ("GIfTODO", [])
      | GRec(_, _, _, _, _, _) -> ("GRecTODO", [])
      | GSort(_, gs) -> ("GSort", [string_of_glob_sort gs])
      | GHole(_, _, _, _) -> ("GHoleTODO", [])
      | GCast(_, _, _) -> ("GCastTODO", [])
    )

let default_env () = {
  Notation_term.ninterp_var_type = Names.Id.Map.empty;
  ninterp_rec_vars = Names.Id.Map.empty;
  ninterp_only_parse = false;
}

let rec string_of_constr_expr ce =
  mk_new (
      match ce with

      | CApp(loc, (pf, ce), l) ->
         ("CApp",
          [ string_of_location loc
          ; string_of_string_list
              [ string_of_proj_flag pf
              ; string_of_constr_expr ce
              ]
          ; string_of_list
              (fun (ce, elo) ->
                string_of_string_list
                  [ string_of_constr_expr ce
                  ; string_of_option
                      (string_of_located string_of_explicitation)
                      elo
                  ]
              )
              l
          ])

      | CNotation(loc, notation, cns) ->
         let (unp, prec) =
           begin
             match notation with
             | "( _ )" -> ([], 0)
             | _       -> Notation.find_notation_printing_rule notation
           end
         in
         ("CNotation",
          [ string_of_location loc
          ; quote notation
          ; string_of_constr_notation_substitution cns
            (* added for PeaCoq *)
          ; string_of_int prec
          ; string_of_unparsing_list unp
          ])

      | CPrim(loc, t) ->
         ("CPrim",
          [ string_of_location loc
          ; string_of_prim_token t
          ])

      | CProdN(loc, bl, c) ->
         ("CProdN",
          [ string_of_location loc
          ; string_of_list string_of_binder_expr bl
          ; string_of_constr_expr c
          ])

      | CRef(r, us) ->
         ("CRef",
          [ string_of_reference r
          ; string_of_option string_of_instance_expr us
          ])

      | CSort(loc, gs) ->
         ("CSort",
          [ string_of_location loc
          ; string_of_glob_sort gs
          ])

      | CFix(_) -> ("TODO_CFix", [])

      | CCoFix(_) -> ("TODO_CCoFix", [])

      | CLambdaN(loc, bel, ce) ->
         ("CLambdaN",
          [ string_of_location loc
          ; string_of_list string_of_binder_expr bel
          ; string_of_constr_expr ce
          ])

      | CLetIn(loc, lname, ce1, ce2) ->
         ("CLetIn",
          [ string_of_location loc
          ; string_of_located string_of_name lname
          ; string_of_constr_expr ce1
          ; string_of_constr_expr ce2
          ])

      | CAppExpl(_) -> ("TODO_CAppExpl", [])

      | CRecord(_) -> ("TODO_CRecord", [])

      | CCases(loc, style, ceo, casel, branchl) ->
         ("CCases",
          [ string_of_location loc
          ; string_of_case_style style
          ; string_of_option string_of_constr_expr ceo
          ; string_of_list string_of_case_expr casel
          ; string_of_list string_of_branch_expr branchl
          ])

      | CLetTuple(loc, nll, (nlo, ceo), ce1, ce2) ->
         ("CLetTuple",
          [ string_of_location loc
          ; string_of_list (string_of_located string_of_name) nll
          ; string_of_option (string_of_located string_of_name) nlo
          ; string_of_option string_of_constr_expr ceo
          ; string_of_constr_expr ce1
          ; string_of_constr_expr ce2
          ])

      | CIf(_) -> ("TODO_CIf", [])

      | CHole(_) -> ("TODO_CHole", [])

      | CPatVar(_) -> ("TODO_CPatVar", [])

      | CEvar(_) -> ("TODO_CEvar", [])

      | CCast(_) -> ("TODO_CCast", [])

      | CGeneralization(_) -> ("TODO_CGeneralization", [])

      | CDelimiters(loc, s, ce) ->
         ("CDelimiters",
          [ string_of_location loc
          ; quote(s)
          ; string_of_constr_expr ce
          ])

    )

and string_of_binder_expr (nll, bk, c) =
  string_of_string_list
    [ string_of_list (string_of_located string_of_name) nll
    ; string_of_binder_kind bk
    ; string_of_constr_expr c
    ]

and string_of_constr_notation_substitution (cel, cell, lbll) =
  string_of_string_list
    [ string_of_list string_of_constr_expr cel
    ; string_of_list (string_of_list string_of_constr_expr) cell
    ; string_of_list (string_of_list string_of_local_binder) lbll
    ]

and string_of_local_binder lb =
  let s = string_of_constr_expr in
  mk_new (
      match lb with

      | LocalRawDef(ln, ce) ->
         ("LocalRawDef",
          [ string_of_located string_of_name ln
          ; s ce
          ])

      | LocalRawAssum(lnl, bk, ce) ->
         ("LocalRawAssum",
            [ string_of_list (string_of_located string_of_name) lnl
            ; string_of_binder_kind bk
            ; s ce
            ])

    )

and string_of_case_expr (ce, (nlo, cpeo)) =
  string_of_string_list
    [ string_of_constr_expr ce
    ; string_of_string_list
        [ string_of_option (string_of_located string_of_name) nlo
        ; string_of_option string_of_cases_pattern_expr cpeo
        ]
    ]

and string_of_branch_expr (loc, cpelll, ce) =
  string_of_string_list
    [ string_of_location loc
    ; string_of_list
        (string_of_located (string_of_list string_of_cases_pattern_expr))
        cpelll
    ; string_of_constr_expr ce
    ]

let string_of_interp_rule ir =
  mk_new (
      match ir with

      | NotationRule(scope_name_option, notation) ->
         let (unp, prec) = Notation.find_notation_printing_rule notation in
         ("NotationRule",
          [ string_of_option quote scope_name_option
          ; quote(notation)
          ; string_of_unparsing_list unp
          ; string_of_int prec
          ])

      | SynDefRule(kernel_name) ->
         ("SynDefRule",
          [quote(Names.KerName.to_string kernel_name)])

    )

let rec string_of_notation_constr nc =
  mk_new (
      match nc with
      | NRef(gr) -> ("NRef", [string_of_global_reference gr])
      | NVar(id) -> ("NVar", [string_of_id id])
      | NApp(nc, ncl) ->
         ("NApp",
          [ string_of_notation_constr nc
          ; string_of_list string_of_notation_constr ncl
          ])
      | NHole(_, _, _) -> ("NHole", [])
      | NList (_, _, _, _, _) -> ("NList", [])
      | NLambda(_, _, _) -> ("NLambda", [])
      | NProd(name, nc1, nc2) ->
         ("NProd",
          [ string_of_name name
          ;  string_of_notation_constr nc1
          ;  string_of_notation_constr nc2
          ])
      | NBinderList(_, _, _, _) -> ("NBinderList", [])
      | NLetIn(_, _, _) -> ("NLetIn", [])
      | NCases(_, _, _, _) -> ("NCases", [])
      | NLetTuple(_, _, _, _) -> ("NLetTuple", [])
      | NIf(_, _, _, _) -> ("NIf", [])
      | NRec(_, _, _, _, _) -> ("NRec", [])
      | NSort(_) -> ("NSort", [])
      | NPatVar(_) -> ("NPatVar", [])
      | NCast(_, _) -> ("NCast", [])
    )

let string_of_subscopes (so, sl) =
  string_of_string_list
    [ string_of_option quote so
    ; string_of_list quote sl
    ]

let string_of_notation_var_instance_type nvit =
  mk_new (
      match nvit with
      | NtnTypeConstr -> ("NtnTypeConstr", [])
      | NtnTypeConstrList -> ("NtnTypeConstrList", [])
      | NtnTypeBinderList -> ("NtnTypeBinderList", [])
    )

let string_of_interpretation (l, notation_constr) =
  mk_new (
      ("Interpretation",
       [ string_of_list
           (fun (id, (subscopes, nvit)) ->
             string_of_string_list
               [ string_of_id id
               ;  string_of_subscopes subscopes
               ;  string_of_notation_var_instance_type nvit
               ])
           l
       ;  string_of_notation_constr notation_constr
       ])
    )

let string_of_loc loc =
  let (start, stop) = Loc.unloc loc in
  mk_new ("Loc", [string_of_int start; string_of_int stop])

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

(*
This type should be similar to constr_expr, but carry information only
available in glob_constr.
 *)

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
      "Notation_Rule",
      [ string_of_interp_rule interp_rule
      ;  string_of_interpretation interpretation
      ;  string_of_option string_of_int intoption
      ]
    )

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

let string_of_pre_env e =
  "{\n"
  ^ "}"

let string_of_env e = string_of_pre_env (Environ.pre_env e)
 *)

let find_notation_rule notation_name glob_constr =
  let candidate_rules = Notation.uninterp_notations glob_constr in
  try
    List.find
      (fun (ir, _, _) ->
        match ir with
        | NotationRule(_, n) -> n = notation_name
        | _ -> false
      )
      candidate_rules
  with Not_found ->
    print_string ("Looking for " ^ notation_name ^ "\n");
    List.iter (fun (ir, _, _) ->
        match ir with
        | NotationRule(_, n) -> print_string n
        | _ -> ()
      ) candidate_rules;
    print_newline ();
    failwith "find_notation_rule_for_glob_constr: not found"

let print s = Pp.msg (Pp.str s)

type mkBinderExprExpects =
  { bindingKind : binding_kind;
    globConstr : glob_constr;
  }

type 'a pre_expr =
  | Notation of notation * constr_notation_substitution * notation_rule
  | ProdN of 'a binder_expr list * 'a pre_expr
  | Ref of reference * instance_expr option
           * global_reference * glob_level list option
  | Todo of string

 and 'a my_local_binder =
   | MyLocalRawDef of Names.Name.t Loc.located * 'a pre_expr
   | MyLocalRawAssum of Names.Name.t Loc.located list * binder_kind * 'a pre_expr

 and 'a my_constr_notation_substitution =
   'a pre_expr list * 'a pre_expr list list * 'a my_local_binder list list

 and 'a binder_expr =
   Names.Name.t Loc.located list * binder_kind * binding_kind * 'a pre_expr

type expr = unit pre_expr

let rec mk_expr env (glob_constr, constr_expr) : expr =
  begin
    match constr_expr with
    | CNotation(_, notation, subst) ->

       (* let notation_constr = *)
       (*   Notation_ops.notation_constr_of_glob_constr *)
       (*     (default_env ()) glob_constr *)
       (* in *)

       let notation_rule = find_notation_rule notation glob_constr in

       (* print "Time to decypher notation!\n"; *)
       (* print (string_of_glob_constr glob_constr); *)
       (* print_newline (); print_newline (); *)
       (* print (string_of_notation_constr notation_constr); *)

       (* let constr_expr' = Constrextern.extern_glob_constr Names.Id.Set.empty glob_constr in *)

       (* print_newline (); print_newline (); *)
       (* print (string_of_notation_rule notation_rule); *)
       (* print_newline (); print_newline (); *)

       (* print_newline (); print_newline (); *)
       (* print (string_of_constr_expr constr_expr'); *)
       (* print_newline (); print_newline (); *)

       Notation(notation, subst, notation_rule)

    | _ ->
       begin
         match glob_constr, constr_expr with
         | GProd(_, _, _, _, _),
           CProdN(_, bel, ce) ->
            let (gc', bel') = mk_binder_expr_list env glob_constr bel in
            ProdN(bel', mk_expr env (gc', ce))
         | GRef(_, gr, gllo), CRef(r, ieo) ->
            Ref(r, ieo, gr, gllo)
         | _, _ ->

            print (string_of_glob_constr glob_constr);
            print_newline ();
            print_newline ();

            print (string_of_constr_expr constr_expr);
            print_newline ();
            print_newline ();

            failwith "mk_expr: missing case, see above"

     end
  end

(*
CProdN(BinderExpr([Name a, Name b, Name c], Default(Explicit), CRef(...)))

GProd(Name a, GRef(...), GProd(Name b, ...))
 *)

and mk_binder_expr_list env gc bel =
  begin
    match bel with
    | [] -> (gc, [])
    | (nameLocatedList, binderKind, ce) :: bel' ->
       let expects =
         match gc with
         | GProd(_, _, bk, gcType, _) ->
            { bindingKind = bk; globConstr = gcType }
         | _ -> failwith "mk_binder_expr_list: expected GProd"
       in
       let (gc', nll') = mk_binder_expr env expects nameLocatedList gc in
       let (gc'', bel'') = mk_binder_expr_list env gc' bel' in
       let e = mk_expr env (expects.globConstr, ce) in
       (gc'', (nll', binderKind, expects.bindingKind, e) :: bel'')
  end

and mk_binder_expr env expects nameLocatedList gc =
  match nameLocatedList, gc with
  | [], _ -> (gc, [])
  | nameLocated :: nls, GProd(_, name, bindingKind, gcL, gcR) ->
     assert (snd nameLocated = name);
     assert (bindingKind = expects.bindingKind);
     (*assert (gcL = expects.globConstr);*)
     (* TODO: should env be extended? *)
     let (gc', rest) = mk_binder_expr env expects nls gcR in
     (gc', nameLocated :: rest)
  | _, _ -> failwith "mk_binder_expr"

and mk_subst (cel, cell, lbll)
             (glob_constr, notation_constr)
    : unit my_constr_notation_substitution option =
  Some ([], [], [])

and mk_notation ?root:(root=None)
                (glob_constr, notation_constr) : expr option =
  let fail () =
    print_string "mk_notation failing:\n";
    print_string (string_of_glob_constr glob_constr);
    print_newline ();
    print_string (string_of_notation_constr notation_constr);
    print_newline ();
    None
  in
  match (glob_constr, notation_constr) with
  | GApp(_, gc, gcl), NApp(nc, ncl) ->
     begin
       let match_function = mk_notation (gc, nc) in
       let match_arguments = map_may_fail mk_notation (List.combine gcl ncl) in
       match match_function, match_arguments with
       | Some(f), Some(args) ->
          Some(Todo("App"))
       (* Some(App(notation root, f, args)) *)
       | _, _ -> fail ()
     end
  | GRef(_, gr, _), NRef(gr') ->
     if Globnames.eq_gr gr gr'
     then Some(Todo("Ref"))
       (*Some(mk_Ref(NotationPiece, gr))*)
     else None
  | GHole(_, ek, ipne, ggao), NHole(ek', ipne', ggao') ->
  (* TODO: check equality of some arguments? *)
     Some(Todo("Hole"))
  (*Some(Hole(NotationPiece))*)
  | GProd(loc, n, bk, gc1, gc2), NProd(n', nc1, nc2) ->
     if Names.Name.equal n n'
     then
       let match1 = mk_notation (gc1, nc1) in
       let match2 = mk_notation (gc2, nc2) in
       match match1, match2 with
       | Some(t1), Some(t2) ->
          Some(Todo("Prod"))
       (*Some(Prod(notation root, t1, t2(*, [(loc, n)], Default(bk)*)))*)
       | _, _ -> fail ()
     else None
  | GVar(_, s1), NVar(s2) ->
     if s1 = s2
     then Some(Todo("Var"))
               (* Some(Var(notation root, s2)) *)
     else fail ()
  (*
  | gc, NVar(_) ->
     fail ()
   *)
  | _, _ ->

     print (string_of_glob_constr glob_constr);
     print_newline ();
     print_newline ();

     print (string_of_notation_constr notation_constr);
     print_newline ();
     print_newline ();

     failwith "mk_notation: missing case, see above"

and string_of_expr env t =
  mk_new (
      match t with

      | Notation(n, cns, e) ->
         ("Notation",
          [ quote(n)
          ; string_of_constr_notation_substitution cns
          ; string_of_notation_rule e
          ])

      | ProdN(bel, e) ->
         ("Prod",
          [ string_of_list (string_of_binder_expr env) bel
          ; string_of_expr env e
          ])

      | Ref(r, ieo, gr, gllo) ->
         ("Ref",
          [ string_of_reference r
          ; "TODO"
          ; string_of_global_reference gr
          ; string_of_option (string_of_list string_of_glob_level) gllo
          ])

      | Todo(s) ->
         ("Todo", [s])

    )

and string_of_binder_expr env (nll, brk, bgk, e) =
  mk_new (
      "BinderExpr",
      [ string_of_list (string_of_located string_of_name) nll
      ; string_of_binder_kind brk
      ; string_of_binding_kind bgk
      ; string_of_expr env e
      ]
    )

let string_of_pre_goals string_of_a pgs =
  string_of_object
    [ ("fgGoals", string_of_list string_of_a pgs.fg_goals)
    ; ("bgGoals",
       string_of_list (fun (before, after) ->
           string_of_object
             [ ("before", string_of_list string_of_a before)
             ; ("after", string_of_list string_of_a after)
             ]
         ) pgs.bg_goals)
    ; ("shelvedGoals", string_of_list string_of_a pgs.shelved_goals)
    ; ("givenUpGoals", string_of_list string_of_a pgs.given_up_goals)
    ]

(*
let rec mk_term env (glob_constr, constr_expr): term =

  (*
  print_string("mk_term:\n\n");
  print_string (string_of_glob_constr glob_constr);
  print_newline ();
  print_string (string_of_constr_expr constr_expr);
  print_newline ();
  print_newline ();
   *)

  match constr_expr with
  | CNotation(_, notation, subst) ->
     let notation_constr =
       Notation_ops.notation_constr_of_glob_constr (default_env ()) glob_constr
     in
     let candidate_rules = Notation.uninterp_notations glob_constr in
     let correct_rule =
       try
         List.find
           (fun (ir, _, _) ->
             match ir with
             | NotationRule(_, n) -> notation = n
             | _ -> false
           )
           candidate_rules
       with Not_found ->
         print_string ("Looking for " ^ notation ^ "\n");
         List.iter (fun (ir, _, _) ->
             match ir with
             | NotationRule(_, n) -> print_string n
             | _ -> ()
           ) candidate_rules;
         print_newline ();
         failwith "Beepboop"
     in
     begin
       let term_option =
         mk_notation ~root:(Some(correct_rule, subst)) (glob_constr, notation_constr)
       in
       match term_option with
       | None -> failwith "mk_term: mk_notation failed"
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
       | _, CProdN(loc, bel, ce2) ->
          begin
            match bel with
            | [] -> mk_term env (glob_constr, ce2)
            | (nal, bk, ce1) :: bel ->
               match glob_constr with
               | GProd(_, _, _, gc1, gc2) ->
                  Prod(NotNotation,
                       mk_term env (gc1, ce1),
                       mk_term env (gc2, CProdN(loc, bel, ce2))(*,
                       nal, bk*))
               | _ -> failwith "mk_term: non-empty CProd, not a GProd"
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
          print_string (
              "OOPS\n" ^ string_of_glob_constr glob_constr
              ^ "\n,\n" ^ string_of_constr_expr constr_expr
              ^ "\n"
            );
          failwith "mk_term failed"
     end

and notation root =
  match root with
  | None -> NotationPiece
  | Some(notation, subst) -> NotationRoot(notation, subst)

and mk_notation ?root:(root=None) (glob_constr, notation_constr): term option =
  let fail () =
    print_string "mk_notation failing:\n";
    print_string (string_of_glob_constr glob_constr);
    print_newline ();
    print_string (string_of_notation_constr notation_constr);
    print_newline ();
    None
  in
  match (glob_constr, notation_constr) with
  | GApp(_, gc, gcl), NApp(nc, ncl) ->
     begin
       let match_function = mk_notation (gc, nc) in
       let match_arguments = map_may_fail mk_notation (List.combine gcl ncl) in
       match match_function, match_arguments with
       | Some(f), Some(args) -> Some(App(notation root, f, args))
       | _, _ -> fail ()
     end
  | GRef(_, gr, _), NRef(gr') ->
     if Globnames.eq_gr gr gr'
     then
       Some(mk_Ref(NotationPiece, gr))
     else None
  | GHole(_, ek, ipne, ggao), NHole(ek', ipne', ggao') ->
     (* TODO: check equality of some arguments? *)
     Some(Hole(NotationPiece))
  | GProd(loc, n, bk, gc1, gc2), NProd(n', nc1, nc2) ->
     if Names.Name.equal n n'
     then
       let match1 = mk_notation (gc1, nc1) in
       let match2 = mk_notation (gc2, nc2) in
       match match1, match2 with
       | Some(t1), Some(t2) ->
          Some(Prod(notation root, t1, t2(*, [(loc, n)], Default(bk)*)))
       | _, _ -> fail ()
     else None
  | GVar(_, s1), NVar(s2) ->
     if s1 = s2
     then Some(Var(notation root, s2))
     else fail ()
  | gc, NVar(_) ->
     fail ()
  | _, _ -> failwith "TODO"
            *)

(*
and string_of_term env = string_of_preterm (string_of_notation_marker env)

(*
This should turn a constr_expr into a term, and then print that term
 *)
and string_of_constr_expr' env constr_expr =
  (* I don't remember why I did the bottom one and it doesn't work
   when the environment gets extended... *)
  string_of_constr_expr constr_expr
  (*
  print_string "string_of_constr_expr'\n";
  print_string (string_of_constr_expr constr_expr);
  let pre_env = Environ.pre_env env in

  let glob_constr = Constrintern.intern_constr env constr_expr in
  print_string "After intern_constr\n";
  string_of_term env (mk_term env (glob_constr, constr_expr))
   *)

and string_of_local_binder (env: Environ.env) lb =
  let s = string_of_constr_expr' env in
  mk_new (
      match lb with
      | LocalRawDef(ln, ce) ->
         "LocalRawDef(" ^ string_of_located string_of_name ln
         ;  s ce
         ^ ")"
      | LocalRawAssum(lnl, bk, ce) ->
         "LocalRawAssum(" ^ string_of_list (string_of_located string_of_name) lnl
         ;  string_of_binder_kind bk
         ;  s ce
         ^ ")"
    )

and string_of_subst env ((cel, cell, lbll) as subst) =
  let s = string_of_constr_expr' env in
  mk_new (
      "Substitutions("
      (* ^ string_of_list s cel *)
      (* ;  string_of_list (string_of_list s) cell *)
      (* ;  string_of_list (string_of_list (string_of_local_binder env)) lbll *)
      ^ ")"
    )

and string_of_notation_marker env nm =
  mk_new (
      match nm with
      | NotationRoot(s, subst) ->
         "NotationRoot(" ^ string_of_notation_rule s
         ;  string_of_subst env subst
         ^ ")"
      | NotationPiece -> "NotationPiece", [])
      | NotNotation -> "NotNotation", [])
    )
 *)
