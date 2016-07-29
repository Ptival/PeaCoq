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
    [ ("constructorName", quote name)
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
      [ quote (Names.MutInd.to_string mi)
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

let string_of_id id = quote (Names.Id.to_string id)

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
      | Const((c, _)) -> ("Const", [quote (string_of_constant c)])
      | Ind((i, _)) -> ("Ind", [string_of_inductive(i)])
      | Construct((((m, i), j), u)) ->
         ("Construct",
          [ quote (Names.MutInd.to_string m)
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
      | UnpTerminal(s) -> ("UnpTerminal", [quote s])
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
      | String(s) -> ("PrimTokenString", [quote s])
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
          ; string_of_option (string_of_list string_of_cases_pattern_expr) cl1
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
          ; quote s
          ; string_of_cases_pattern_expr cases
          ])
      | CPatCast(_) -> ("TODO_CPatCast", [])
    )

let string_of_constructor (ind, i) =
  mk_new ("Constructor", [string_of_inductive ind; string_of_int i])

let string_of_global_reference gr =
  mk_new (
      match gr with
      | VarRef(v) -> ("VarRef", [string_of_id v])
      | ConstRef(c) -> ("ConstRef", [quote (string_of_constant c)])
      | IndRef(i) -> ("IndRef", [string_of_inductive i])
      | ConstructRef(c) -> ("ConstructRef", [string_of_constructor c])
    )

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

      | CLetTuple(loc, nll, nlo_ceo, ce1, ce2) ->
         ("CLetTuple",
          [ string_of_location loc
          ; string_of_list (string_of_located string_of_name) nll
          ; string_of_pair
              (string_of_option (string_of_located string_of_name))
              (string_of_option string_of_constr_expr)
              nlo_ceo
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
          ; quote s
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

      | LocalPattern(_, _, _) -> ("LocalPattern", ["TODO"])

    )

and string_of_case_expr (ce, nlo, cpeo) =
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
