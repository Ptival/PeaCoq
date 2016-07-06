(*i camlp4deps: "grammar/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

let contrib_name = "peacoq_plugin"

DECLARE PLUGIN "peacoq_plugin"

open Feedback
open Peacoq_utils
open Pp
open Printer
open Util

let print s = Feedback.msg_notice (Pp.str s)

(* don't want Pp.quote *)
let quote = Peacoq_utils.quote

(* : env -> evar_map -> constr -> constr_expr *)
(*
The boolean means:
- [true]: do α-conv as a goal, avoiding names in context
- [false]: just avoid names that appear in subterms
*)
let constr_expr_of_constr = Constrextern.extern_constr true

let ppstring_of_constr c =
  let pp = Printer.pr_constr c in
  Pp.string_of_ppcmds pp

let print_constr c = print (string_of_constr c)

let print_constr_expr c = print (string_of_constr_expr c)

let print_named_declaration (ident, maybeValue, ttype) =
  let valueStr = match maybeValue with
    | Some(value) -> " := " ^ string_of_constr value
    | None -> ""
  in
  print (Names.Id.to_string ident ^ valueStr ^ " : " ^ string_of_constr ttype)

let map_option f = function None -> None | Some(x) -> Some(f x)

let string_of_named_declaration convert decl =
  (*
(* I don't know how to: *)
let open Context.Named.Declaration in
(* in .ml4 files... *)
   *)
  let (name, maybeTerm, typ) = (
    Context.Named.Declaration.get_id decl,
    Context.Named.Declaration.get_value decl,
    Context.Named.Declaration.get_type decl
    )
  in
  string_of_object
    [ ("name", string_of_id name)
    ; ("maybeTerm", string_of_option
                      string_of_constr_expr
                      (map_option convert maybeTerm))
    ; ("type", string_of_constr_expr (convert typ))
    ]

module Interface = struct

  type goal = {
      goal_id : string;
      goal_hyp : string list;
      goal_ccl : string;
    }

  let string_of_goal g =
    string_of_object
      [ ("goal_id", g.goal_id)
      ; ("goal_hyp", string_of_list quote g.goal_hyp)
      ; ("goal_ccl", quote g.goal_ccl)
      ]

end

let process_goal sigma g =
  let env = Goal.V82.env sigma g in
  let min_env = Environ.reset_context env in
  let id = Goal.uid g in
  let ccl =
    let norm_constr = Reductionops.nf_evar sigma (Goal.V82.concl sigma g) in
    string_of_ppcmds (pr_goal_concl_style_env env sigma norm_constr) in
  let process_hyp d (env,l) =
    let d = Context.NamedList.Declaration.map_constr (Reductionops.nf_evar sigma) d in
    let d' = List.map
               (fun name ->
                 match pi2 d with
                 | None -> Context.Named.Declaration.LocalAssum (name, pi3 d)
                 | Some value -> Context.Named.Declaration.LocalDef (name, value, pi3 d))
               (pi1 d) in
      (List.fold_right Environ.push_named d' env,
       (string_of_ppcmds (pr_var_list_decl env sigma d)) :: l) in
  let (_env, hyps) =
    Context.NamedList.fold process_hyp
      (Termops.compact_named_context (Environ.named_context env)) ~init:(min_env,[]) in
  { Interface.goal_hyp = List.rev hyps; Interface.goal_ccl = ccl; Interface.goal_id = id; }

type peacoq_goal =
  { pphyps: int list
  ; ppconcl: Term.constr
  }

let string_of_goal env sigma (hyps, concl) =
  let convert = constr_expr_of_constr env sigma in
  (* hyps are stored in reverse order *)
  let hyps = List.rev hyps in
  string_of_object
    [ ("hyps", string_of_list (string_of_named_declaration convert) hyps)
    ; ("concl", string_of_constr_expr (convert concl))
    ]

let format_for_peacoq env sigma g =
  let hyps = Environ.named_context_of_val (Goal.V82.nf_hyps sigma g) in
  let concl = Goal.V82.concl sigma g in
  string_of_object
    [ ("ppgoal", string_of_goal env sigma (hyps, concl))
    ; ("goal", Interface.string_of_goal (process_goal sigma g))
    ]

VERNAC COMMAND EXTEND PeaCoqQuery CLASSIFIED AS QUERY
| [ "PeaCoqGetContext" ] ->
   [

     try

     let (sigma, env) = Lemmas.get_current_context () in
     let proof = Pfedit.get_pftreestate () in
     let goals = Proof.map_structured_proof proof (format_for_peacoq env) in
     print (string_of_pre_goals (fun s -> s) goals);

     with e -> print "";

   ]
END;;
