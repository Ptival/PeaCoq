(*i camlp4deps: "grammar/grammar.cma" i*)
(*i camlp4use: "pa_extend.cmp" i*)

let contrib_name = "peacoq_plugin"

DECLARE PLUGIN "peacoq_plugin"

open Peacoq_utils
open Proof

let print s = Pp.msg (Pp.str s)

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

let rec print_notations_aux ((((_, (_, notation_constr), _), rest))) =
     print (string_of_notation_constr notation_constr);
     List.iter print_notations_aux rest

let rec print_notations glob_constr = ()
  (*
  match find_matching_notations glob_constr with
  | None -> print "No notation found"
  | Some(n) -> print_notations_aux n
   *)

let map_option f = function None -> None | Some(x) -> Some(f x)

let string_of_named_declaration convert (name, maybeTerm, typ) =
  "{ name: "  ^ string_of_id name
  ^ ", maybeTerm: "
  ^ string_of_option
      string_of_constr_expr
      (map_option convert maybeTerm)
  ^ ", type: "
  ^ string_of_constr_expr (convert typ)
  ^ " }"

VERNAC COMMAND EXTEND PeaCoqQuery CLASSIFIED AS QUERY
| [ "PeaCoqGetContext" ] ->
   [
     try
     let (evm, env) = Lemmas.get_current_context () in
     let proof = Pfedit.get_pftreestate () in

     let goals =
       Proof.map_structured_proof
         proof
         (fun evm g ->
           (Environ.named_context_of_val (Goal.V82.nf_hyps evm g),
            Goal.V82.concl evm g))
     in

     let convert = constr_expr_of_constr env evm in

     let string_of_goal (hyps, concl) =
       (* hyps are stored in reverse order *)
       let hyps = List.rev hyps in
       "{ hyps:\n"
       ^ string_of_list (string_of_named_declaration convert) hyps
       ^ "\n, concl:\n" ^ string_of_constr_expr (convert concl)
       ^ "\n}"
     in

     print (string_of_list string_of_goal goals.fg_goals);

     with e -> print (string_of_list (fun _ -> "") []);
     (*let glob_constr = Constrintern.intern_constr env constr_expr in*)

   ]
END;;
