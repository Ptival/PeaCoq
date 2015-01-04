(*
An artificially slow tactic, to test asynchronicity and delays between server and client
*)

Ltac ackerman m n :=
  match m with
    | O => constr:(S n)
    | S ?m' =>
      match n with
        | O =>
          let res := ackerman m' 1 in
          constr:(res)
        | S ?n' =>
          let tmp1 := ackerman m n' in
          let tmp2 := ackerman m' tmp1 in
          constr:(tmp2)
      end
  end.

(* notree *)
Theorem t : False.
Proof.
  let res := ackerman 3 5 in pose res.
  idtac "to be processed".
  idtac "does idtac print this?".
Qed.