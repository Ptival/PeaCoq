Theorem test : forall n
  (H1 : True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True)
  (H2 : match n with O => True | _ => False end),
  match n with
  | O => O
  | _ => O
  end = O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O ->
  0 + 0 + 0 = (0 + (0 + 0)) ->
  n = n.
Proof. intros. reflexivity.
Qed.