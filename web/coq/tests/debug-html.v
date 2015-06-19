Theorem test : forall n
  (H1 : True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True -> True)
  (H2 : match n with O => True | _ => False end),
  match n with
  | O => O
  | _ => O
  end = O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O + O ->
  n = O.
Proof. intros. destruct n; [ reflexivity | ].