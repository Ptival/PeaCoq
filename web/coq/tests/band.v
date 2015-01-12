
Definition band b1 b2 : bool :=
  match b1 with
    | true => match b2 with
                | true => true
                | false => false
              end
    | false => false
  end.