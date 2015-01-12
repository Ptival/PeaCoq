
Definition test := (fun (x, y) => y) (0, 1).

Fixpoint nat_le (m n : nat) : bool :=
  match m with
    | O => true
    | S mp =>
      match n with
        | O => false
        | S np => nat_le mp np
      end
  end
.

(* notree *)
Lemma nat_le_ok:
  forall m n, nat_le m n = true -> m <= n.
Proof.
  induction m; firstorder.
  admit.