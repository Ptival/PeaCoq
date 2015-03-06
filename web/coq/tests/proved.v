(* Some of the proof is done in PeaCoq style, then the rest breaks the style *)
Theorem t : forall n, n = 0 \/ n <> 0.
Proof.
  { intro. { destruct n.
             { left. { reflexivity. } }
             { right. intro. { discriminate. }
             }
           }
  } }
Qed.
