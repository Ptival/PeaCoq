Theorem t : forall n, n = 0 \/ n > 0.
Proof.
  intro. destruct n.
  auto.
  + { right.
      - { { admit.
          }
        }
    }
Qed.
