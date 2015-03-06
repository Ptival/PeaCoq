Inductive three :=
| One
| Two
| Three
.

Theorem t : forall t, t = One \/ t = Two \/ t = Three.
