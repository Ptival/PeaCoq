Theorem long_theorem :
  forall (a b c d e : nat),
    a = b ->
    b = c ->
    a < c ->
    e = S e ->
    c = d.