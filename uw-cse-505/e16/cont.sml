open SMLofNJ.Cont

val _ =
  let
    val x = ref true
    val g : int cont option ref = ref NONE
    val y = ref (1 + 2 + (callcc (fn k => ((g := SOME k); 3))))
    (* wrong - infinite loop! *)
    (* val x = ref true *)
    val z = if !x then (
              x := false;
              throw (valOf (!g)) 7
            ) else
              !y
  in
    print ("\n\n" ^ Int.toString z ^ "\n\n")
  end
