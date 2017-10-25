
(*
val store : Environments.value Environments.TMap.t ref
val getstore : Environments.term_variable ->  Environments.value 
val getval : Environments.term_variable ->  Environments.i_term
*)
val printString: Environments.value ->  unit

val evaluate : Environments.i_term -> Environments.value
val print_value : Environments.value -> unit


