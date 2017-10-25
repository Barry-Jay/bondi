(* Module [Config]: Compile-time configuration options *)

val isatty : unit -> bool
    (* [isatty ()] ==> bool
       Whether standard input is a terminal. *)
val readline : string -> string
    (* [readline prompt] ==> [line]
       Read a line from standard input. *)

val now : unit -> string
    (* [now ()] ==> ["Tue Dec  7 16:22:55 EST 1999"]
       Return the current date and time in human format. *)
val who : unit -> string
    (* [who ()] ==> [user_name]
       Return the name of the user. *)
val hostname : unit -> string
    (* [where ()] ==> [machine_name]
       Return the name of the machine on which we are running. *)

(* End of file config.mli. *)
