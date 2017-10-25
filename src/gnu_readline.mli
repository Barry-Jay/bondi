(* interface to C routines calling Gnu readline and unix isatty functions *)

external readline : string -> string = "caml_readline";;
external isatty : int -> bool = "caml_isatty";;

