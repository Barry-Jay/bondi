(* begin readline-gnu *)

let isatty () = Gnu_readline.isatty 0

let readline = Gnu_readline.readline

(* end readline-gnu *)
