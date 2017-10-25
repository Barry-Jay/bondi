(* begin readline-bare *)

let isatty () = true

let readline prompt =
  print_string prompt;
  try read_line () ^ "\n"
  with End_of_file -> ""

(* end readline-bare *)
(* begin sys-bare *)

let now () = "??"

let who () =
  try Sys.getenv "USER" with Not_found ->
    try Sys.getenv "LOGNAME" with Not_found ->
      "??"

let hostname () =
  try Sys.getenv "HOSTNAME" with Not_found -> "??"

(* end sys-bare *)
