(* begin readline-bare *)

let isatty () = true

let readline prompt =
  print_string prompt;
  try read_line () ^ "\n"
  with End_of_file -> ""

(* end readline-bare *)
