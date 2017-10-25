(* begin readline-gnu *)

let isatty () = Gnu_readline.isatty 0

let readline = Gnu_readline.readline

(* end readline-gnu *)
(* begin sys-unix *)

open Unix

let string_of_time tm =
  Printf.sprintf "%s %s %2d %02d:%02d:%02d GMT %d"
    ([|"Sun";"Mon";"Tue";"Wed";"Thu";"Fri";"Sat";|].(tm.tm_wday))
    ([|"Jan";"Feb";"Mar";"Apr";"May";"Jun";"Jul";"Aug";"Sep";"Oct";"Nov";"Dec";|].(tm.tm_mon))
    (tm.tm_mday)
    (tm.tm_hour) (tm.tm_min) (tm.tm_sec)
    (tm.tm_year + 1900)
let now () =
  string_of_time (gmtime (time ()))

let who () =
  try Sys.getenv "USER" with Not_found ->
    try Sys.getenv "LOGNAME" with Not_found ->
      try getlogin () with _ ->
        "??"

let hostname () =
  try Sys.getenv "HOSTNAME" with Not_found ->
    try gethostname () with _ ->
      "??"

(* end sys-unix *)
