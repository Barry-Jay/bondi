(* BONDI version must be moved to ../VERSION *)

let version = "2.09" 
let standard_library_default =
     Printf.sprintf "%s/.bondi" @@ Unix.getenv "HOME"
(*
 let standard_prelude_default =
     Printf.sprintf "%s/.bondi/prelude" @@ Unix.getenv "HOME"
     *)
let standard_library =
  try
    Sys.getenv "BONDI_LIB_DIR"
  with Not_found ->
  try
    Sys.getenv "BONDILIB"
with Not_found ->
(*
 we failed to create an alternative pathway by: 
 try standard_prelude_default
with Not_found ->
*)

standard_library_default
