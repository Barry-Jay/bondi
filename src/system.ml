(* BONDI version must be moved to ../VERSION *)

let version = "2.09" 
let standard_library_default = "/usr/lib/bondi"
let standard_library =
  try
    Sys.getenv "BONDI_LIB_DIR"
  with Not_found ->
  try
    Sys.getenv "BONDILIB"
  with Not_found ->
    standard_library_default

let architecture = "x86_64"
let model        = "unknown"
let system       = "linux-gnu"
;;
