type identifier = string
type tyVar = 
    TyVar of string   (* user-defined variables *)
  | MTypeVar of int   (* machine-introduced type variable  *)
type p_type =
  | PtyV of tyVar 
  | Pconstant of string
  | PapplyF of p_type * p_type       (* applications *)
  | Pfunty of p_type  * p_type  
  | Plinty of p_type  
  | Pquant of tyVar * p_type 
  | Pnestedclass of string * p_type list * p_type
  | Pref of p_type 
  | Parr of p_type 
type p_term =
  | Ptvar of identifier 
  | Pwildcard of string 
  | Pconstructor of identifier 
  | Pdatum of Datum.datum_value 
  | Poper of string * p_term list (* name and arguments *)
	(* datum operators, conditionals, new, assignment, output *) 
  | Papply of p_term * p_term
  | Plam of p_term * p_term 
(*
  | Plin of p_term * p_term 
*)
  | Pcases of p_case list 
  | Paddcase of identifier * p_case
  | Psubcase of identifier 
  | Plet of let_status * p_term * p_term * p_term 
  | Ptyped of p_term * p_type
  | Pnew of string * p_type list 
  | PnewArr of p_term * p_term
  | Pinvoke of p_term * identifier * bool (* a super ? *) 
(*> CPC *)
  | Pname of name_form * identifier
  | Pcname of name_form * identifier
  | Pdname of name_form * p_term
  | Pparr of p_term * p_term
  | Prest of identifier * p_term
  | Prepl of p_term
  | Ppcase of p_term * p_term
and name_form = Variable | Protected | Binding
(*< CPC *)
and let_status = Simple | Recursive | Extensible | Linear | Method | Discontinuous
and p_case = identifier list option * p_term * p_type option * p_term 
type add_case = identifier * p_case
type simple_datatype_declaration = 
    p_type list*(identifier * p_type list) list 
type datatype_declaration = 
    identifier * simple_datatype_declaration list * add_case list 
type show_mode = 
  | Show_on 
  | Show_off
type shell_action =
  | Let_decl of  p_term * p_term
  | Lin_decl of  p_term * p_term
  | Let_type_synonym of  identifier * p_type
  | Let_type of datatype_declaration
  | Let_class of string * tyVar list  * string option *
      ((p_term  list * (let_status * identifier * p_term) list) * add_case list)
  | Directive of string * string 

exception PTermError of p_term list * string
exception PtypeError of p_type list * string

val pTermError : p_term list -> string -> 'a
val pTypeError : p_type list -> string -> 'a

val nextTypeVar : unit -> tyVar
val pconstTy : string -> p_type
val pApF : p_type -> p_type -> p_type 
val pclass :  string * p_type list * p_type -> p_type

val zvar : identifier -> p_term
val p_datum : Datum.datum_value ->  p_term
val ap : p_term -> p_term -> p_term
val ap2 : p_term -> p_term -> p_term -> p_term
val lam : p_term -> p_term -> p_term
val multilam :  p_term list -> p_term -> p_term
(*> CPC *)
val multirest : identifier list -> p_term -> p_term
(*< CPC *)
(*
val lin : p_term -> p_term -> p_term
val multilin :  p_term list -> p_term -> p_term
*)

val modes : (string * show_mode) list ref
val set_mode : string -> show_mode -> unit
val safe_set_mode : string -> show_mode -> unit
val get_mode : string -> show_mode

type command_line = {
    mutable cl_std : bool;              (* Load the standard prelude? *)
    mutable cl_errorstopmode : bool;    (* Halt on any error? *)
    mutable cl_files : string list;     (* Files to run *)
  }
val parse_command_line : string array -> command_line

val pf : string -> unit
val ps : string -> unit
val lpn : unit -> unit
val rpn : unit -> unit

val incrStringCounter : string -> char -> char -> string

val format_p_type : p_type -> unit
val format_p_term : p_term -> unit
val formatPTermError :  p_term list * string -> unit

val p_peek_type : p_type -> string -> unit
val p_peek : p_term -> string -> unit
val p_peeks : p_term list -> string -> unit

