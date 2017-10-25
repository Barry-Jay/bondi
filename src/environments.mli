module OrderedTyVars: 
  sig
    type t = P_data.tyVar 
    val compare : t -> t -> int 
  end 
module TyMap :
  sig
    type key = OrderedTyVars.t
    and 'a t = 'a Map.Make(OrderedTyVars).t
    val empty : 'a t
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  end
type term_variable =
  | Var of P_data.identifier
  | Mvar of int

(* typed term variables should only appear as arguments to
abstractions. Otherwise use Typed(t,ty). Unfortunately, these have
been used in defining datatypes, so will have to be handled, at least
temporarily, in environments, etc.  *)

module Ordered_vars :
  sig
    type t = term_variable
    val compare : t -> t -> int
  end
module TVarSet : Set.S with type elt = Ordered_vars.t
module TMap :
  sig
    type key = Ordered_vars.t
    and 'a t = 'a Map.Make(Ordered_vars).t
    val empty : 'a t
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  end

type i_type =
  | TyV of P_data.tyVar * int
  | TyC of P_data.tyVar * int
  | ApplyF of i_type * i_type
  | ChoiceF of i_type * i_type
  | SuperF of i_type * i_type
  | Funty of i_type  * i_type 
  | Linty of i_type  
  | Ref of i_type 
  | Array of i_type               
  | Quant of P_data.tyVar * i_type 

type i_term =
  | Tvar of term_variable * int 
  | Tnextvar 
  | Tsuper of term_variable * int 
  | Twildcard of string 
  | Twildstring                   
  | Tconstructor of term_variable  * int
  | Datum of Datum.datum_value 
  | Oper of string * i_term list
  | Apply of i_term * i_term
  | Lam of term_variable * i_term 
  | Case of  term_variable list option * i_term * i_term 
  | Choice of  i_term * i_term 
  | Over of  i_term * i_term 
  | Addcase of term_variable * i_term * i_type option 
  | Subcase of term_variable 
  | Tlet of P_data.let_status * term_variable * i_term * i_term 
(*
  | Tletrec of term_variable * i_term * i_term 
  | Tletext of term_variable * i_term * i_term 
  | Tletdiscontinuous of term_variable * i_term * i_term 
*)
  | TnewArr of i_term * i_term             
(*> CPC *)
  | Tdname of P_data.name_form * i_term * i_type
  | Tcname of P_data.name_form * term_variable * int * i_type
  | Tname of P_data.name_form * term_variable * int * i_type
  | Tpapp of i_term * i_term * i_type
  | Prll of i_term * i_term
  | Rest of term_variable * i_term
  | Repl of i_term
  | Pcase of i_term * i_term
(*< CPC *)

type sub = i_type TyMap.t

type value =
  | Vvar of term_variable
  | Vsuper of value
  | Vconstructor of term_variable * int
  | Vdatum of Datum.datum_value
  | Vwildcard of string
  | Vwildstring
  | Vas of value * value
  | Vview of value * value
  | Vwhere of value * i_term
  | Vapply of value * value
  | Vlam of term_variable *  value_env ref * i_term
  | Vcase of value * value_env ref * i_term
  | Vchoice of value * value
  | Vext of value ref 
  | Vref of value ref
  | Varray of value array
(*> CPC *)
  | VtySub of sub
(*< CPC *)
and value_env = value TMap.t


(* type sub = i_type TyMap.t *)

type type_data = 
  | Synonym of i_type  
  | Class of (P_data.tyVar * int) option * 
	(P_data.p_term -> P_data.p_term) * (i_term -> i_term) * int 

type type_env = (int * type_data) list TyMap.t 
type constructor_env = (int * (i_type * P_data.let_status)) list TMap.t
               (* declaration time, type *)
type scheme_env = (i_type * P_data.let_status) TMap.t 


type global_value_env =
      (int * (value * (P_data.let_status * i_type * bool))) list TMap.t
      (* dec time, location,   status,         type  has refVars *) 

exception Wrong_index of int


(*** i_data *) 

exception TypeError of i_type list * string
exception TermError of i_term list * string
val typeError : i_type list -> string -> 'a

val fvar : string -> i_type
val cvar : string -> i_type
val apF : i_type -> i_type -> i_type
val apF2 : i_type -> i_type -> i_type -> i_type
val funty : i_type -> i_type -> i_type
val funty2 : i_type -> i_type -> i_type -> i_type
val comm : i_type

val termVarError : term_variable -> string -> 'a
val termError : i_term list -> string -> 'a

(* Commented out by TGW 2011-05-23
 * Note: I don't know why this was shared, seems like a bad idea.
 * Also it is no longer used anywhere.
val fvc : int ref *)
val nextvar : unit -> term_variable

val tvar : P_data.identifier -> i_term
val t_un : i_term 
val zcvar : P_data.identifier -> i_term
val exn :   i_term
val isValue : i_term -> bool 

(*** global environments *)

val globalTyEnv : type_env ref 
val gTyEnvFind : int -> TyMap.key -> int * type_data
val gTyEnvAdd : TyMap.key -> int -> type_data -> unit


val get_best : int -> (int * 'a) list -> int * 'a
val envFind : int -> TMap.key -> (int * 'a) list TMap.t ref -> int * 'a 
val envFindFull : int -> TMap.key -> (int * 'a) list TMap.t ref -> int *'a 
val envAdd : TMap.key -> int -> 'b -> (int * 'b) list TMap.t ref -> unit

val globalVEnv : global_value_env ref
val globalCEnv : constructor_env ref
val globalRefVarSub: sub ref

(*** type substitutions *) 

val freshen_tyvars:     
    P_data.tyVar list -> i_type TyMap.t * P_data.tyVar list
val freshen_tyvar2: P_data.tyVar -> P_data.tyVar -> i_type TyMap.t * P_data.tyVar

val idSub : sub  
val composeSubs : sub -> sub -> sub
val applySub : sub -> i_type -> i_type 

val list_remove : P_data.tyVar -> P_data.tyVar list -> P_data.tyVar list
val freeTyVars : sub -> i_type -> P_data.tyVar list
val freeRefTyVars : i_type -> P_data.tyVar list
val covTyVars : sub -> i_type -> P_data.tyVar list
val freeTyVarsInSEnv : sub -> scheme_env -> P_data.tyVar list 
val avoid : P_data.tyVar -> sub -> bool 

val declaration_counter : int ref
val get_declaration_counter : unit -> int 

val classTyString : string 

val type_of_class : string * int -> i_type list -> i_type -> i_type
                   (* class_name, dec time, args, rest, type of the class *) 
val convert_type : P_data.p_type -> i_type
    (* from p_type to i_type *) 
val pattern_of_class : P_data.tyVar * int -> P_data.p_term -> P_data.p_term 
                       (* class_name, dec time, pattern for the rest, pattern for the class *) 


(*** formatting *)

val f_string_tbl : (string * string) list ref
val f_counter : string ref
val format_untidy_tyvar : P_data.tyVar -> unit
val format_type : bool -> i_type -> unit
val format_specialisation : i_type -> unit
val format_tyvarlist : P_data.tyVar list -> unit
val format_sub : sub -> unit
val format_sEnv : sub -> i_type TMap.t -> unit
val format_term_variable :term_variable -> unit
val format_term : i_term -> unit
val format_value : value -> unit
val formatTypeError :
    i_type TyMap.t -> i_type list * string -> unit
val formatTermError :  i_term list * string -> unit

val peek_type : i_type -> string -> unit 
val peek_tyvs : P_data.tyVar list  -> string -> unit 
val peek : i_term -> string -> unit
val peeks : i_term list -> string -> unit
val peek_value : value -> string -> unit

(*> CPC *)
val new_lock : unit -> (unit -> unit) * (unit -> unit)
val optlock : unit -> (unit -> bool) * (unit -> unit)
val new_generator : (int -> 'a) -> unit -> 'a
val procEnv : (int , ((unit -> bool) * (unit -> unit) * value_env * i_term)) Hashtbl.t
val show_status : unit -> unit
val procGen : unit -> int
(*< CPC *)

