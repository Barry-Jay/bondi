module OrderedStrings:
    sig
      type t = string
      val compare : t -> t -> int 
    end

module StringMap : 
  sig
    type key = OrderedStrings.t
    and 'a t = 'a Map.Make(OrderedStrings).t
    val empty : 'a t
    val add : key -> 'a -> 'a t -> 'a t
    val find : key -> 'a t -> 'a
    val remove : key -> 'a t -> 'a t
    val mem : key -> 'a t -> bool
    val iter : (key -> 'a -> unit) -> 'a t -> unit
    val map : ('a -> 'b) -> 'a t -> 'b t
    val fold : (key -> 'a -> 'b -> 'b) -> 'a t -> 'b -> 'b
  end
;;


type datum_value =
    Int of int
  | Float of float
  | Char of char
  | String of string
  | Bool of bool 
  | Socket of Unix.file_descr * Pervasives.in_channel * (Pervasives.out_channel *bool) * string
  | Host of Unix.host_entry
  | Un                            


exception Error of string
val basicError : string -> 'a

val datum_equal : datum_value * datum_value -> bool 
val datum_type_string : datum_value -> string 
(*
val string_of_datum_value : datum_value -> string
has been moved to p_data.ml to allow for modes to influence printing 
*)
val all_ops : (string list * string)  StringMap.t 
val eval_datum : string -> datum_value list -> datum_value
val prec_op : string -> int
val oper_table :  (StringMap.key, StringMap.key) Hashtbl.t
val noper_table :  (StringMap.key, StringMap.key) Hashtbl.t
