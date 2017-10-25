val initial_types : string list 
val declare_type_synonym : string -> P_data.p_type -> unit
val declare_type : P_data.datatype_declaration ->  unit
(* delete ??
val declare_data_type :P_data.datatype_declaration ->  unit
*)

val declare : P_data.let_status  -> P_data.p_term -> P_data.p_term -> unit
val add_decl : P_data.let_status -> P_data.identifier -> P_data.p_term -> P_data.p_type option -> P_data.p_term -> unit
val add_outer_decl : P_data.identifier -> P_data.p_term -> P_data.p_type option -> P_data.p_term -> unit
val declare_class :
    string ->
    P_data.tyVar list ->
    string option ->
    P_data.p_term list * (P_data.let_status * P_data.identifier * P_data.p_term) list ->
    P_data.add_case list -> unit


