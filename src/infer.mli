
val clos_ty_with_refVars : Environments.sub -> Environments.scheme_env -> 
  Environments.i_type -> Environments.i_type * P_data.tyVar list
      (* quantify all type variables neither free in the scheme_env nor in refVars 
*)
val clos_ty : Environments.sub -> Environments.scheme_env -> 
  Environments.i_type -> Environments.i_type 
      (* quantify all type variables not free in the scheme_env *) 


val inst_tyscheme : Environments.i_type -> Environments.i_type
      (* instantiate all leading quantified type variables *) 
val is_simple_method_type : P_data.tyVar list -> Environments.i_type -> Environments.i_type -> bool
                            (* delta               arg type             result type  *) 
val inf_linear :
    P_data.p_term ->
    (Environments.scheme_env)  ->
    Environments.TyMap.key list ->
    Environments.scheme_env ->
    Environments.term_variable list option ->
    Environments.sub ->
    Environments.i_type option ->
    P_data.let_status ->
    Environments.sub * Environments.i_term * Environments.TyMap.key list *
    Environments.scheme_env * Environments.i_type

val infer : P_data.p_term -> Environments.i_type -> Environments.i_term * Environments.i_type * Environments.sub 
val infer_add_case :
           Environments.TMap.key ->
           P_data.p_case ->
           Environments.scheme_env ->
           Environments.TyMap.key list ->
           Environments.sub ->
           Environments.i_type -> Environments.sub * Environments.i_term

(*> CPC *)
val unify_for_cpc : Environments.sub ->Environments.sub ->
                        Environments.i_type -> Environments.i_type -> Environments.sub
(*< CPC *)

