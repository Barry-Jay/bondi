(* Module [Datatype]: datatype definition *)

(* Internal and exported syntactic sugar *)

(* deleting all representations from revision 148 
   and putting them in represnent.ml *) 


open List
open Format
open Datum 
open P_data
open Environments
open Infer
open Eval

let rec field_tyvars = function (* ignoring fields of function type *) 
  | TyV (tv,_) -> [tv]
  | TyC _ (* (tv,n) *) -> []
  | ApplyF (g,f)  -> append (field_tyvars g) (field_tyvars f) 
  | ChoiceF _ (* (g,f) *)
  | SuperF  _ (* (g,f) *)
  | Funty _ (* (g,f) *) -> [] 
  | Linty ty
  | Ref ty 
  | Array ty -> field_tyvars ty 
  | Quant(x,ty) -> list_remove x (field_tyvars ty)
;;


let initial_types = ["Int";"Float";"Bool";"Char";"String";"Unit"; "Top";"Socket";"Host"] 
(* What is the relationship of these to the datum types? I've added Socket and Host *)   

(*** local formatting *) 

let format_parsed_term identifier term = 
  format_p_term identifier ;
  ps " has parse tree "; 
  print_newline();
  format_p_term term;
  flush stdout ;
  print_newline()

(*
let format_inferred_term term = 
  ps "Inferred term : ";
  print_newline();
  format_term term;
  print_newline()
*)

let format_declaration str ty = 
  if get_mode "types" = Show_on
  then 
    begin
      ps str;
      ps ": ";
      format_type true ty;
      print_newline();
      flush stdout 
    end 

let rec doprint = function 
    Funty _ 
  | Ref _  
  | TyC(TyVar "Unit",_) 
  | ApplyF(TyC(TyVar "Array",_),_) -> false 
  | Linty ty -> doprint ty 
  | (* ty *) _ -> true
;;

let format_declared_value ty x v =
  if doprint ty
  then 
    begin
      ps x; 
      ps " = ";
      print_flush();
      print_value v;
      print_newline()
    end
;;


(*** declare term *)

let declare is_attribute identifier source =


  let ctr =   
    match is_attribute with 
      Method -> 0 
    | _ ->  !declaration_counter 
  in 

  if (get_mode "parse" = Show_on)
  then format_parsed_term identifier source ;

  let (theString,expectedTy)  = 
    match identifier with 
      Ptvar x -> (x,TyV(nextTypeVar(),0))
    | Ptyped(Ptvar x,ty) -> (x, convert_type ty)
    | _ -> pTermError [identifier] "is not an identifier"
  in 
  let (inferredTerm,inferredType,inferredSub) = 
    match is_attribute with 
      Linear -> 
	let (sub3,u3,_,_,uty3) = 
	  inf_linear source 
	    TMap.empty [] TMap.empty (Some []) idSub (Some expectedTy) Linear
	in 
	let uty4 = applySub sub3 uty3 in 
	begin 
	  match uty4 with 
	  | Funty(pty,sty) -> 
	      let aux b x = b && mem x (freeTyVars idSub sty) in 
	      if fold_left aux true (freeTyVars idSub pty) 
	      then (u3,uty4,sub3)
	      else typeError [uty4] "is not the type of a linear term" 
	  | _ ->  (u3,uty4,sub3)
	end
    | Method -> 
	let (t1,ty1,sub1) = infer source expectedTy in 
	begin 
	  match ty1 with 
	    Funty(pty,sty) when is_simple_method_type [] pty sty -> 
	      (t1,funty pty sty,sub1) 
	  | _ -> typeError [ty1] "is not a method type" 
	end
    | Simple |Recursive | Extensible | Discontinuous -> infer source expectedTy 
  in 
  globalRefVarSub := 
    TyMap.fold 
      (fun x ty sub -> TyMap.add x (applySub inferredSub ty) sub) 
      !globalRefVarSub 
      TyMap.empty ;
  if get_mode "infer" = Show_on
  then peek inferredTerm "the inferred term"; 
  if (get_mode "declaration" = Show_on)
  then format_declaration theString inferredType; 

  if get_mode "eval" = Show_off
  then pf "no evaluation done" 
  else 
      let (theScheme,refVars) = clos_ty_with_refVars idSub TMap.empty inferredType in 
      let theVal = evaluate inferredTerm in 
      let theValue =    
	match is_attribute with
        | Extensible | Method | Discontinuous -> Vext (ref theVal)
	| _ -> theVal
      in 
      let closed = (theValue,(is_attribute,theScheme,refVars != [])) 
      in
      envAdd (Var theString) ctr closed globalVEnv; 
      globalRefVarSub := 
        fold_left (fun sub x -> TyMap.add x (TyV(x,0)) sub) !globalRefVarSub refVars; 
      format_declared_value inferredType theString theValue;

;;



(*** adding cases *) 

let add_case_method m case sch =  

  let (sub1,added_case) = infer_add_case (Var m) case TMap.empty [] idSub (TyC(TyVar "Unit",0)) in 
  let _ = evaluate added_case in 
  let default_sch = applySub sub1 sch in 
  let case_sch,res_sch = 
    match added_case with 
    | Addcase(_,_,Some ty1) -> 
	let sch1 = clos_ty idSub TMap.empty ty1 in 
	(sch1,ChoiceF(sch1, default_sch))
    | _ -> (default_sch, default_sch) 
  in 
  ps ( m ^ ": "); 
  format_type true (inst_tyscheme case_sch);
  pf "";
  res_sch 
;;


let add_decl is_att thefun pattern pty_opt body = 
  try 
    let (_,(default,(att,sch0,hasRefVar))) =  envFind 0 (Var thefun) globalVEnv in 
    let sch = 
      if hasRefVar
      then applySub !globalRefVarSub sch0
      else sch0
    in 
    if is_att == att
    then 
      let sch2 = add_case_method thefun (None,pattern,pty_opt,body) sch in 
(*
peek_type sch0 "sch0";
peek_type sch "sch";
peek_type sch2 "sch2";
*)
      match is_att with 
	Method -> envAdd (Var thefun) 0 (default,(Method,sch2,hasRefVar)) globalVEnv  (*  !declaration_counter ?? *) 
      | _ ->  () 

    else termError [Tvar (Var thefun,0)] "cannot be extended" 
 
  with Not_found -> 
 declare is_att (Ptvar thefun) (Pcases([None,pattern,pty_opt,body])) 

;;

let add_outer_decl thefun pattern pty_opt body =     
  let (_,(_,(att,_,_))) =  
    try envFind 0 (Var thefun) globalVEnv 
    with Not_found -> termError [Tvar (Var thefun,0)] "is not recognised" 
  in
  add_decl att thefun pattern pty_opt body 
  
let rec pattern_constructors
 = function

    Pconstructor x -> TVarSet.singleton (Var x)
  | Papply(p1,p2) 
  | Poper("as",[p1;p2]) -> TVarSet.union (pattern_constructors p1) (pattern_constructors p2)
  | Ptyped(_,Pconstant str) 
  | Ptyped(_,Pnestedclass(str,_,_)) -> TVarSet.singleton (Var str)
  | _ -> TVarSet.empty 
;;

let add_case_function constructors (x,((* theta *) _,p,ty_opt,s)) = 

  let cs = pattern_constructors p 
  in 
  if TVarSet.inter cs constructors == TVarSet.empty 
  then 
    match envFind 0 (Var x) globalVEnv with 
    | (_,(_,(Discontinuous,_,_)))  -> add_outer_decl x p ty_opt s 
    | _ -> basicError "added cases must use a new constructor"
  else add_outer_decl x p ty_opt s 


(*** declare type *)

let declare_type_synonym ident ty0 =

  if mem ident initial_types then typeError [TyC(TyVar ident,0)] "cannot be re-declared" ;

  let ctr = !declaration_counter
  and identifier = TyVar ident 
  and  ty = convert_type ty0 in 
  let f tv b = b&& TyMap.mem tv !globalTyEnv in 
  if fold_right f (freeTyVars idSub ty) true 
  then gTyEnvAdd identifier ctr (Synonym ty) 
  else typeError [ty] " has free variables in type declaration" ;

  if (get_mode "declaration" = Show_on)
  then 
    begin
      ps "type " ;
      format_untidy_tyvar identifier ; 
      ps " = ";
      format_type false ty;
      print_newline()
    end
;;


let is_primitive = function 
             (* fragile!! Primitive types must not be re-defined *)
    "Pair" 
  | "Evr"
  | "Ths"
  | "Ok" 
  | "ParamPair"
  | "Nest" 
  | "Tag" -> true
  | _ -> false
;;


let declare_function_type (tyv,ctr,decs) = 


  let abstractors = ref TVarSet.empty 
  in 
  let apF_with_tyvars (ty1,tyvs) ty2 = 
    let ty3 =  convert_type ty2 in 
    (apF ty1 ty3, append (freeTyVars idSub ty3) tyvs)
  in 
  let aux (params,abstrs0) = 

    let (dty,paramvars) = 
      fold_left apF_with_tyvars  (convert_type (Pconstant tyv),[]) params in 

    let aux0 (abs,frs)  =
      let fty = fold_right (fun fr ty -> funty (convert_type fr) ty) frs dty in

      let fvs = freeTyVars idSub fty in 
      let is_linear = 
	fold_right (fun x b -> b && mem x paramvars) fvs true
      in 
      let status = if is_linear then Linear else Simple in 

      if (get_mode "declaration" = Show_on)
      then format_declaration abs fty; 


      let abs_ty=clos_ty idSub TMap.empty fty 
(* miseese some vars 
fold_right (fun x ty -> Quant(x,ty)) paramvars fty
*)
      in 
      let ctr2 = 
	if is_primitive abs
	then 0 
	else ctr 
      in 
      envAdd (Var abs) ctr2 (abs_ty,status) globalCEnv;
      abstractors := TVarSet.add (Var abs) !abstractors 
    in 
    List.iter aux0 abstrs0
  in 
  List.iter aux decs;
  !abstractors 
;;


(*** representations for structure polymorphism  *)


let extract pty fr0 = 
let fr = convert_type fr0 in
  match pty with 
    PtyV x -> 
      begin
	if not (List.mem x (freeTyVars idSub fr))
	then (apF (convert_type (pconstTy "Konstant")) fr,zcvar "Evr") 
	else 
	  match fr with 
	    TyV _ -> (convert_type (pconstTy  "Identity"),zcvar "Ths")
		
	  | ApplyF(fr1,fr2) when not (mem x (freeTyVars idSub fr1)) -> 
	      begin
		match fr2 with 
		  TyV(y,_) when y = x -> (apF (convert_type (pconstTy "Okay")) fr1, zcvar "Ok")
		| ApplyF(fr3,TyV(y,_)) 
		  when not (mem x (freeTyVars idSub fr3)) && y = x -> 
		    (apF2 (convert_type (pconstTy "Nested")) fr1 fr3, zcvar "Nest")
		| _  -> typeError [fr] "extract" 
	      end 
	  | _  -> typeError [fr] "extract" 
      end 
  | _  -> typeError [fr] "extract" 

 

let rec extract_all xs frs = 

 match frs with 
(* were they already reversed in the parser ?? *)
    [] ->  (apF  (convert_type (pconstTy "Konstant")) (cvar "Unit"),Apply(zcvar "Evr",t_un),[])
  | [fr] -> 
      let (g,c) = extract xs fr in 
      let x = nextvar() in 
      (g,Apply(c,Tvar(x,0)), [x])
  | fr1::frs0 -> 
      let (g1,c1,tvs) = extract_all xs frs0 in 
      let (g0,c0) = extract xs fr1 in 
      let x = nextvar() in 
      (apF2 (convert_type (pconstTy "ParamProduct")) g0 g1, 
       Apply(Apply(zcvar "ParamPair",Apply(c0,Tvar(x,0))),c1),x::tvs)
;;

let extract_all_all decs = 
  let aux  (params,abstrs) = 
    match rev params with   (* simplify? produce the_functor here ? *) 
      [] -> basicError "extract"
    | args :: _ -> 
	(List.map convert_type params, 
	 List.map (fun (abs,frs) -> (abs,frs,extract_all args frs)) abstrs) 
  in 
  List.map aux decs
;;


let declare_data_type (tyv,ctr,decs) =

  let abstractors = ref TVarSet.empty 
  in 
  let funtyc pty ty = funty (convert_type pty) ty in 

  let aux (params,abstrs0) = 

    let dty = fold_left apF (convert_type (Pconstant tyv)) params in 

    let aux0 (abs,frs,(g,c0,tvs))  = 

      let abs_ty = (fold_right funtyc frs dty) in 

      if (get_mode "declaration" = Show_on)
      then format_declaration abs abs_ty; 

      let abs_sch = clos_ty idSub TMap.empty abs_ty in 
      if is_primitive abs
      then  
	begin
	  envAdd (Var abs) 0 (abs_sch,Linear) globalCEnv;
	  abstractors := TVarSet.add (Var abs) !abstractors 
	end
      else 
	begin
	  let the_functor = 
	    match dty with 
       	      ApplyF(fr,_) -> fr 
	    | _ -> typeError [dty] "is not an application" 
	  in 

       	  let nm_str = abs ^ "_name" in
       	  let nm_var = Var nm_str in 
       	  let nm = Tconstructor (Var nm_str,ctr) in 
       	  let nm_ty = (funty g the_functor) in 
       	  let nm_sch = clos_ty idSub TMap.empty  nm_ty in 
	  let pat = 
	    fold_left (fun x y -> Apply(x,Tvar(y,ctr)))
	      (Tconstructor (Var abs,ctr)) tvs in 
	  let body0 =  Apply(Apply(Tconstructor (Var "Tag",0),nm),c0) in 
	  let body = let f = nextvar() in Lam(f,Apply(Tvar(f,0),body0)) in  

	  let new_case = evaluate (Case(None,pat,body)) in 
	  let (dv,snd_arg) = snd(envFind 0 (Var "deconstruct") globalVEnv) in 
	  envAdd (Var "deconstruct") 0 (Vchoice(new_case,dv),snd_arg) globalVEnv;

	  let new_case = evaluate (Case(None,body0,pat)) in 
	  let (dv,snd_arg) = snd (envFind 0 (Var "reconstruct") globalVEnv) in 
	  envAdd (Var "reconstruct") 0 (Vchoice(new_case,dv),snd_arg) globalVEnv;
 
	  envAdd nm_var ctr (nm_sch,Linear) globalCEnv;
       	  envAdd (Var abs) ctr (abs_sch,Linear) globalCEnv;
	  abstractors := TVarSet.add (Var abs) !abstractors 
	end 
    in 
    List.iter aux0 abstrs0
  in 
  List.iter aux decs;
  !abstractors
;;


let declare_type (str,decs,add_cases) =  
  if mem str initial_types then typeError [cvar str ] "cannot be re-declared";

  let ctr = !declaration_counter in 
  gTyEnvAdd (TyVar str) ctr (Synonym(TyC (TyVar str,ctr)));

  let abstractors = 
    try declare_data_type (str, ctr,extract_all_all decs) 
    with _ -> declare_function_type (str,ctr,decs) 
  in 
  List.iter (add_case_function abstractors)  add_cases   



    (*** class declarations *) 




let split_fields (tys,fds,ctr) tv = 
  match tv with 
    Ptyped(Ptvar label,pty) -> 
      (pApF(pApF (Pconstant "Binprod") (Pref pty)) tys,(label,pty,label^"_") ::fds,
       ctr+1)
  | _ -> pTermError [tv] "is inappropriate as attribute label" 


let void = Apply(zcvar "Ref", Twildcard "void")

let rec nullify = function 
    0 ->   Tconstructor (Var "Un",0)
  | 1 -> void
  | n -> Apply(Apply(zcvar "Pair", void),nullify (n-1))



let declare_class cl_str zeds super_opt (fds,mds) add_cases = 

  let ctr = !declaration_counter in 
  let cl_tyv = cl_str ^ classTyString in 
  let restparam  = PtyV(nextTypeVar()) in 
  let cty = Pnestedclass(cl_str,map (fun x -> PtyV x) zeds, restparam) in 
  let (argtys1,fds1,_) = 
    match rev fds with 
      [] -> (Pconstant "Unit",[],0)
    | [Ptyped(Ptvar label,pty)] -> (Pref pty,[(label,pty,label^"_")],1)
    | Ptyped(Ptvar label,pty) :: tvs -> 
	fold_left split_fields (Pref pty,[(label,pty,label^"_")],1) tvs
    | tv :: _  -> pTermError [tv] "is inappropriate as attribute label" 
  in 

  let pat_pair p (_,_,x)  = ap2 (Pconstructor "Pair") (Ptvar x) p in 
  let fd_pat = 
    match rev fds1 with 
      [] ->  Pconstructor "Un"
    | [(_,_,x)] -> Ptvar x
    | (_,_,x) :: fds2 -> fold_left pat_pair (Ptvar x) fds2 
  in 
  let constructorString = cl_str  in 
  let local_pat x = ap2 (Pconstructor constructorString) x fd_pat 
  and local_new x = Apply(Apply(Tconstructor(Var constructorString,ctr),x),nullify (length fds))
  in 
  let (class_info,pattern,root_class) = 
    match super_opt with 
      None -> Class(None,local_pat,local_new,length zeds),local_pat (Pwildcard ""),true
    | Some super_str -> 
	try 	
	  match gTyEnvFind ctr (TyVar super_str) with 
	  | (super_n,Class(_,whole_pattern,whole_new,refpositions)) -> 
	      let pattern_maker x = whole_pattern (local_pat x) in 
	      let new_term x = whole_new (local_new x)
	      in  
	      Class(Some (TyVar super_str,super_n),pattern_maker,new_term,refpositions),pattern_maker (Pwildcard ""),false
	  | _ -> typeError [TyC(TyVar super_str,ctr)] " is not a known class" 

	with _ -> typeError [TyC(TyVar super_str,ctr)] " is not a known class" 
  in

  let class_info_temp = 
    if root_class 
    then 
      match class_info with 
	Class(None,local_pat,local_new, (* k *) _) -> Class(None,local_pat,local_new,0)
      | _ -> class_info
    else class_info
  in 
  gTyEnvAdd (TyVar cl_str) ctr class_info_temp;

(* this test causes problems for container.bon so the latter must be modified. *)


let delete_field_tyvars zeds (_,ty,_) = 
  let ty1 = convert_type ty in 
  fold_right list_remove (field_tyvars ty1) zeds 
in 


if root_class && (fold_left delete_field_tyvars zeds  fds1 != [])
then 
  begin
    let env = !globalTyEnv in 
    globalTyEnv := TyMap.add (TyVar cl_str) (tl (TyMap.find  (TyVar cl_str) env)) env;
    basicError (cl_str ^ " has generic type variables that are not controlled by fields")
  end 
;



gTyEnvAdd (TyVar cl_str) ctr class_info; 
gTyEnvAdd (TyVar cl_tyv) ctr (Synonym(TyC (TyVar cl_tyv,ctr)));


  let dty = ApplyF(fold_left apF (TyC(TyVar cl_tyv,ctr)) (map (fun x -> TyV(x,0)) zeds),convert_type restparam) in 
  let fty = funty (convert_type restparam)  (funty (convert_type argtys1) dty) 
  in 
  envAdd (Var constructorString) ctr (clos_ty idSub TMap.empty fty,Linear) globalCEnv;

   pf ("class "^cl_str^" {") ; 



  let add_field (label,ty,x) = 
    f_counter := "";
    add_decl Method label pattern (Some cty) (Ptyped(Ptvar x,Pref ty)) 
  in
  List.iter add_field fds1 ;

  let pattern_as_this = Poper("as",[pattern;Ptvar "this"]) in 

  let add_method (status,label,t) = 
    f_counter := "";
    match status with 
    | Method ->  add_decl status label pattern_as_this (Some cty) t
    | Recursive -> let full_label = cl_str^"."^label in 
                   declare status (Ptvar full_label) (Plet(status,(Ptvar full_label),t,(Ptvar full_label)))
    | Discontinuous -> let full_label = cl_str^"."^label in 
                   declare status (Ptvar full_label) (Plet(status,(Ptvar full_label),t,(Ptvar full_label)))
    | _ ->  let full_label = cl_str^"."^label in 
            declare status (Ptvar full_label) t
  in
  List.iter add_method mds;

  List.iter 
   (f_counter := "";add_case_function (TVarSet.singleton (Var constructorString))) 
   add_cases;
pf "}"
;;



