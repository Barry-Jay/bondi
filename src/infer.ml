open List
open Datum
open P_data
open Environments

(*** precision allows the same algorithms to be used for solving 
     type equations and inqualities. *)

type precision = Exact | LessThan 


(*** instantiating and closing types.
     These freshen bound type variables *) 

let rec inst_tyscheme_with_bvars  = function
   | Quant(x,ty) -> 
      let bv = nextTypeVar() in 
      let sub = TyMap.add x (TyV(bv,0)) idSub in 
      let (ty1,bvs1) = inst_tyscheme_with_bvars ty in 
      (applySub sub ty1,bv :: bvs1)
  | ty -> (ty,[]) 

let inst_tyscheme ty = fst (inst_tyscheme_with_bvars ty) 


let clos_ty_with_refVars sub sEnv ty = 
  let refTyVars = freeRefTyVars (applySub sub ty) in 

 (*

format_tyvarlist refTyVars ; print_flush(); 
pf "is refTyVars";
format_tyvarlist(freeTyVars sub ty) ;print_flush(); 
pf "is free tyVars"; 
*)
  let bTyVars = 
    fold_right list_remove (freeTyVarsInSEnv sub sEnv) (
    fold_right list_remove refTyVars (freeTyVars sub ty)) in 
  let (sub1,tyvs1) = freshen_tyvars bTyVars in 
  let sub2 = composeSubs sub1 sub 
  in 
  (fold_right (fun x y -> Quant(x,y)) tyvs1 (applySub sub2 ty),refTyVars)

let clos_ty sub sEnv ty = fst (clos_ty_with_refVars sub sEnv ty)

(* delete ??

let clos_ty_not_ref sub sEnv ty = 
  let refTyVars = fold_right list_remove (freeTyVarsInSEnv sub sEnv) (freeTyVarsInRef sub ty) 
  in 
  if refTyVars != [] then typeError [ty] "has unconstrained polymorphic references";
  let bTyVars = 
    fold_right list_remove (freeTyVarsInSEnv sub sEnv) (freeTyVars sub ty) in 
  let (sub1,tyvs1) = freshen_tyvars bTyVars in 
  let sub2 = composeSubs sub1 sub 
  in 
  fold_right (fun x y -> Quant(x,y)) tyvs1 (applySub sub2 ty)
 
*)


(*** unification and matching 

   ` Unification should be rewritten to take advantage of the latest algorithms. 
*)

(* addSubCheck adds a new binding to a substitution, 
   Check that no occurence error occurs, 
   then use sequential composition of subs, 
   which is correct but inefficient. *) 

let addSubCheck sub tyv ty = 
  let tyvs = freeTyVars sub ty in 
  if  List.mem tyv tyvs
  then typeError [TyV (tyv,0); ty] "produce an occurence error in unification"
  else composeSubs (TyMap.add tyv ty TyMap.empty) sub 
;;

(* the unification algorithm *)

let rec unify_p cpc fixed precision sub ty0 ty1 = 
  (* CPC Change: cpc = if this is a CPC unification
     fixed = fixed tyvars that cannot be replaced, 
     but other variables may be mapped to them. 
     unlike quantified variables that must be completely avoided.
  *) 

  if get_mode "types" = Show_off
  then sub 
  else 
    let ty2 = applySub sub ty0
    and ty3 = applySub sub ty1 
    in
   match (ty2,ty3) with

          (* Top is top *)

    | _,TyC(TyVar "Top",_) when precision = LessThan -> sub   

	  (* ty2 is a variable *) 

    | (TyV _, TyV _) when  ty2 = ty3 ->  sub 

	  (* handling problems with fixed variables *) 

    | (_,TyV (x,_)) when not (mem x fixed) ->  addSubCheck sub x ty2

    | (TyV(x,_), _) when mem x fixed -> 
	typeError [ty2] "is fixed in unification" 

    | (TyV (x,_),_) when precision = Exact -> addSubCheck sub x ty3


	  (* subunification:
	     To solve X < F Top (respectively, X< P -> Top)
	     map X to F Y (respectively, P -> Y) for some fresh Y. 
	     Otherwise default to Exact unification *)
 
    | TyV (x,_), ApplyF(_,TyV(_,_)) -> addSubCheck sub x ty3
    | TyV (x,_), ApplyF(g1,f1) -> 
	let ty = TyV(nextTypeVar(),0) in 
	let sub1 = addSubCheck sub x (ApplyF(g1,ty)) in 
	unify_p cpc fixed precision sub1 ty f1 
    | TyV (x,_), Funty(_,TyV _) -> addSubCheck sub x ty3
    | TyV (x,_), Funty(g1,f1) -> 
	let ty = TyV(nextTypeVar(),0) in 
	let sub1 = addSubCheck sub x (Funty(g1,ty)) in 
	unify_p cpc fixed precision sub1 ty f1 
   | (TyV (x,_),_)  -> addSubCheck sub x ty3

	  (* structured types *)

    | TyC _, TyC _ when ty2 = ty3 -> sub
    | ApplyF(g0,f0), ApplyF(g1,f1)
    | Funty(g0,f0), Funty(g1,f1) -> 
	unify_p cpc fixed precision 
	  (unify_p cpc fixed Exact sub g0 g1) f0 f1
    | ChoiceF(g0,f0), ChoiceF(g1,f1) when precision = Exact -> 
	unify_p cpc fixed Exact 
	  (unify_p cpc fixed Exact sub g0 g1) f0 f1
    | SuperF(g0,f0), SuperF(g1,f1) when precision = Exact -> 
	unify_p cpc fixed Exact 
	  (unify_p cpc fixed Exact sub g0 g1) f0 f1
    | SuperF((* g0 *) _,f0), _ when precision = LessThan -> unify_p cpc fixed LessThan sub f0 ty3
    | (Linty f1,Linty f2) -> unify_p cpc fixed Exact sub f1 f2
    | (Linty f1,_) when cpc -> unify_p cpc fixed precision sub f1 ty3
    | (Ref f1, Ref f2) 
    | (Array f1, Array f2) -> unify_p cpc fixed Exact sub f1 f2 
    | (Quant(x1,f1), Quant(x2,f2)) ->
	let (sub1,x) = freshen_tyvar2 x1 x2 in 
	let sub2 = unify_p cpc (x::fixed) precision sub (applySub sub1 f1) (applySub sub1 f2) in 
	if avoid x sub2 
	then sub2
	else typeError [ ty2; ty3] "quantified types don't unify"
    | _ -> typeError [ ty2; ty3] "don't unify"
;;

      (* The usual versions of unification *) 

let unify fixed sub ty0 ty1 = unify_p false fixed Exact sub ty0 ty1 
 
let subunify fixed sub ty0 ty1 = unify_p false fixed LessThan sub ty0 ty1 


      (* tymatch is a one-sided form of unification,
         like unification except that 
	 it specifies the variables delta available for matching, 
	 instead of the fixed ones. 
	 These must not appear outside of the type being matched. 
       *) 

let rec tymatch delta sub ty0 ty1 = 
  if get_mode "types" = Show_off
  then sub 
  else 
 
  let ty2 = applySub sub ty0
  and ty3 = applySub sub ty1 in

  match (ty2,ty3) with
  | TyV _, TyV _ 
  | TyC _, TyC _ when ty2 = ty3 -> sub 
  | (_,TyV (tyv3,_)) when List.mem tyv3 delta ->  TyMap.add tyv3 ty2 sub 
              (* no need to check since tyv2 is fresh for ty2 and sub *) 
  | (TyV (tyv2,_),_) when List.mem tyv2 delta -> TyMap.add tyv2 ty3 sub 
              (* no need to check since tyv2 is fresh for ty3 and sub *) 
  | (ApplyF(g1,f1), ApplyF(g2,f2))
  | (ChoiceF(g1,f1), ChoiceF(g2,f2))
  | (SuperF(g1,f1), SuperF(g2,f2))
  | (Funty(g1,f1), Funty(g2,f2)) -> 
      tymatch delta (tymatch delta sub g1 g2) f1 f2
  | (Linty f1, Linty f2)
  | (Ref f1, Ref f2) 
  | (Array f1, Array f2) -> tymatch delta sub f1 f2 
  | _ ->  typeError [ ty2; ty3] "don't match"
;;

let rec tysubmatch delta sub ty0 ty1 = 


  (* tysubmatch is a one-sided form of sub-unification.
     delta is the set of variables available for matching.
    *) 
 
  if get_mode "types" = Show_off
  then sub 
  else 

  let ty2 = applySub sub ty0
  and ty3 = applySub sub ty1 in

  match (ty2,ty3) with
  | _,TyC(TyVar "Top",_)  -> sub
  | ApplyF(g0,f0),ApplyF(g1,f1) 
  | Funty(g0,f0),Funty(g1,f1) -> tysubmatch delta (tymatch delta sub g0 g1) f0 f1
  | SuperF(_,f0),_  -> tymatch delta sub f0 ty3
  | _,_ -> tymatch delta sub ty2 ty3 
;;


let rec relate sub ty0 ty1 = 
  (* find a substitution that relates ty0 and ty1, 
     which are assumed separated.
     This could be done by adding a third form of precision, 
     but the code becomes even more complex. *) 

  if get_mode "types" = Show_off
  then sub 
  else 

  let ty2 = applySub sub ty0
  and ty3 = applySub sub ty1 in

  match (ty2,ty3) with
  | _,TyC(TyVar "Top",_)  
  | TyC(TyVar "Top",_),_ -> sub
  | ApplyF(g0,f0),TyV(tyv,_) 
  | TyV(tyv,_), ApplyF(g0,f0) -> 
      let y = TyV(nextTypeVar(),0) in 
      let sub1 = TyMap.add tyv (ApplyF(g0,y)) sub in 
      relate sub1 f0 y 
  | (ApplyF(g1,f1), ApplyF(g2,f2))
  | (Funty(g1,f1), Funty(g2,f2)) -> 
      let sub1 = unify [] sub g1 g2 in 
      relate sub1 f1 f2 
(* what about choiced types? *) 
  | _,_ -> unify [] sub  ty2 ty3 
;;



(*** case types *)

let is_case_type delta pty sty = 

  (* delta contains possible local tyvars.
     Every tyvar that is free in sty and in delta 
     must be free in pty *) 

  let ptyv = freeTyVars idSub pty 
  and styv = freeTyVars idSub sty 
  in
  let aux b x = b && if mem x delta then mem x ptyv  else true
  in 
  fold_left aux true styv 
;;




(*** method types *) 


let is_simple_method_type delta pty sty = 
  (* delta pty sty must yield a case type.
     Also, any covariant  type variable of pty that is free in sty 
     must be a covariant  type variable of sty. 
   *)
  
  let styv = freeTyVars idSub sty 
  and potyv = covTyVars idSub pty 
  and sotyv = covTyVars idSub sty 
  in
  let aux b x = b && if mem x styv then mem x sotyv else true 
  in 
  fold_left aux (is_case_type delta pty sty) potyv 
;;

let rec dle sEnv sub aty rty = function 
    (* dle is << or type specialisation *) 

    ChoiceF(n,m) 
  | SuperF(n,m) -> 
      dle sEnv sub aty rty n && (* check the first alternative *) 
      dle sEnv sub aty rty m    (* and the second alternative *) 
  | mty -> 
      match inst_tyscheme mty with         
	Funty(argty2,resty2) -> 
	  let subOpt = 
	    (* try to relate the argument types *) 
	    try Some (relate sub aty argty2)
	    with _ -> None 
	  in 
	  begin 
	    match subOpt with 
	      None -> true (* if the argument types can't be related then okay *) 
	    | Some sub1 -> (* if they can then ... *) 	 
		try 
		  let x = nextvar() in 
		  let sEnv_temp = TMap.add x (applySub sub1 aty,Simple) sEnv in 
		  let rty_scheme = clos_ty sub1 sEnv_temp rty in 
		  let (rty2,delta) = inst_tyscheme_with_bvars rty_scheme in
		  let _ = tysubmatch delta sub1 rty2 resty2 in true 

(* the line above does not allow for alpha-conversion of implicitly bound tyvars *) 

		with _  -> false 
	  end
      | _ -> false (* if mty is not a function type then no specialisation *) 
;;



let specialises sEnv sub delta aty rty mty = 
 
  is_simple_method_type delta aty rty &&
  dle sEnv sub aty rty mty
;;


let invoke_ty_by_matching sEnv sub uty mty  = 
  (* produces a substitution and a result type, 
     to which the substitution must be applied.
     It will not modify uty 
     *)

  match inst_tyscheme_with_bvars (clos_ty sub sEnv mty) with 
    Funty(pty,sty), delta -> (tysubmatch delta sub uty pty,sty)
  | _ -> typeError [mty] "is not a function or method type"
;;
	  

let rec invoke_ty sEnv sub uty mty  = 
  (* produces a substitution and a result type, 
     to which the substitution must be applied.
     If mty is a function type, 
     i.e. is a the last alternative,
     then any free vars of uty may be instantiated.
   *) 

  match mty with 
  | ChoiceF(mty1,mty2) -> 
      begin 
	try invoke_ty_by_matching sEnv sub uty mty1  
	with _ -> invoke_ty sEnv sub uty mty2 
      end
  | SuperF(mty1,mty2) -> 
      begin 
	match invoke_ty_by_matching sEnv sub uty mty2 with 
	| (sub1,sty1) -> 
	    try invoke_ty_by_matching sEnv sub uty mty1 
	    with _ -> (sub1,sty1)
      end
  | _ ->   
      match inst_tyscheme (clos_ty sub sEnv mty) with 
	Funty(pty,sty) -> (subunify [] sub uty pty,sty)
      | _ -> typeError [mty] "is not a function or method type"
;;








(*** type inference *)

  (* 
     sEnv provides type (schemes) for  term variables
     sub is a substitution 
     expectedTy is the expected type

     fixed contains fixed type variables. These increase below as follows:
      - let fixed1 = append delta1 fixed
              fixes the type variables of the pattern of a case 
      - let fixed1 = append (freeTyVars sub2 inst_ty) fixed
              fixes the type variables of a polymorphic argument in let rec 
      - let fixed2 = append (freeTyVars sub2 uty2) fixed
              fixes the tyvars of a linear argument 
      - let fixed2 = append delta fixed in 
              fixes the type variables of a polymorphic argument in an application 

*) 


 
(* constructors and datum constants appear in both linear terms  and terms *) 

let infer_constructor_with_delta x (* sEnv *) _ fixed sub0 expectedTy =
  let (n,(sch,status)) = 
    try envFind 0 (Var x) globalCEnv
    with Not_found -> termError [Tconstructor (Var x,0)] "is not recognised"
  in 
  let (ty1,delta1) = inst_tyscheme_with_bvars sch  in 
  let sub2 = subunify fixed sub0 ty1 expectedTy
  in 
    ((sub2,Tconstructor(Var x,n)),(delta1,status))

let infer_constructor x sEnv fixed sub0 expectedTy =
  fst (infer_constructor_with_delta x sEnv fixed sub0 expectedTy) 

let infer_datum d (* sEnv *) _ fixed sub0 expectedTy = 
  (subunify fixed sub0 (cvar (datum_type_string d)) expectedTy,Datum d)



let rec inf_linear p (sEnv: scheme_env) fixed tyEnv theta sub pty_opt status = 
  (* status to allow that the static pattern x y has x linear and y not *) 

  let (pty,delta0) = 
    match pty_opt with 
      None -> 
	let tyv = nextTypeVar() in 
	(TyV(tyv,0), [tyv]) 
    | Some ty ->  (ty, freeTyVars sub ty)
  in 	
  match p with 

  | Ptvar x -> 
      let x1 = Var x in 
      let binding = 
	match theta with 
	  Some theta1 -> List.mem x1 theta1
	| _ -> true 
      in 
      if binding 
      then 
	if TMap.mem x1 tyEnv 
	then termError [Tvar(x1,0)] "is a duplicate binding symbol" 
	else 
	  let tyEnv1 = TMap.add x1 (pty,status) tyEnv  in 
	  (sub,Tvar(x1,0),delta0,tyEnv1,pty)
      else 
	let (n,(ty,status1)) = 
	  try (0,TMap.find x1 sEnv) 
	  with Not_found -> 
	    try 
	      match envFind 0 x1 globalVEnv with 
		(n,(_,(status2,sch,hasRefVar))) -> 
		  if hasRefVar 
		  then (n,(applySub !globalRefVarSub (inst_tyscheme sch),status2))
		  else (n,(inst_tyscheme sch,status2))
	    with _ -> (0,(pty,Simple))   (* pty is a dummy argument *) 	  
	in 
	begin
	  match status1 with 
	    Linear -> (sub,Tvar(x1,n),[],tyEnv,ty) 
	  | _ ->  termError [Tvar(x1,0)] "not a linear variable" 
	end


  | Pconstructor x -> 
      let ((sub1,c),(delta1, _)) = infer_constructor_with_delta x sEnv [] sub pty 
      in 
      (sub1,c,delta1,tyEnv,pty)

  | Pdatum d -> 
      let (sub1,c) = infer_datum d sEnv [] sub pty 
      in 
      (sub1,c,[],tyEnv,pty)

  | Pwildcard str -> 
    let wild = Twildcard str in 
    let x = TyV(nextTypeVar(),0) in 
    let principal_type = 
	match str with 
	  "" -> x
	| "Int" 
	| "Float" 
	| "Char" 
	| "String"  -> cvar str 
	| "ref"  -> Ref x
	| "array"  -> Array x
	| _ -> basicError ("_" ^ str ^ " is not a wildcard" )
    in 
    
    (subunify [] sub principal_type pty,wild,delta0,tyEnv,pty)

  | Papply(p1,p2) -> 
      let argty = TyV(nextTypeVar(),0) in 
      let (sub1,q1,delta1,tyEnv1,pty1) = inf_linear p1 sEnv fixed tyEnv  theta sub  (Some (funty argty pty)) Linear in 
      let (sub2,q2,delta2,tyEnv2,pty2) = inf_linear p2 sEnv fixed tyEnv1 theta sub1 (Some argty) Simple in 


      begin
	match applySub sub2 pty1 with 
	| Funty(uty,sty) -> 
	    let sub3 = subunify [] sub2 uty pty2
	    in  
	    (sub3,Apply(q1,q2),append delta1 delta2, tyEnv2,sty) 
	| _ -> 
	    let z = nextTypeVar() in 
	    let rty = TyV(z,0) in 
	    let sub3 = unify [] sub2 (funty pty2 rty) pty1 
	    in
	    (sub3,Apply(q1,q2),append delta1 delta2, tyEnv2,rty) 
      end 

  | Poper("as",[p2;p1]) -> 
      let (sub1,q1,delta1,tyEnv1,pty1) = 
	inf_linear p1 sEnv fixed tyEnv theta sub  (Some pty) status in 
      let (sub2,q2,delta2,tyEnv2,pty2) = 
	inf_linear p2 sEnv fixed tyEnv1 theta sub1  (Some pty) status in 
      let sub3 = unify [] sub2 pty1 pty2 in 
      (sub3,Oper("as",[q2;q1]),append delta1 delta2,tyEnv2,pty1)

  | Poper("view",[t;q]) -> 
      let fixed1 = append delta0 fixed in 
      let qty = TyV (nextTypeVar(),0) in
      let (sub1,t1) = inf t sEnv fixed1 sub  (funty pty qty) in 
      let (sub2,q2,delta2,tyEnv2,_) = 
      	inf_linear q sEnv fixed TMap.empty theta sub1  (Some qty) status 
      in 
      (sub2,Oper("view",[t1;q2]),delta2,tyEnv2, pty)

 | Poper("where",[q;test]) -> 
      let (sub1,q1,delta1,tyEnv1,pty1) = 
      inf_linear q sEnv fixed tyEnv theta sub  (Some pty) status in 
      let fixed1 = append delta1 fixed in 
      let (sub2,t2) = inf test tyEnv1 fixed1 sub1 (cvar "Bool") in
      (sub2,Oper("where",[q1;t2]),delta1,tyEnv1,pty1)

  | Ptyped(p0,(Pnestedclass (str,_,_))) -> 
      if mem str ["Int"; "Float"; "Char" ; "String"] 
      then 
	let the_ty = TyC(TyVar str,0) in 
	let (sub1,p1,delta1,tyEnv1,pty1) = inf_linear p0 sEnv fixed tyEnv theta sub (Some pty) status in 
	let sub2 = unify [] sub1 pty1 the_ty
	in (sub2,Oper("as",[p1;Twildcard str]),delta1,tyEnv1,the_ty)
      else 
	let class_pat = pattern_of_class (TyVar str,!declaration_counter) (Pwildcard "")
	in 
	let class_ty = TyV (nextTypeVar(),0) in
	let (sub1,p1,delta1,tyEnv1,pty1) = inf_linear class_pat sEnv fixed tyEnv theta sub (Some class_ty) status 
	in 
	let sub2 = subunify [] sub1 pty1 pty in (* replaced fixed by [] here !? *) 
	let (sub3,p3,delta3,tyEnv3,pty3) = 
	  inf_linear p0 sEnv fixed tyEnv1 theta sub2 (Some (applySub sub2 pty1)) status  
	in 
	(sub3,Oper("as",[p3;p1]),append delta1 delta3, tyEnv3,pty3)


  | Plam(Ptvar x,p0) -> 
      let ty1 = TyV(nextTypeVar(),0) in 
      let ty2 = TyV(nextTypeVar(),0) in 
      let sub0 = unify [] sub (funty ty1 ty2) pty in        
      begin 
	match theta with 
	  None -> 


	    let (sub1,p1,delta1,tyEnv1,pty1) = inf_linear p0 sEnv fixed tyEnv theta sub0 (Some ty2) status 
	    in 
	    if TMap.mem (Var x) tyEnv1 
	    then  (sub1,Lam(Var x,p1),delta1,TMap.remove (Var x) tyEnv1,funty (applySub sub1 ty1) pty1)
	    else pTermError [p] "is not linear"
	| Some vars -> 
	    let (sub1,p1,delta1,tyEnv1,pty1) = inf_linear p0 sEnv fixed tyEnv (Some ((Var x):: vars)) sub0 (Some ty2) status in 
	    let argty = 
	      try fst(TMap.find (Var x) tyEnv1)
	      with Not_found -> pTermError [Ptvar x] "is a missing binding symbol"
	    in 
	    (sub1,Lam(Var x,p1),delta1,TMap.remove (Var x) tyEnv1,applySub sub1 (funty argty pty1))
      end

(* it is theoretically possible to allow linear cases, 
   but the benefits are not clear, so don't bother for now. 
   
     | Pcases [(None,p0,None,s0)] -> (* a single, static, case, without a type for the pattern  *) 

      let (sub1,p1,delta1,tyEnv1,pty1) = inf_linear p0 sEnv fixed TMap.empty None sub None 
      in 
      let (sub2,sty) = 
	match applySub sub1 pty with 
          Funty(uty,sty3) ->  
	    let sub3 = subunify [] sub1 pty1 uty in 
	    (sub3, sty3)
	| _ -> 
	    let sty3 = TyV(nextTypeVar(),0) in
	    let case_ty = funty pty1 sty3 in 
	    let sub3 = unify [] sub1 case_ty pty in 
	    (sub3,sty3)
      in 
      let theta2 = Some (TMap.fold (fun x _ xs -> x::xs) tyEnv1 [])
      in 
      let (sub4,s4,delta4,tyEnv4,sty4) =  inf_linear s0 sEnv fixed TMap.empty theta2 sub2 None 
      in 
      (sub4,Case(p1,s4),delta4,tyEnv4,funty pty1 sty4)
*)

  | _ -> pTermError [p] "is not linear"


and inf_linear_or_var p (sEnv: scheme_env) fixed tyEnv theta sub pty_opt status = 
  let (pty,delta0) = 
    match pty_opt with 
      None -> 
	let tyv = nextTypeVar() in 
	(TyV(tyv,0), [tyv]) 
    | Some ty ->  (ty, freeTyVars sub ty)
  in 	
  match p with 
 | Ptvar x -> 
      let x1 = Var x in 
      let binding = 
	match theta with 
	  Some theta1 -> List.mem x1 theta1
	| _ -> true 
      in 
      if binding 
      then 
	if TMap.mem x1 tyEnv 
	then termError [Tvar(x1,0)] "is a duplicate binding symbol" 
	else 
	  let tyEnv1 = TMap.add x1 (pty,status) tyEnv  in 
	  (sub,Tvar(x1,0),delta0,tyEnv1,pty)
      else 
	let (n,(ty, (* status1 *) _)) =
	  try (0,TMap.find x1 sEnv) 
	  with Not_found ->
	    try 
	      match envFind 0 x1 globalVEnv with 
		(n,(_,(status2,sch,hasRefVar))) -> 
		  if hasRefVar 
		  then (n,(applySub !globalRefVarSub (inst_tyscheme sch),status2))
		  else (n,(inst_tyscheme sch,status2))
	    with _ -> (0,(pty,Simple))   (* pty is a dummy argument *) 	  
	in 
	(sub,Tvar(x1,n),[],tyEnv,ty)

  | _ -> inf_linear p (sEnv: scheme_env) fixed tyEnv theta sub pty_opt status 



and inf = 
  (* 
     inf term (sEnv,fixed,constraints,sub,expectedTy) = (sub',term') 

     term 
     sEnv = scheme environment for free variables in the term
     fixed = tyvars to be fixed in substitution 
     sub = the initial type substitution
     expectedTy = the expected type 
     The arguments need not be  normal wrt the sub 
*)

function 

  | Ptvar x -> infer_var (Var x) 
  | Pwildcard str -> infer_wild str 
  | Pconstructor x -> infer_constructor x 
  | Pdatum d -> infer_datum d 
  | Poper ("eqcons",[f;x]) -> infer_eqcons f x 
  | Poper("cond",[b;s;t]) -> infer_cond b s t
  | Poper("prim2string",[t]) -> infer_prim2str t 
  | Poper("printstring",[t]) -> infer_printstring false t
  | Poper("printlnstring",[t]) -> infer_printstring true t
  | Poper("printchar",[t]) -> infer_printchar t 
  | Poper("isRef",[t]) -> infer_isRef t 
  | Poper("isArray",[t]) -> infer_isArray t 
  | Poper("seq",[u;v]) -> infer_seq u v
  | Poper("assign",[u;v]) -> infer_assign u v 
  | Poper("spawn",[t]) -> infer_spawn t
  | Poper("sleep",[t]) -> infer_sleep t
  | Poper("deref",[t]) -> infer_deref t 
  | Poper("while",[b;t]) -> infer_while b t 
  | Poper("lengthv",[v]) -> infer_lengthv v 
  | Poper("entry",[v;t]) -> infer_entry v t 
  | Poper(d,args) -> infer_oper d args 
  | Papply (f, x) -> infer_ap f x 
  | Plam(p,s) -> infer_lam p s
(*
  | Plin (p,s) -> infer_lin p s
*)
  | Pcases cs -> infer_cases cs 
  | Paddcase (x,case) -> infer_add_case (Var x) case 
  | Psubcase x -> infer_sub_case (Var x)
  | Plet(status,param,u,t) -> infer_let status param u t 
  | Ptyped (t1,ty) -> infer_typed t1 ty  
  | Pnew (tyv,tys) -> infer_new tyv tys
  | PnewArr (t1,t2) -> infer_new_array t1 t2 
  | Pinvoke (t,x,super) -> infer_invoke t x super

and infer_var x sEnv fixed sub0 expectedTy = 
  let (sch,symbol) = 
    try (fst (TMap.find x sEnv),Tvar(x,0))
    with Not_found ->
      try 
	match envFind 0 x globalVEnv with 
	  (_,(_,(Method, (* sch1 *) _,_)))  -> termError [Tvar (x,0)] "is an attribute"
	| (n,(_,(_,sch1,hasRefVar))) -> 
	    if hasRefVar 
	    then (applySub !globalRefVarSub sch1,Tvar(x,n))
	    else (sch1,Tvar(x,n))
      with Not_found -> termError [Tvar (x,0)] "is not recognised"
  in 
  let ty1 = inst_tyscheme (applySub sub0 sch) in 
  let sub2 = subunify fixed sub0 ty1 expectedTy
  in 
  (sub2,symbol)
  
and infer_wild str (* sEnv *) _ fixed sub0 expectedTy = 
 let wild = Twildcard str in 

    match str with 
      "" -> (sub0,wild)
    | "Int" 
    | "Float" 
    | "Char" 
    | "String"  -> (subunify fixed sub0 (cvar str) expectedTy,wild)
    | "ref"  -> 
	    let x = TyV(nextTypeVar(),0) in 
	    (subunify [] sub0 (Ref x) expectedTy,wild)
    | "array"  -> 
	    let x = TyV(nextTypeVar(),0) in 
	    (subunify [] sub0 (Array x) expectedTy,wild)
    | _ -> basicError ("_" ^ str ^ " is not a wildcard" )

and infer_cond b s t sEnv fixed sub0 expectedTy = 
  let (sub1,b1) = inf b sEnv fixed sub0 (cvar "Bool") in 
  let (sub2,s2) = inf s sEnv fixed sub1 expectedTy in 
  let (sub3,t3) = inf t sEnv fixed sub2 expectedTy in 
  (sub3,
   Apply(Choice 
	   (Case(None,Datum(Bool  true),s2),
	    Case(None,Datum(Bool false),t3)),
	 b1))

and infer_prim2str t sEnv fixed sub0 expectedTy = 
  let ty1 = TyV(nextTypeVar(),0) in 
  let (sub1,t1) = inf t sEnv fixed sub0 ty1 in 
  let sub2 = subunify fixed sub1 (cvar "String") expectedTy 
  in 
  (sub2,Oper("prim2string",[t1]))

and infer_printstring newl t sEnv fixed sub0 expectedTy = 
  let ty1 = cvar "String" in 
  let (sub1,t1) = inf t sEnv fixed sub0 ty1 in 
  let sub2 = subunify fixed sub1 (cvar "Unit") expectedTy in
  let oper = (if newl then "printlnstring" else "printstring")
  in
  (sub2,Oper(oper,[t1]))

and infer_printchar t sEnv fixed sub0 expectedTy = 
  let ty1 = cvar "Char" in 
  let (sub1,t1) = inf t sEnv fixed sub0 ty1 in 
  let sub2 = subunify fixed sub1 (cvar "Unit") expectedTy 
  in 
  (sub2,Oper("printchar",[t1]))

and infer_isRef t sEnv fixed sub0 expectedTy = 
  let ty1 = TyV(nextTypeVar(),0)  in 
  let (sub1,t1) = inf t sEnv fixed sub0 ty1 in 
  let sub2 = subunify fixed sub1 (cvar "Bool") expectedTy in
  (sub2,Oper("isRef",[t1]))

and infer_isArray t sEnv fixed sub0 expectedTy = 
  let ty1 = TyV(nextTypeVar(),0)  in 
  let (sub1,t1) = inf t sEnv fixed sub0 ty1 in 
  let sub2 = subunify fixed sub1 (cvar "Bool") expectedTy in
  (sub2,Oper("isArray",[t1]))


and infer_seq u v sEnv fixed sub0 expectedTy = 
  let uty = TyV(nextTypeVar(),0)  in 
  let (sub1,u1) = inf u sEnv fixed sub0 uty in 
  let (sub2,v2) = inf v sEnv fixed sub1 expectedTy in 
  (sub2,Oper("seq",[u1;v2]))

and infer_assign u v sEnv fixed sub0 expectedTy = 
  let dty = TyV(nextTypeVar(),0)  in 
  let (sub1,u1) = inf u sEnv fixed sub0 (Ref dty) 
  in 
    match inst_tyscheme (clos_ty sub1 sEnv (Ref dty)) with 
    | Ref dty1 -> 
	let (sub2,v2) = inf v sEnv fixed sub1 dty1 in 
	let sub3 = subunify fixed sub2 comm expectedTy
	in 
	(sub3,Oper("assign",[u1;v2]))
    | ty -> typeError [ty] "should be a reference type"
	  
and infer_spawn t sEnv fixed sub0 expectedTy =
  let ty1 = cvar "Unit" in
  let (sub1,t1) = inf t sEnv fixed sub0 ty1
  in
  let sub2 = subunify fixed sub1 (cvar "Unit") expectedTy
  in
  (sub2,Oper("spawn",[t1]))

and infer_sleep f sEnv fixed sub0 expectedTy =
  let ty1 = cvar "Float" in
  let (sub1,f1) = inf f sEnv fixed sub0 ty1 in
  let sub2 = subunify fixed sub1 (cvar "Unit") expectedTy in
  (sub2,Oper("sleep",[f1]))

and infer_deref t sEnv fixed sub0 expectedTy = 
  let (sub1,t1) = inf t sEnv fixed sub0 (Ref expectedTy)
  in 
  (sub1,Oper("deref",[t1]))

and infer_while b t sEnv fixed sub0 expectedTy = 
  let (sub1,b1) = inf b sEnv fixed sub0 (TyC(TyVar "Bool",0)) in 
  let (sub2,t2) = inf t sEnv fixed sub1 comm in 
  let sub3 = subunify fixed sub2 comm expectedTy
  in 
  (sub3,Oper("while",[b1;t2]))

and infer_lengthv v sEnv fixed sub0 expectedTy = 
  let ety = TyV(nextTypeVar(),0)  in 
  let (sub1,v1) = inf v sEnv fixed sub0 (Array ety)  in 
  let sub2 = subunify fixed sub1 (TyC(TyVar "Int",0)) expectedTy 
  in 
  (sub2,Oper("lengthv",[v1]))

and infer_entry v t sEnv fixed sub0 expectedTy = 
  let (sub1,t1) = inf t sEnv fixed sub0 (TyC(TyVar "Int",0)) in
  let ety = TyV(nextTypeVar(),0)  in 
  let (sub2,v2) = inf v sEnv fixed sub1 (Array ety)  in 
  let sub3 = subunify fixed sub2 (Ref ety)  expectedTy
  in 
  (sub3,Oper("entry",[v2;t1]))

and infer_oper d args sEnv fixed sub0 expectedTy = 
  if StringMap.mem d all_ops 
  then 
    let (argtys,str) = StringMap.find d all_ops in 
    let (sub2,args2,argtys2) = 
      infer_op_args sEnv fixed sub0 d args (sub0,[],argtys) in 
    if argtys2 = []
    then 
      let sub3 = subunify fixed sub2 (cvar str) expectedTy in 
      (sub3,Oper(d,args2))
    else basicError (d^" has too few arguments") 
  else basicError (d^" is an unknown operator") 

and infer_op_args sEnv fixed (* sub *) _ d =
  let aux arg (sub,args,argtys) =
    match argtys with
      argty :: argtys1 ->
	let (sub1,arg1) = inf arg sEnv fixed sub (cvar argty)
	in
	(sub1,arg1 :: args,argtys1)
    | _ -> basicError (d^" has too many arguments")
  in
  fold_right aux



and infer_eqcons r u sEnv fixed sub0 expectedTy = 
  let rty = TyV (nextTypeVar(),0) in
  let (sub1,r1) = inf r sEnv fixed sub0 rty in
  let uty = TyV (nextTypeVar(),0) in 
  let (sub2,u2) = inf u sEnv fixed sub1 uty in 
  let sub3 = unify fixed sub2 expectedTy (cvar "Bool") 
  in 	
  (sub3,Oper("eqcons",[r1;u2]))

  
and infer_ap r u sEnv fixed sub0 expectedTy = 
  try infer_ap_arg_first r u sEnv fixed sub0 expectedTy 
  with _ -> infer_ap_fun_first r u sEnv fixed sub0 expectedTy 

and infer_ap_arg_first r u sEnv fixed sub0 expectedTy = 
  let uty = TyV (nextTypeVar(),0) in
  let (sub1,u1) = inf u sEnv fixed sub0 uty in 
  let (sub2,r2) = inf r sEnv fixed sub1 (funty uty expectedTy) 
  in 
  (sub2,Apply(r2,u1))

and infer_ap_fun_first r u sEnv fixed sub0 expectedTy = 
  let rty = TyV (nextTypeVar(),0) in
  let (sub1,r1) = inf r sEnv fixed sub0 rty 
  in 
  let (sub2,u2,uty2) = 
    match applySub sub1 rty with 
      Funty(Linty _,_) -> 
	let (sub3,u3,_,_,uty3) = inf_linear u sEnv fixed TMap.empty (Some []) sub1 None Simple in 
	(sub3,u3,Linty uty3) 
    | _ -> 
	let uty = TyV (nextTypeVar(),0) in 
	let (sub3,u3) = inf u sEnv fixed sub1 uty in 
	(sub3,u3,uty) 
  in 
  match applySub sub2 rty with 

  | Funty(pty,sty) -> 
      let (pty2,delta) = inst_tyscheme_with_bvars pty in 
      let fixed2 = append delta fixed in 
      let sub3 = subunify fixed2 sub2 uty2 pty2 in 
      let sub4 = subunify fixed2 sub3 sty expectedTy in  
      let eVars = freeTyVarsInSEnv sub4 sEnv in 
      let sVars = freeTyVars sub4 sty in 
      let nVars = append sVars eVars in 
      let check x = 
	if mem x nVars 
	then typeError [TyV(x,0); applySub sub4 pty2] "should be bindable" 
      in 
      iter check delta;
      (sub4,Apply(r1,u2))

  | _ -> 
      let sub3 = unify fixed sub2 rty (funty uty2 expectedTy)
      in 	
      (sub3,Apply(r1,u2))



and infer_lam p s sEnv fixed sub0 expectedTy = 
  let (x,status,pty) = 
    match p with 
      Ptvar x  -> (Var x,Simple,TyV(nextTypeVar(),0))
    | Ptyped(Ptvar x,Plinty pty) -> (Var x,Linear,convert_type pty)
    | Ptyped(Ptvar x,pty) -> (Var x,Simple,convert_type pty)
    | _ -> pTermError [p] "should be a variable in abstraction" 
  in
  let sEnv1 = TMap.add x (pty,status) sEnv in
  let pty1 = match status with 
  | Linear -> Linty pty
  | _ -> pty 
  in  
  let rty = TyV(nextTypeVar(),0) in 
  let the_ty = funty pty1 rty 
  in 
  let sub1 = unify fixed sub0 the_ty expectedTy 
  in
  let (sub2,s2) = inf s sEnv1 fixed sub1 rty
  in 
  (sub2,Lam(x,s2))

(*
and infer_lin p s sEnv fixed sub0 expectedTy = 
  let (x,pty) = 
    match p with 
      Ptvar x  -> (Var x,TyV(nextTypeVar(),0))
    | Ptyped(Ptvar x,Plinty pty) -> (Var x,convert_type pty)
    | _ -> pTermError [p] "should be a variable of linear type in abstraction" 
  in
  let rty = TyV(nextTypeVar(),0) in 
  let the_ty = Funty(Linty pty,rty)
  in 
  let sub1 = subunify fixed sub0 the_ty expectedTy 
  in
  let sEnv1 = TMap.add x (pty,Linear) sEnv in   
  let (sub2,s2) = inf s sEnv1 fixed sub1 rty
  in 
  let the_term = Lam(x,s2)
  in 
  (sub2,the_term)
*)

and infer_case (xs_opt,p,pty_opt,s) is_att sEnv fixed sub0 default_ty = 
  let theta = 
    match xs_opt with 
      None -> None 
    | Some xs -> Some (List.map (fun x -> Var x) xs) 
  in 
  let ty_opt = 
    match pty_opt with
      None -> None 
    | Some ty -> Some (convert_type ty) 
  in 


(* this works for everything except setPrev, where the pattern
(n:DNode<a>) is not expanded to a pattern in the desired fashion. 
So, I plan to remove the pty_opt from everywhere, first by making it always None, and then deleting *) 




  if is_att == Method

  then      
  let (sub1,p1,delta1,tyEnv1,pty) = 
    inf_linear_or_var p sEnv fixed TMap.empty theta sub0 ty_opt Simple in 
  let fixed1 = append delta1 fixed in 
  let sEnv1 = TMap.fold TMap.add tyEnv1 sEnv 
  in 
  let sty = TyV(nextTypeVar(),0) in
  let (sub2,s2) = inf s sEnv1 fixed1 sub1 sty 
  in 
  let pty2 = applySub sub2 pty  
  and sty2 = applySub sub2 sty 
  and def2 = applySub sub2 default_ty 
  in
  if specialises sEnv sub2 delta1 pty2 sty2 def2
  then (sub2,Case(None,p1,s2), funty pty2 sty2)
  else basicError "specialises" 

  else (* not a method *) 

   let def1 = applySub sub0 default_ty 
   in 
    match def1 with 
      Funty(uty,tty) ->  
	let (sub1,ty_opt1) = 
	  match ty_opt with 
	  | Some ty -> 
	      let sub = unify fixed sub0 ty uty in 
	      (sub,Some (applySub sub ty))
	  | None -> (sub0,Some uty) 
	in 
	let (sub2,p1, (* delta1 *) _,tyEnv1,pty) = 
	  inf_linear_or_var p sEnv fixed TMap.empty theta sub1 ty_opt1 Simple in 

	let sEnv1 = TMap.fold TMap.add tyEnv1 sEnv in 
	let (sub3,s3) = inf s sEnv1 fixed sub2 tty in 
	format_specialisation (applySub sub2 pty); 

let backtrack x ty3 sub = 
  let ty1_opt = 
    try Some (TyMap.find x sub1)
    with Not_found -> None 
  and ty2_opt = 
    try Some (TyMap.find x sub2)
    with Not_found -> None 
 in 
 let is_altered_by_pattern_unification = 
   match (ty1_opt,ty2_opt) with 
   | (Some ty1,Some ty2) -> ty1 != ty2 
   | (_,Some _) -> true 
   | _ -> false 
  in 
  let is_stable_under_body_unification = 
    match ty2_opt with 
    | None -> false
    | Some ty2 -> 
	let fixed2 = append (freeTyVars sub2 ty2) fixed in 
	try let _ = unify fixed2 sub3 ty2 ty3 in true 
	with _ -> false 
  in 
  if is_altered_by_pattern_unification && is_stable_under_body_unification
  then 
    match ty1_opt with 
    | Some ty1 -> TyMap.add x ty1 sub (* revert to old value *) 
    | None -> TyMap.remove x sub      (* remove the local value *) 
  else TyMap.add x ty3 sub            (* keep the new value *)


in 
let sub4 = TyMap.fold backtrack sub3 TyMap.empty in 

	(sub4,Case(theta,p1,s3),applySub sub4 def1)  

    | _ -> 
	let (sub1,p1,delta1,tyEnv1,pty) = 
	  inf_linear_or_var p sEnv fixed TMap.empty theta sub0 ty_opt Simple in 
	let sEnv1 = TMap.fold TMap.add tyEnv1 sEnv in 
	let sty = TyV(nextTypeVar(),0) in
	let case_ty = funty pty sty in 
	let sub2 = unify fixed sub1 case_ty def1 in 
	let (sub3,s3) = inf s sEnv1 fixed sub2 sty in 
	let pty3 = applySub sub3 pty
	and sty3 = applySub sub3 sty in 
	let case_ty3 = funty pty3 sty3 
	in 
	if is_case_type delta1 pty3 sty3
	then (sub3,Case(theta,p1,s3),case_ty3)
	else typeError [case_ty3] "is ill-formed"



(* to be used when converting dynamic cases to static ones 

match (theta,default_result) with 
| (Some xs,(sub3,Case(p,s),ty3)) -> 
  let bind y q = Lam(y,q) in 
  let p1 = fold_right bind xs p in 
  let s1 = fold_right bind xs s in 
  let n = length xs in 
  (sub3,Apply(Apply(Apply(Apply(Apply(Tvar (Var "dynamic_case_for_internal_use_only",0),
           Twildstring),Tnextvar),Datum(Int n)),p1),s1),
	ty3)
| (_,_) -> 

*)



and infer_cases cs sEnv fixed sub0 expectedTy = 
  let f (sub1,rest1) case1 = 
	let (sub2,case2,_) = 
	  infer_case case1 Simple sEnv fixed sub1 expectedTy
    in 
    (sub2,Choice(case2,rest1))
  in 
  match rev cs with 
    [] -> basicError "no cases in pattern matching function" 
  | case :: cs1 -> 
      let (sub2,case2,_) = infer_case case Simple sEnv fixed sub0 expectedTy 
      in 
      fold_left f (sub2,case2) cs1 


(* replacved by th eexperiment above !!! 


and infer_case (xs_opt,p,pty_opt,s) is_att sEnv fixed sub0 default_ty = 
  let theta = 
    match xs_opt with 
      None -> None 
    | Some xs -> Some (List.map (fun x -> Var x) xs) 
  in 
  let ty_opt = 
    match pty_opt with
      None -> None 
    | Some ty -> Some (convert_type ty) 
  in 

  if is_att == Method

  then      
  let (sub1,p1,delta1,tyEnv1,pty) = 
    inf_linear_or_var p sEnv fixed TMap.empty theta sub0 ty_opt Simple in 
  let fixed1 = append delta1 fixed in 
  let sEnv1 = TMap.fold TMap.add tyEnv1 sEnv 
  in 
  let sty = TyV(nextTypeVar(),0) in
  let (sub2,s2) = inf s sEnv1 fixed1 sub1 sty 
  in 
  let pty2 = applySub sub2 pty  
  and sty2 = applySub sub2 sty 
  and def2 = applySub sub2 default_ty 
  in
  if specialises sEnv sub2 delta1 pty2 sty2 def2
  then (sub2,Case(None,p1,s2), funty pty2 sty2)
  else basicError "specialises" 

  else (* not a method *) 

   let def1 = applySub sub0 default_ty 
   in 
    match def1 with 
      Funty(uty,tty) ->  
	let (sub1,ty_opt1) = 
	  match ty_opt with 
	  | Some ty -> 
	      let sub = unify fixed sub0 ty uty in 
	      (sub,Some (applySub sub ty))
	  | None -> (sub0,Some uty) 
	in 
	let (sub2,p1,delta1,tyEnv1,pty) = 
	  inf_linear_or_var p sEnv fixed TMap.empty theta sub1 ty_opt1 Simple in 
	let fixed1 = append delta1 fixed in 
	let sEnv1 = TMap.fold TMap.add tyEnv1 sEnv 
	in 
	let dVars = freeTyVars sub2 def1 in 
	let sEnvVars = freeTyVarsInSEnv	sub2 sEnv1 in 
	let fixed2 = append dVars (append sEnvVars fixed1) in
	let (sub3,s3) = inf s sEnv1 fixed2 sub2 tty in 
	format_specialisation (applySub sub2 pty); 
	(sub1,Case(theta,p1,s3),def1)  
    | _ -> 
	let (sub1,p1,delta1,tyEnv1,pty) = 
	  inf_linear_or_var p sEnv fixed TMap.empty theta sub0 ty_opt Simple in 
	let fixed1 = append delta1 fixed in 
	let sEnv1 = TMap.fold TMap.add tyEnv1 sEnv 
	in 
	let sty = TyV(nextTypeVar(),0) in
	let case_ty = funty pty sty in 
	let sub2 = unify fixed sub1 case_ty def1 in 
	let pVars = freeTyVars sub2 pty in 
	let fixed2 = append pVars fixed1 in
	let (sub3,s3) = inf s sEnv1 fixed2 sub2 sty in 
	let pty3 = applySub sub3 pty
	and sty3 = applySub sub3 sty in 
	let case_ty3 = funty pty3 sty3 
	in 
	if is_case_type delta1 pty3 sty3
	then (sub3,Case(theta,p1,s3),case_ty3)
	else typeError [case_ty3] "is ill-formed"



(* to be used when converting dynamic cases to static ones 

match (theta,default_result) with 
| (Some xs,(sub3,Case(p,s),ty3)) -> 
  let bind y q = Lam(y,q) in 
  let p1 = fold_right bind xs p in 
  let s1 = fold_right bind xs s in 
  let n = length xs in 
  (sub3,Apply(Apply(Apply(Apply(Apply(Tvar (Var "dynamic_case_for_internal_use_only",0),
           Twildstring),Tnextvar),Datum(Int n)),p1),s1),
	ty3)
| (_,_) -> 

*)


(* spare copy of old code -- to be deleted 

and infer_case (xs_opt,p,pty_opt,s) is_att sEnv fixed sub0 default_ty = 
  let theta = 
    match xs_opt with 
      None -> None 
    | Some xs -> Some (List.map (fun x -> Var x) xs) 
  in 
  let ty_opt = 
    match pty_opt with
      None -> None 
    | Some ty -> Some (convert_type ty) 
  in 
  let (sub1,p1,delta1,tyEnv1,pty) = inf_linear_or_var p sEnv fixed TMap.empty theta sub0 ty_opt Simple in 
  let fixed1 = append delta1 fixed in 
  let sEnv1 = TMap.fold TMap.add tyEnv1 sEnv 
  in 
let default_result = 
  if is_att == Method
  then      
    let sty = TyV(nextTypeVar(),0) in
    let (sub2,s2) = inf s sEnv1 fixed1 sub1 sty 
    in 
    let pty2 = applySub sub2 pty  
    and sty2 = applySub sub2 sty 
    and def2 = applySub sub2 default_ty 
    in
    if specialises sEnv sub2 delta1 pty2 sty2 def2
    then (sub2,Case(None,p1,s2), funty pty2 sty2)
    else basicError "specialises" 
  else (* not a method *) 
    let def1 = applySub sub1 default_ty 
    in 
    match def1 with 
      Funty(uty,tty) ->  
	let sub2 = unify fixed sub1 pty uty
	in 
	let dVars = freeTyVars sub2 def1 in 
	let sEnvVars = freeTyVarsInSEnv	sub2 sEnv1 in 
	let fixed2 = append dVars (append sEnvVars fixed1) in
	let (sub3,s3) = inf s sEnv1 fixed2 sub2 tty in 

	format_specialisation (applySub sub2 pty); 
	(sub1,Case(theta,p1,s3),def1)  
    | _ -> 
	let sty = TyV(nextTypeVar(),0) in
	let case_ty = funty pty sty in 
	let sub2 = unify fixed sub1 case_ty def1 in 
	let pVars = freeTyVars sub2 pty in 
	let fixed2 = append pVars fixed1 in
	let (sub3,s3) = inf s sEnv1 fixed2 sub2 sty in 
	let pty3 = applySub sub3 pty
	and sty3 = applySub sub3 sty in 
	let case_ty3 = funty pty3 sty3 
	in 
	if is_case_type delta1 pty3 sty3
	then (sub3,Case(theta,p1,s3),case_ty3)
	else typeError [case_ty3] "is ill-formed"

in 

(* to be used when converting dynamic cases to static ones 

match (theta,default_result) with 
| (Some xs,(sub3,Case(p,s),ty3)) -> 
  let bind y q = Lam(y,q) in 
  let p1 = fold_right bind xs p in 
  let s1 = fold_right bind xs s in 
  let n = length xs in 
  (sub3,Apply(Apply(Apply(Apply(Apply(Tvar (Var "dynamic_case_for_internal_use_only",0),
           Twildstring),Tnextvar),Datum(Int n)),p1),s1),
	ty3)
| (_,_) -> 

*)

default_result

*)


and infer_cases cs sEnv fixed sub0 expectedTy = 
  let f (sub1,rest) case = 
	let (sub2,case1,_) = 
	  infer_case case Simple sEnv fixed sub1 expectedTy
    in 
    (sub2,Choice(case1,rest))
  in 
  match rev cs with 
    [] -> basicError "no cases in pattern matching function" 
  | case :: cs1 -> 
      let (sub2,case2,_) = infer_case case Simple sEnv fixed sub0 expectedTy 
      in 
      fold_left f (sub2,case2) cs1 

end of experiemntal replacvement *) 


and infer_add_case x case sEnv fixed sub0 expectedTy = 
  let (sch,status) = 
   try TMap.find x sEnv
    with Not_found ->
      try 
	let (_,(_,(status1,sch1,hasRefVar))) =  envFind 0 x globalVEnv in 
        if hasRefVar
	then (applySub !globalRefVarSub sch1,status1)
	else (sch1,status1) 
      with Not_found -> termError [Tvar (x,0)] "is not recognised"
  in 
  begin
    match status with 
    | Extensible | Method | Discontinuous -> ()
    | _ -> termError [Tvar (x,0)] "is not extensible"
  end;
  let ty1 = inst_tyscheme (applySub sub0 sch) in 
  let sub1 = subunify fixed sub0 (TyC(TyVar "Unit",0)) expectedTy in 
  let (sub2,case2,casety) = infer_case case status sEnv fixed sub1 ty1 in 
  let ty_opt = 
    match status with 
      Method -> Some casety
    | _ -> None
  in 
  (sub2,Addcase(x,case2,ty_opt))

and infer_sub_case x sEnv fixed sub0 expectedTy = 
  let ( (* sch *) _,status) = 
   try TMap.find x sEnv
    with Not_found ->
      try 
	let (_,(_,(status1,sch1,hasRefVar))) =  envFind 0 x globalVEnv in 
        if hasRefVar
	then (applySub !globalRefVarSub sch1,status1)
	else (sch1,status1) 
      with Not_found -> termError [Tvar (x,0)] "is not recognised"
  in 
  if status != Extensible && status != Discontinuous
  then termError [Tvar (x,0)] "is not extensible"
  else 
      let sub1 = subunify fixed sub0 (TyC(TyVar "Unit",0)) expectedTy 
      in 
      (sub1,Subcase x)

and infer_let = function 
  | Simple -> infer_let_simple
  | Linear -> basicError "infer_let Linear is not supported" 
  | status -> infer_letrec status 
  
and infer_let_simple param u t sEnv fixed sub0 expectedTy = 
  let (x,uty) = 
    match param with 
      Ptvar x -> (Var x,TyV(nextTypeVar(),0))
    | Ptyped(Ptvar x,ty) -> (Var x,convert_type ty)
    | _ -> pTermError [Plet(Simple,param,u,t)] "has a complex let-binding"
  in 
  let (sub1,u1) = inf u sEnv fixed sub0 uty in
  let sch = clos_ty sub1 sEnv uty in 
  let sEnv2 = TMap.add x (sch,Simple) sEnv in 
  let (sub3,t3) = inf t sEnv2 fixed sub1 expectedTy 
  in 
  (sub3,Tlet(Simple,x,u1,t3))


and infer_letrec status param u t sEnv fixed sub0 expectedTy =  

    match param with 
      Ptvar x -> 
	let uty = TyV(nextTypeVar(),0) in 
	let sEnv1 = TMap.add (Var x) (uty,status) sEnv in 
        let (sub1,u1) = inf u sEnv1 fixed sub0 uty in
	let (sub2,t2) = inf t sEnv1 fixed sub1 expectedTy 
	in 
	(sub2,Tlet(status,Var x,u1,t2))

    | Ptyped(Ptvar x,pty) -> 
	let uty = convert_type pty in 
	let sch = clos_ty sub0 sEnv uty  in 

	let sEnv1 = TMap.add (Var x) (sch,status) sEnv in 
	let fixed0 = append (freeTyVars sub0 uty)  fixed in 
	let (sub1,u1) = inf u sEnv1 fixed0 sub0 uty in
	let (sub2,t2) = inf t sEnv1 fixed0 sub1 expectedTy 
	in 
	(sub2,Tlet(status,Var x,u1,t2))

    |_ -> basicError "Pletrec"  


(* old code 

and infer_letrec status param u t sEnv fixed sub0 expectedTy =  

  let (x,sch) = 
    match param with 
      Ptvar x -> (x,TyV(nextTypeVar(),0))
    | Ptyped(Ptvar x,pty) -> (x,clos_ty sub0 sEnv (convert_type pty)) 
    |_ -> basicError "Pletrec"  
  in 

  try 
    let sEnv1 = TMap.add (Var x) (sch,Simple) sEnv in 
    let (inst_ty,delta) =  inst_tyscheme_with_bvars sch in 
    let fixed0 = append delta fixed in 
    let (sub1,u1) = inf u sEnv1 fixed0 sub0 inst_ty in
    let (sub2,t2) = inf t sEnv1 fixed0 sub1 expectedTy 
    in 
  (sub2,Tlet(status,Var x,u1,t2))

  with _ -> 
    let uty = inst_tyscheme sch in 
    let sEnv1 = TMap.add (Var x) (uty,Simple) sEnv in 
    let (sub1,u1) = inf u sEnv1 fixed sub0 uty in
    let sch = clos_ty sub1 sEnv1 uty in 
    let sEnv2 = TMap.add (Var x) (sch,status) sEnv in 
    let (sub3,t3) = inf t sEnv2 fixed sub1 expectedTy 
    in 
    (sub3,Tlet(status,Var x,u1,t3))

*) 
(* delete ??
    let sEnv1 = TMap.add (Var x) (sch,Simple) sEnv in 
     let (sub1,u1) = inf u sEnv1 fixed sub0 inst_ty in
    let (sub2,t2) = inf t sEnv1 fixed sub1 expectedTy in 
    let fixed1 = append (freeTyVars sub2 inst_ty) fixed in 
    if get_mode "types" = Show_off || 
       let _ = subunify fixed1 sub2 (clos_ty sub2 sEnv inst_ty) (clos_ty sub2 sEnv sch) in true 
    then (sub2,Tlet(status, Var x,u1,t2))
    else 
      typeError [applySub sub2 inst_ty] 
      "instantiates bound type variables in inference"
*)
(* delete ?? 

and infer_letext param u t sEnv fixed sub0 expectedTy = 

  let (x,sch) = 
    match param with 
      Ptvar x -> (x,TyV(nextTypeVar(),0))
    | Ptyped(Ptvar x,pty) -> (x,clos_ty sub0 sEnv (convert_type pty)) 
    |_ -> basicError "Pletrec"  
  in 
  let sEnv1 = TMap.add (Var x) (sch,Extensible) sEnv in 

  try 
    let (inst_ty,delta) =  inst_tyscheme_with_bvars sch in 
    let fixed0 = append delta fixed in 
    let (sub1,u1) = inf u sEnv1 fixed0 sub0 inst_ty in
    let (sub2,t2) = inf t sEnv1 fixed0 sub1 expectedTy 
    in 
    (sub2,Tletext(Var x,u1,t2))

  with _ -> 
    let inst_ty = inst_tyscheme sch in 
    let (sub1,u1) = inf u sEnv1 fixed sub0 inst_ty in
    let (sub2,t2) = inf t sEnv1 fixed sub1 expectedTy in 
    let fixed1 = append (freeTyVars sub2 inst_ty) fixed in 
    if get_mode "types" = Show_off || 
       let _ = subunify fixed1 sub2 (clos_ty sub2 sEnv inst_ty) (clos_ty sub2 sEnv sch) in true 
    then (sub2,Tletext(Var x,u1,t2))
    else 
      typeError [applySub sub2 inst_ty] 
      "instantiates bound type variables in inference"
   

 
and infer_letmethod param u t sEnv fixed sub0 expectedTy = 

  let (x,sch) = 
    match param with 
      Ptvar x -> (x,TyV(nextTypeVar(),0))
    | Ptyped(Ptvar x,pty) -> (x,clos_ty sub0 sEnv (convert_type pty)) 
    |_ -> basicError "Pletrec"  
  in 
  let sEnv1 = TMap.add (Var x) (sch,Method) sEnv in 
  let (inst_ty,delta) =  inst_tyscheme_with_bvars sch in 
  let fixed0 = append delta fixed in 
  let (sub1,u1) = inf u sEnv1 fixed0 sub0 inst_ty in
  let (sub2,t2) = inf t sEnv1 fixed0 sub1 expectedTy in 
  (sub2,Tletext(Var x,u1,t2))
 
and infer_letdiscontinuous param u t sEnv fixed sub0 expectedTy = 

  let (x,sch) = 
    match param with 
      Ptvar x -> (x,TyV(nextTypeVar(),0))
    | Ptyped(Ptvar x,pty) -> (x,clos_ty sub0 sEnv (convert_type pty)) 
    |_ -> basicError "Pletrec"  
  in 
  let sEnv1 = TMap.add (Var x) (sch,Discontinuous) sEnv in 
  let (inst_ty,delta) =  inst_tyscheme_with_bvars sch in 
  let fixed0 = append delta fixed in 
  let (sub1,u1) = inf u sEnv1 fixed0 sub0 inst_ty in
  let (sub2,t2) = inf t sEnv1 fixed0 sub1 expectedTy in 
  (sub2,Tletdiscontinuous(Var x,u1,t2))

end delete *) 


and infer_typed t1 ty sEnv fixed sub0 expectedTy = 
  let ty1 = convert_type ty in 
  let sub1 = subunify fixed sub0 ty1 expectedTy in 
  inf t1 sEnv fixed sub1 ty1 

and infer_new str args (* sEnv *) _ fixed sub0 expectedTy =
  let n = !declaration_counter in 
  let class_ty = type_of_class (str,n) (map convert_type args) (TyC(TyVar "Unit",0)) in 
  let sub1 = subunify fixed sub0 class_ty expectedTy in 
  match gTyEnvFind n (TyVar str) with 
  | (_,Class(_,_,new_term,_)) -> (sub1,new_term  (Tconstructor (Var "Un",0)))
  | _ -> typeError [TyC(TyVar str,n)] "is an unknown class" 

and infer_new_array t n sEnv fixed sub0 expectedTy = 
  let ety = TyV (nextTypeVar(),0) in 
  let (sub1,t1)  =  inf t sEnv fixed sub0  ety in 
  let (sub2,n2) = inf n sEnv fixed sub1  (cvar "Int") in 
  let sub3 = subunify fixed sub2 (Array ety) expectedTy 
  in 	
 (sub3, TnewArr(t1,n2))


and infer_invoke t x super sEnv fixed sub0 expectedTy = 
  let (n,sch) = 
    try       let (n0,(_,(is_att,sch1,hasRefVar))) = envFind 0 (Var x) globalVEnv
      in 
      if is_att == Method 
      then 
        if hasRefVar
	then (n0,applySub !globalRefVarSub sch1)
	else (n0,sch1)
      else raise Not_found
    with Not_found -> termError [Tvar (Var x,0)] "is not a recognised method"
  in 
  let x1 = 
    if super 
    then Tsuper(Var x,n)
    else Tvar(Var x,n)
  in 
  let fty = inst_tyscheme (applySub sub0 sch) in 
  let ty = TyV (nextTypeVar(),0) in
  let (sub1,t1) = inf t sEnv fixed sub0 ty in
  let fty1 = applySub sub1 fty in
  let ty1 = applySub sub1 ty in 
  let (sub2,resty) = invoke_ty sEnv sub1 ty1 fty1 in 

  let sub3 = subunify fixed sub2 resty expectedTy 
  in 	
  (sub3,Apply(x1,t1))

(*
and infer_field sEnv fixed (sub,u) expectedTy = 
  match u with 
  | Ptvar x when TMap.mem (Var x) sEnv -> 
      let ty1 = inst_tyscheme (applySub sub (fst (TMap.find (Var x) sEnv))) in 
      let sub2 = subunify fixed sub ty1 expectedTy
      in 
      (sub2,Tvar(Var x,!declaration_counter))
  
  | Pinvoke (t,x,false) -> 
      let (n,mty) = 
	try 
	  let (n0,(_,(is_att,sch1,hasRefVar))) = envFind 0 (Var x) globalVEnv
	  in 
	  if is_att == Method 
	  then 
	    if hasRefVar
	    then (n0,applySub !globalRefVarSub sch1)
	    else (n0,sch1)
	  else raise Not_found
	with Not_found -> 
	  termError [Tvar (Var x,0)] "is not a recognised method"
      in 
      let x1 = Tvar(Var x,n) in 
      let ty = TyV (nextTypeVar(),0) in
      let (sub1,t1) = infer_field sEnv fixed (sub,t) ty in
      let mty1 = applySub sub1 mty in
      let ty1 = applySub sub1 ty in 
      let (sub2,resty) = invoke_ty sEnv sub1 ty1 mty1 in 
      let sub3 = subunify fixed sub2 resty expectedTy 
      in 	
      (sub3,Apply(x1,t1))

  | _ -> pTermError [u] "is not a field"
*)


let infer source ty = 
  let (sub,term) = inf source TMap.empty  [] idSub ty 
  in 
  (term,applySub sub ty,sub)
 ;;



