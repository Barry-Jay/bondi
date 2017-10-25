open List  
open Format
open Datum
open P_data

 
module OrderedTyVars = 
  struct 
    type t = tyVar
    let compare v1 v2 =       
      match v1,v2 with
	(TyVar x1,TyVar x2) -> compare x1 x2 
      | (TyVar _,_) -> 1
      | (_,TyVar _) -> -1
      | (MTypeVar x1,MTypeVar x2) -> compare x1 x2
  end
module TyMap = Map.Make(OrderedTyVars);;

type term_variable =
    Var of identifier (* normal variables, start with lower case *)
  | Mvar of int        (* machine variables *)

module Ordered_vars = (* ordering on term variables *)
  struct
    type t = term_variable
    let compare v1 v2 =
      match (v1,v2) with
          (Var x1,Var x2) -> compare x1 x2
        | (Var _,_) -> 1
        | (_,Var _) -> -1
        | (Mvar x1,Mvar x2) -> compare x1 x2
  end
module TVarSet = Set.Make(Ordered_vars);; 
module TMap = Map.Make(Ordered_vars);;

type i_type =
  | TyV of tyVar * int         (* variables *)
  | TyC of tyVar * int         (* constants *)
  | ApplyF of i_type * i_type  (* applications *)
  | ChoiceF of i_type * i_type  (* choices *)
  | SuperF of i_type * i_type  (* choices *)
  | Funty of i_type  * i_type  (* function types *)
  | Linty of i_type   	       (* linear  types *)
  | Ref of i_type               (* reference types *) 
  | Array of i_type               (* array types *) 
  | Quant of tyVar * i_type      (* quantified types *) 
type i_term =
  | Tvar of term_variable * int    (* var, index *) 
  | Tnextvar                        (* for producing unknowns -- deprecate this? *) 
  | Tsuper of term_variable * int   (* super terms, for super.method *) 
  | Twildcard of string                    (* a constant that matches anything *)  
  | Twildstring                    (* a constant for identifying wildcards -- internal use only -- deprecate this?  *)  
  | Tconstructor of term_variable  * int (* constructors *) 
  | Datum of datum_value                  (* datum values *) 
  | Oper of string * i_term list          (* operators with arguments *)
  | Apply of i_term * i_term              (* applications *) 
  | Lam of term_variable * i_term         (* abstractions *) 
  | Case of term_variable list option * i_term * i_term               (* static cases *) 
  | Choice of i_term * i_term              (* choices, for extensions *) 
  | Over of i_term * i_term              (* overcase, for extensions *) 
  | Addcase of term_variable * i_term * i_type option     (* add a case *) 
  | Subcase of term_variable                (* remove a case *) 
  | Tlet of P_data.let_status * term_variable * i_term * i_term (* let-terms *) 
(*
  | Tletrec of term_variable * i_term * i_term (* recursive let-terms *) 
  | Tletext of term_variable * i_term * i_term (* extensible let-terms *) 
  | Tletdiscontinuous of term_variable * i_term * i_term (* discontinuous let-terms *) 
*)
  | TnewArr of i_term * i_term                 (* new arrays *) 
(*> CPC *)
  | Tdname of P_data.name_form * i_term * i_type          (* Datum values in patterns *)
  | Tcname of P_data.name_form * term_variable * int * i_type   (* Constructors for CPC patterns: form, constructor, index *)
  | Tname of P_data.name_form * term_variable * int * i_type (* Names for CPC patterns: name form, variable, index *)
  | Tpapp of i_term * i_term * i_type             (* Compound patterns *)
  | Prll of i_term * i_term                       (* Paralell composition of two processes *)
  | Rest of term_variable * i_term                (* Restriction of a term_variable over a process *)
  | Repl of i_term                                (* Replicating process *)
  | Pcase of i_term * i_term                       (* Process-case, pattern and body *)
(*< CPC *)

type sub = i_type TyMap.t

type value =
  | Vvar of term_variable
  | Vsuper of value
  | Vconstructor of term_variable * int
  | Vdatum of datum_value
  | Vwildcard of string
  | Vwildstring
  | Vas of value * value
  | Vview of value * value
  | Vwhere of value * i_term
  | Vapply of value * value
  | Vlam of term_variable * value_env ref * i_term
  | Vcase of value * value_env ref * i_term
  | Vchoice of value * value
  | Vext of value ref (* for extensible functions and methods *) 
  | Vref of value ref
  | Varray of value array
(*> CPC *)
  | VtySub of sub
(*< CPC *)
and value_env = value TMap.t

(* type sub = i_type TyMap.t *)

type type_data = 
  | Synonym of i_type  
  | Class of (tyVar * int) option * (p_term -> p_term) * (i_term -> i_term)  * int 
type type_env = (int * type_data) list TyMap.t 
type constructor_env = (int * (i_type * let_status)) list TMap.t
type scheme_env = (i_type * let_status) TMap.t 
type global_value_env = (int * (value * (let_status * i_type * bool))) list TMap.t 

exception Wrong_index of int;;
exception TypeError of i_type list * string;;
exception TermVarError of term_variable * string
exception TermError of i_term list * string

(*** i_data *)

let typeError tys s = raise (TypeError (tys,s));;
let termVarError t s = raise (TermVarError (t,s));;
let termError ts s = raise (TermError (ts,s));;

let fvar str = TyV(TyVar str,0)
let cvar str = TyC(TyVar str,0)
let apF g f = ApplyF(g,f)
let apF2 h g f = apF (apF h g) f 
let pairF ty1 ty2 = apF2 (cvar "PairF") ty1 ty2
let funty ty1 ty2 = Funty(ty1,ty2)
let funty2 ty1 ty2 ty3 = funty ty1 (funty ty2 ty3)
let comm = cvar "Unit"

(* Commented out by TGW 2011-05-23
 * Notes: Note sure why this is still here. Superceded by thread safe version
 * later on (see CPC code near the end).
let fvc = ref 0;; (* free variable counter - private *)
let nextvar() = incr fvc ; Mvar !fvc;; *)
let tvar x = Tvar(Var x,0) 
let zcvar x = Tconstructor (Var x,0)
let t_un = Tconstructor (Var "Un",0)
let exn = zcvar  "Exception"

let rec isValue = function (* for the value restriction upon polymorphism *) 
  | Apply (Tconstructor _,u) -> isValue u 
  | Tlet (_,_,_,body) -> isValue body 
  | Tconstructor  (Var "Ref",_)
  | Twildcard "ref" 
  | Twildcard "array" -> false
  | Tvar _ 
  | Tnextvar                      
  | Tsuper _
  | Twildcard _ 
  | Twildstring   _   
  | Tconstructor _ 
  | Datum _
  | Lam _ 
  | Case _ 
  | Choice _ 
  | Addcase _ -> true 
  |  _ -> false 


(*** environments *) 

let get_best m ys = 
  let rec gb p q = function 
      [] -> raise (Wrong_index p)
    | (n,x):: xs ->  if q=0 || n<=q then(n,x) else gb n q xs 
  in 
  if List.length ys = 0 
  then raise Not_found 
  else gb 0 m ys 
;;

let globalTyEnv = ref (TyMap.empty : type_env);;

let gTyEnvFind n tyv = 
  try get_best n (TyMap.find tyv !globalTyEnv)
  with Wrong_index p -> 
   typeError 
      [TyV (tyv,n)] 
      ("has index " ^ 
       (string_of_int n) ^ 
       " but earliest known index is " ^ 
       (string_of_int p))
;;

let gTyEnvAdd tyv n ty_data = 
  let tyds = 
    try TyMap.find tyv !globalTyEnv 
    with Not_found -> [] 
  in 
  globalTyEnv := TyMap.add tyv ((n,ty_data) :: tyds) !globalTyEnv


let globalVEnv = ref (TMap.empty : global_value_env) 
let globalCEnv = ref (TMap.empty : constructor_env) 
let globalRefVarSub = ref (TyMap.empty: sub)

let envFind n tv env = 
  try get_best n (TMap.find tv !env)
  with Wrong_index p -> termVarError tv "has a bad index" 

let envFindFull n tv env = 
  try get_best n (TMap.find tv !env)
  with Wrong_index p -> termVarError tv "has a bad index" 

let envAdd tv n t env  = 
  let ts = 
    try TMap.find tv !env 
    with Not_found -> [] 
  in 
  env := TMap.add tv ((n,t) :: ts) !env 




(*** substitutions *) 

let idSub = TyMap.empty;;

let rec composeSubs tySub1 tySub0 = 
  let addSub tv f tySub = 
    if TyMap.mem tv tySub0 
    then tySub 
    else TyMap.add tv f tySub 
  in
  TyMap.fold addSub tySub1 (TyMap.map (applySub tySub1) tySub0)

and applySub tySub =
  let rec appS = function
    | TyV (tyv,n) ->
	begin 
	  try TyMap.find tyv tySub
          with Not_found -> TyV (tyv,n)
        end
    | TyC (tyv,n) as ty -> ty 
    | ApplyF(g,f) -> ApplyF(appS g, appS f)
    | ChoiceF(g,f) -> ChoiceF(appS g, appS f)
    | SuperF(g,f) -> SuperF(appS g, appS f)
    | Funty (g,f) -> Funty(appS g, appS f) 
    | Linty f -> Linty(appS f) 
    | Ref ty -> Ref (appS ty) 
    | Array ty -> Array (appS ty) 
    | Quant(x, ty) -> 
	  begin 
	    match freshen_tyvars [x] with  
	      (sub1,[y]) -> 	
		let sub2 = composeSubs tySub sub1 in 
		Quant(y,applySub sub2 ty)
	    | _ -> basicError "error in applySub"
	  end
  in
  appS 

and freshen_tyvar  x (sub,ys) = 	
  let y = nextTypeVar() in 
  (TyMap.add x (TyV(y,0)) sub,y::ys)

and freshen_tyvars tyvs = 
  fold_right freshen_tyvar tyvs (idSub,[]) 

and freshen_tyvar2  x y = 	
  let z = nextTypeVar() in 
  (TyMap.add x (TyV(z,0)) (TyMap.add y (TyV(z,0)) idSub),z)
  ;;



(*** free variables *)

let rec list_remove (x:tyVar)  = function
    [] -> []
  | y :: ys -> if x = y then list_remove x ys else y :: (list_remove x ys)

let rec remove_duplicates = function 
    [] -> [] 
  | x :: xs -> x :: (list_remove x (remove_duplicates xs))

let string_of_tyvar = 
  function 
    TyVar s -> s 
  | MTypeVar n -> "ty_"^(string_of_int n)
;;

let rec freeTyVars sub =
  let rec freeV  = function
  | TyV (tv,_) when TyMap.mem tv sub -> freeV (TyMap.find tv sub)
  | TyV (tv,_) -> [tv]
  | TyC (tv,n) -> []
  | ApplyF (g,f) 
  | ChoiceF (g,f) 
  | SuperF (g,f) 
  | Funty (g,f) -> remove_duplicates (append (freeV f) (freeV g))
  | Linty ty
  | Ref ty 
  | Array ty -> freeV ty 
  | Quant(x,ty) -> 
      let (sub1,tyvs) = freshen_tyvars [x] in 
      let sub2 = composeSubs sub1 sub in 
      fold_right list_remove tyvs (freeTyVars sub2 ty)
  in 
  freeV
;;


let covTyVars sub = 
 let rec oV  = function
  | TyV (tv,_) -> 
      if  TyMap.mem tv sub 
      then oV (TyMap.find tv sub)
      else [ tv]
  | ApplyF (g,f)
  | ChoiceF (g,f)
  | SuperF (g,f)
  | Funty (g,f) -> fold_right list_remove (freeTyVars sub g) (oV f)
  | _ -> []
  in 
  oV
;;

let freeTyVarsInSEnv sub sEnv =
  let doEntry x (sch,_) tyVars =
    append (freeTyVars sub sch) tyVars
    in
    remove_duplicates (TMap.fold doEntry sEnv [])
  ;;


let avoid x sub = 
  let aux y ty b = b &&  not (mem x (freeTyVars idSub ty)) 
  in 
  TyMap.fold aux sub true
;;






(*** p_types to i_types *) 


let declaration_counter = ref 0 ;;
let get_declaration_counter() = 
  incr declaration_counter; 
  if get_mode "declaration_index" = Show_on 
  then printf "%d is the new declaration index\n"  !declaration_counter; 
  !declaration_counter;;

let classTyString = "_cty";;
(* 
let classStringOfClassTyString str = String.sub str 0  (String.length str - 4);;
*)

let rec type_of_class (str,n) zs rest = 
  let tyv = TyVar (str^classTyString) in 
  try 
    match gTyEnvFind n (TyVar (str)) with 
    | (_,Synonym ty) -> ty 
    | (n1,Class(Some (TyVar str0,n0),_,_,_)) -> 
	type_of_class (str0,n0) zs (ApplyF (fold_left apF (TyC(tyv,n1)) zs, rest))
    | n1,_ -> ApplyF (fold_left apF (TyC(tyv,n1)) zs, rest)
  with Not_found -> typeError [TyC(TyVar str,n)] "is an unknown type or class constant"


let rec convert_type = function
    PtyV x -> TyV(x,!declaration_counter)
  | Pconstant x -> type_of_class (x,!declaration_counter) [] (TyC(TyVar "Top",0))
  | PapplyF(ty1,ty2) -> ApplyF(convert_type ty1,convert_type ty2) 
  | Pfunty (ty1,ty2) -> Funty(convert_type ty1, convert_type ty2)
  | Plinty (ty) -> Linty(convert_type ty)
  | Pquant(x,ty) -> Quant(x,convert_type ty)
  | Pnestedclass(str,args,rest) -> 
      type_of_class (str,!declaration_counter) (map convert_type args) (convert_type rest) 
  | Pref ty -> Ref (convert_type ty )
  | Parr ty -> Array (convert_type ty) 
;;

let rec pattern_of_class (tyv,n) inner_pat = 
    match tyv with 
      TyVar cl_str -> 
	let local_pat = ap2 (Pconstructor cl_str) inner_pat (Pwildcard "")
	in 
	begin
	  try 
	    match gTyEnvFind n tyv with 
	      _,Class(Some (tyv0,n0),_,_,_) -> pattern_of_class (tyv0,n0) local_pat
	    | _,Class(None,_,_,_) -> local_pat
	    | _ -> typeError [TyC(TyVar cl_str,n)] "is an unknown class"
	  with Not_found -> typeError [TyC(TyVar cl_str,n)] "is an unknown class"
	end
    | _ -> typeError [TyC(tyv,n)] "is an unknown class"
;;



(*** Formatting *)

(* how many spaces to indent if line break *) 

let termIndent = 2;;
let fIndent = 2;;

(* precedences *)

let prec_fun =    1
let prec_let =  2
let prec_selector = 2
let prec_seq = 3
let prec_assign = 4
let prec_equal = 5

let prec_app =    10
let prec_bang = 11
let prec_pattern = 20

let prec_special = 0 ;;
let prec_wedge = 1;;
let prec_forall = 1;;
let prec_funty = 2;; 
let prec_mu = 3
let prec_tuple = 4
let prec_sum = 5
let prec_product = 6
let prec_compose = 7
let prec_par = 3


let string_of_tyvar = 
  function 
    TyVar s -> s 
  | MTypeVar n -> "ty_"^(string_of_int n)
;;

let format_untidy_tyvar tv = ps (string_of_tyvar tv)
;;

let f_string_tbl = ref []  (* for pretty printing *)
let f_counter   = ref ""

let next_f_string() =
  f_counter := incrStringCounter !f_counter 'a' 'z';
  !f_counter
;;

let format_tyvar tidy tv tbl new_fun =
  let s = 
    if tidy 
    then 
      try List.assoc (string_of_tyvar tv) !tbl
      with Not_found ->
	let s' = 
          match tv with 
            TyVar tv' when TyMap.mem tv !globalTyEnv -> tv'
          | _ -> new_fun() in
	tbl := (string_of_tyvar tv,s') :: !tbl;
	s'
    else string_of_tyvar tv
  in 
  ps s;
;;


 let format_tyvarlist tyvs =
 ps "[";
 List.iter (fun x -> ps (string_of_tyvar x ^ ","))        tyvs ;
 ps "]";
 flush stdout


let rec split_apF args = function
    ApplyF(ty,z) -> split_apF (z::args) ty 
  | ty -> (ty,args) 
;;

let rec list_equal = function
    [],[] -> true 
  | x::xs,y::ys -> x ==y && list_equal (xs,ys)
  | _ -> false 

let rec class_path (tyv,n) zs = function
    (ApplyF(ty,rest)) as ty0 -> 
      begin 
	match split_apF [] ty with 
	  (TyC (TyVar str1,n1),zs1) -> 
	    if  true (* list_equal (zs,zs1) !!! *) &&
	      String.length str1 > 4 &&  
	      String.sub str1 (String.length str1 -4) 4 = 
	      classTyString
	    then 
	      let tyv1 =  TyVar (String.sub str1 0  (String.length str1 -4)) in
	      try 
		match gTyEnvFind  n1 tyv1 with 
		  (_,Class(Some p,_,_,_)) when p = (tyv,n) -> class_path  (tyv1,n1) zs rest 
		| _ ->  (tyv,n,ty0)
	      with _ ->  (tyv,n,ty0)
	    else  (tyv,n,ty0)
	| _ -> (tyv,n,ty0)
      end
  | ty0 -> (tyv,n,ty0)
      

let restore_class ty0 = 
  match ty0 with 
    ApplyF(main,rest) -> 
      begin
 	match split_apF [] main with 
	  (TyC(TyVar str,n),zs) -> 
	    if String.length str > 4 &&  
	      String.sub str (String.length str -4) 4 = 
	      classTyString
	    then 
	      let tyv = TyVar (String.sub str 0  (String.length str -4)) in 
	      begin 
		try 
		  match gTyEnvFind n tyv with 
		    n0,Class(None,_,_,_) -> 
		      let  (tyv1,n1,ty1) = class_path (tyv,n0) zs rest in 
		      Some (tyv1,n1,zs,ty1)
		  | _ -> None 
		with _ -> None 
	      end 
	    else None 
	| _ -> None 
      end 
  | _ -> None 
;;
 



let format_type tidy ty  = 

let rec ftype do_ty left_prec right_prec =
   match do_ty with
     
(* delete as it conflicts with Pnestedclass in declare.ml 
     TyV (MTypeVar _,n) when n != 0 -> basicError  "found a non-zero index in a machine type variable" 
*) 
   | TyV (x,_) -> 
       format_tyvar tidy x f_string_tbl next_f_string (* ; ps "_v" *) 
   | TyC (x,n) -> ps (string_of_tyvar x)
   | Funty (ty1,ty2) -> 
       let needsParens = 
	 prec_funty < left_prec 
           (* never happens currently, 
	      as FunTy is right-associative *)
	   || prec_funty <= right_prec
           (* if there is, say, a FunTy to the right *)
       in
       open_box fIndent;       
       if needsParens 
       then (
	 lpn();
      	 ftype ty1 0 prec_funty
	)
       else (
      	 ftype ty1 left_prec prec_funty  
	);
       print_space();
       ps "->" ;
       print_space();
       if needsParens 
       then (
      	 ftype ty2 prec_funty 0;
	 rpn()
	)
       else (
      	 ftype ty2 prec_funty right_prec 
	);
       close_box();


  | ApplyF(ApplyF(TyC(TyVar "Binprod",_),f),g) -> 
       let needsParens = 
	 prec_product < left_prec (* right associative *)
	  || 
	 prec_product <= right_prec 
       in 
       open_box fIndent;
       if needsParens
       then (
	 lpn() ;
	 ftype f 0 prec_product ;
	 ps " * " ;
	 ftype g prec_product 0 ;
	 rpn();
	)
       else (
	 ftype f left_prec prec_product ;
	 ps " * " ;
	 ftype  g prec_product right_prec ;
	) ;
       close_box ()
	 
   | ApplyF(ApplyF(TyC(TyVar "Bincoprod",_),f),g) -> 
       let needsParens = 
	 prec_product < left_prec (* right associative *)
	   ||
	 prec_product <= right_prec 
       in 
       open_box fIndent;
       if needsParens
       then (
	 lpn() ;
	 ftype f 0 prec_product ;
	 ps " + " ;
	 ftype g prec_product 0 ;
	 rpn();
	)
       else (
	 ftype f left_prec prec_product ;
	 ps " + " ;
	 ftype  g prec_product right_prec ;
	) ;
       close_box ()
	 	
   | ChoiceF(ty1,ty2) 
   | SuperF(ty1,ty2) -> 
              let needsParens = 
	 prec_wedge < left_prec 
           (* never happens currently, 
	      as FunTy is right-associative *)
	   || prec_wedge <= right_prec
       in
       open_box fIndent;       
       if needsParens 
       then (
	 lpn();
      	 ftype ty1 0 prec_wedge
	)
       else (
      	 ftype  ty1 left_prec prec_wedge
	);
       print_space();
       ps "/\\";
	 print_space();
       if needsParens 
       then (
      	 ftype ty2 prec_wedge 0;
	 rpn()
	)
       else (
      	 ftype ty2 prec_wedge right_prec
	);
       close_box();
       

  | ApplyF (g,f) ->
       begin	 
	 match restore_class (ApplyF (g,f)) with 
	   None -> 
	     let needsParens = 
	       prec_app <= left_prec 
	   || prec_app < right_prec
       in
	     open_box fIndent; 
	     if needsParens 
	     then (
	       lpn();
	       ftype g 0 prec_app ;
	       ps " "; 
	       ftype f prec_app 0 ;
	       rpn()
	      )
	     else (
	       ftype g 0 prec_app ;
	       ps " "; 
	       ftype f prec_app 0
	      ) ;
	     close_box()

	 | Some (tyv0,n0,zs,ty1) -> 
	     ps (string_of_tyvar tyv0) ;
	     begin
	       match zs with 
		 [] -> () 
	       | z1::zs1 -> 
		   ps "<";
		   ftype z1 0 0;
		   iter (fun z -> ps ","; ftype z 0 0) zs1 ;
		   ps ">"
	     end;
	     begin 
	       match ty1 with 
		 TyC(TyVar "Top",_) -> ()
	       | TyC(TyVar "Unit",_) -> ps "[]" 
	       | _ -> ps "["; ftype ty1 0 0; ps "]"
	     end 
       end

   | Linty ty -> 
       let needsParens = 
	 prec_app <= left_prec || 
	 prec_app < right_prec
       in
       open_box fIndent;       
       if needsParens 
       then (
	 lpn();
      	 ps "lin ";
	 ftype ty 0 prec_funty;
	 rpn()
	)
       else (
      	 ps "lin ";
	 ftype ty left_prec prec_funty  
	);
       close_box();

   | Ref ty -> 
       let needsParens = 
	 prec_app <= left_prec || 
	 prec_app < right_prec
       in
       open_box fIndent;       
       if needsParens 
       then (
	 lpn();
      	 ps "ref ";
	 ftype ty 0 prec_funty;
	 rpn()
	)
       else (
      	 ps "ref ";
	 ftype ty left_prec prec_funty  
	);
       close_box();

   | Array ty -> 
       let needsParens = 
	 prec_app <= left_prec || 
	 prec_app < right_prec
       in
       open_box fIndent;       
       if needsParens 
       then (
	 lpn();
      	 ps "array ";
	 ftype ty 0 prec_funty;
	 rpn()
	)
       else (
      	 ps "array ";
	 ftype ty left_prec prec_funty  
	);
       close_box();

   | Quant(x,ty) ->  
       let needsParens = 
	 prec_forall < left_prec 
	   || prec_forall <= right_prec
       in
       if needsParens then lpn();
       ps "all ";
       format_tyvar tidy x f_string_tbl next_f_string;
       ps "."; 
       ftype ty 0 0;
       if needsParens then rpn();

 in 
 ftype ty 0 0;
 print_flush()
;;

let format_specialisation pty = 
  if get_mode "specialise" = Show_on  
  then 
    begin 
      ps "specialising at ";
      format_type true pty; 
      ps " ...";
      print_newline();
      Format.print_flush()
    end 
;;


let format_sub sub = 
  let f tyv ty =
    format_untidy_tyvar tyv;
    ps " |-> ";
    format_type false ty;
    pf ""
  in
pf" the sub is:\n";
  TyMap.iter f sub
;;

let format_datum d = ps (string_of_datum_value d)

let rec format_term_variable = function
  | Var y -> ps y
  | Mvar n  -> ps ("mvar_" ^(string_of_int n))
;;

let format_sEnv sub sEnv = 
  let fs x ty = 
    format_term_variable x; 
    ps ":";
    format_type false (applySub sub ty);
    print_newline()
  in 
  ps "["; 
  TMap.iter fs sEnv;
  pf "]" ;
  print_newline();
  print_flush()
;;


let rec do_format t' left_prec right_prec =
  match t' with
  | Tvar (x,n) -> 
      format_term_variable x; 
      if get_mode "declaration_index" = Show_on then printf "_%d" n
  | Tnextvar -> ps "nextvar" 
  | Tsuper (x,_) -> ps "super."; format_term_variable x
  | Twildcard str -> ps ("_"^str)
  | Twildstring -> ps "wildstring"
  | Tconstructor (x,n) ->  
      format_term_variable x; 
      if get_mode "declaration_index" = Show_on then printf "_%d" n
  | Datum d -> ps (string_of_datum_value d)
	
  | Oper("cond",[t1;t2;t3]) ->
      ps ("(if " ) ;
      do_format t1 0 0;
      ps " then ";
      do_format t2 0 0;
      ps " else ";
      do_format t3 0 0;
      ps ")"
	
  | Oper("assign",[t1;t2]) -> 
      do_format t1 0 0;
      pf " = "; 
      do_format t2 0 0
	
  | Oper(str,args) -> ps (str^"("); format_arg_list  args; ps ")" 

(*> CPC *)
  | Tpapp(t1,t2,_)
(*< CPC *)
  | Apply(t1,t2) ->
      begin
        let needParens = prec_app <= left_prec || prec_app < right_prec in
        open_box 0;
        do_format t1 left_prec prec_app;
        print_space();
        if needParens 
	then begin
	  lpn();
          do_format t2 prec_app 0; 
          rpn()
        end 
	else do_format t2 prec_app right_prec;
        close_box()
      end
	
  | Lam(x,s) -> 
      lpn();
      format_term_variable x ;
      ps " -> " ;
      do_format s 0 0;
     rpn()	
(*> CPC *)
  | Tdname (ty,d,_) -> (if ty = P_data.Protected then ps "~" else ());do_format d 0 0
  | Tcname (nt,id,_,_)
  | Tname(nt,id,_,_) ->
        (match nt with
        | Variable -> ()
        | Protected -> ps "~"
        | Binding -> ps "\\");
        format_term_variable id
  
  | Prll(p1,p2) -> ps "(";do_format p1 0 0;ps ") | (";do_format p2 0 0;ps ")"
  
  | Rest(x,p) -> ps "(v "; format_term_variable x; ps ")"; do_format p 0 0
  
  | Repl (p) -> ps "!";do_format p 0 0
  
  | Pcase (p,s) -> do_format (Case(None,p,s)) 0 0
(*< CPC *)
 
 | Case (None,p,s) -> 
      lpn();
      do_format p 0 0 ;
      ps " -> ";                 
      do_format s 0 0;
      rpn()

  | Case (Some theta,p,s) -> 
      lpn();
      ps "{";
      List.iter (fun x -> 
	format_term_variable x;
		ps ",") theta ;
      ps "}";
      do_format p 0 0 ;
      ps " -> ";                 
      do_format s 0 0;
      rpn();
 
  | Choice (s,t) -> 
      do_format s left_prec prec_app;
      ps " | "; 
      do_format t prec_app right_prec

  | Over (s,t) -> 
      do_format s left_prec prec_app;
      ps " | "; 
      do_format t prec_app right_prec

  | Addcase (x,t,_) -> 
      lpn();
      format_term_variable x ;
      ps " += " ;
      do_format t 0 0;
      rpn()

  | Subcase x -> 
      ps "generalise ";
      format_term_variable x 

  | Tlet (status,x,t1,t2) ->  (* print the status!! *) 
      ps "let ";
      format_term_variable  x;
      ps " = "; 
      do_format t1 0 0;
      ps " in ";
      do_format t2 0 right_prec;
      
 (* delete 
 | Tletrec (x,t1,t2) ->
      ps "letrec ";
      format_term_variable  x;
      ps " = "; 
      do_format t1 0 0;
      ps " in ";
      do_format t2 0 right_prec;
      
  | Tletext (x,t1,t2) ->
      ps "letext ";
      format_term_variable  x;
      ps " = "; 
      do_format t1 0 0;
      ps " in ";
      do_format t2 0 right_prec;
      
  | Tletdiscontinuous (x,t1,t2) ->
      ps "letdiscontinuous ";
      format_term_variable  x;
      ps " = "; 
      do_format t1 0 0;
      ps " in ";
      do_format t2 0 right_prec;
      *)

  | TnewArr (t,n) -> 
      ps "newArray ";
      do_format t 0 0;
      ps " " ;
      do_format n 0 0

and format_arg_list = function
    [t] -> do_format t 0 0
  | t::ts -> do_format t 0 0 ; ps ","; format_arg_list ts 
  | [] -> ()
	
and format_closure clos str = 
  let f x y = 
    format_term_variable x;
    ps " |-> ";
    format_term_variable y;
    ps " " ;
    flush stdout;
  in 
  TMap.iter f clos;
  pf (" is "^str)
    
let format_term t = 
  open_box 0;
  do_format t 0 0;
  close_box(); 
  print_flush()
;;



(* formatting values *)

let rec format_value = function
  | Vvar x -> format_term_variable x
  | Vsuper x -> format_value x; ps ".super"
  | Vwildcard str -> ps ("_"^str)
  | Vwildstring -> ps "wildstring"
  | Vconstructor (x,n) -> format_term_variable x
  | Vdatum d -> ps (string_of_datum_value d)
  | Vapply(x1,x2) ->
      format_value x1;
      print_space();
      format_value x2;
  | Vchoice(x1,x2) ->
      format_value x1;
      ps " | ";
      format_value x2;
  | _ -> ps "..."


(* peeking *)

let peek_type ty msg = 
  format_type false ty; 
  print_flush(); 
  pf (" is " ^msg) ; 
  print_flush()
;;

let peek_tyvs delta msg = 
pf "[";
iter (fun x ->   format_type false (TyV(x,0)); pf ","; print_flush() ) delta;
pf ("] is "^msg);
  print_flush()
;;


let peek t str = format_term t; print_flush(); pf (" is " ^ str)

let peeks ts str = List.iter (fun x -> peek x str) ts 

let peek_value v str = format_value v; print_flush(); pf (" is " ^ str)

let peek_value v str = format_value v; print_flush (); pf (" is " ^ str)




(*** Errors *)

let formatTypeError sub (tys,s) = 

  let form_in_box ty = 
    open_box 2;
    format_type false (applySub sub ty);
    close_box()
  in

  match tys with 
    [ty] -> 
      open_box 0;
      ps ("type error: ");
      form_in_box ty;
      ps (" "^s);
      close_box();
      print_newline()

  | [ty1;ty2] -> 
      open_box 0;
      ps ("type error: ");
      form_in_box ty1;
      ps " and ";
      form_in_box ty2;
      ps (" "^s);
      close_box();
      print_newline()

  | [ty1;ty2;ty3] -> 
      open_box 0;
      ps ("type error: ");
      form_in_box ty1;
      ps " and ";
      form_in_box ty2;
      ps " and ";
      form_in_box ty3;
      ps (" "^s);
      close_box();
      print_newline()

  | _ -> pf "unformatted type error"
;;

let formatTermError (ts,s) = 

  let form_in_box t =
try 
    open_box termIndent;
    format_term t;
    close_box()
with _ -> pf "cannot format term error"
  in

  match ts with
    [t] ->
      open_box 0;
      ps ("term error: ");
      form_in_box t;
      ps (" "^s);
      close_box();
      print_newline()

  | [t1;t2] ->
      open_box 0;
      ps ("term error: ");
      form_in_box t1;
      ps " and ";
      form_in_box t2;
      ps (" "^s);
      close_box();
      print_newline()

  | [t1;t2;t3] ->
      open_box 0;
      ps ("term error: ");
      form_in_box t1;
      ps " and ";
      form_in_box t2;
      ps " and ";
      form_in_box t3;
      ps (" "^s);
      close_box();
      print_newline()

  | _ -> pf "unformatted term error"
;;


(*> CPC *)
(* Create a lock/unlock pair to allow resource locking. *)
let new_lock () =
  let mutex = Mutex.create () in
  (fun () -> Mutex.lock mutex),(fun () -> Mutex.unlock mutex)

(* A lock that may or may not be lockable. Returns true if the
 * lock is obtained, false otherwise. *)
let optlock () =
  let mutex = Mutex.create () in
  (fun () -> Mutex.try_lock mutex),(fun () -> Mutex.unlock mutex)

(* Code to uniquely generate numbers (thread safe). *)
let new_generator gen =
  let counter = ref 0 in
  let l,ul = new_lock () in
  let next () = l (); incr counter; let res = gen !counter in ul (); res in
  next
;;

(* Create process environment. *)
let procEnv = Hashtbl.create 100;;

(* Shows the processes currently in the process environment. *)
let show_status () =
  let show_proc ppid (_,_,_,p) =
    let pidstr = string_of_int ppid in
    ps ("Process with ID " ^ pidstr ^ ":");
    format_term p;
    print_newline()
  in
  Hashtbl.iter show_proc procEnv
;;

(* A generator for unique machine variables. *)
let nextvar = new_generator (fun x -> Mvar x);;

(* A local generator for process ID's. *)
let procGen = new_generator (fun x -> x);;
(*< CPC *)



let rec freeRefTyVars   ty = 
match restore_class ty with 
| Some (tyv,n,zs,ty1) -> 
    let generic_type_number = 
      try 
	match gTyEnvFind n tyv with 
	| (_,Class(_,_,_,k)) -> k
	| _ -> basicError "freeRefTyVars produces a non-class"
      with _ -> basicError "freeRefTyVars produces an unknown class"
    in 
    handle_args (freeRefTyVars ty1) (zs,generic_type_number)

| None -> 
    match ty with 
    | TyV (_,_)  
    | TyC (_,_) -> []
    | ApplyF (g,f) 
    | ChoiceF (g,f) 
    | SuperF (g,f) -> append (freeRefTyVars g) (freeRefTyVars f)
    | Funty (g,f) -> fold_right list_remove (freeTyVars idSub g) (freeRefTyVars f) 
	         (* the use of freeTyVars above is *not safe !!! 
		    It allows for make methods, but make Nil will be problematic. *) 
    | Linty ty -> freeRefTyVars ty 
    | Ref ty 
    | Array ty -> freeTyVars idSub ty 
    | Quant(x,ty) -> list_remove x (freeRefTyVars ty)

and handle_args rvs = function
  | (argtys,k) -> 
      if k<=0 
      then fold_left handle_args_simple rvs argtys
      else 
	match argtys with 
	| [] -> rvs 
	| f :: argtys1 -> handle_args (append (freeTyVars idSub f) rvs) (argtys,k-1)

and handle_args_simple rvs ty = append (freeRefTyVars ty) rvs
;; 
