open List
open Format
open Datum
open P_data
open Environments


(*** stores *) 
let nomatch_string = Vdatum (String "nomatch")
let exception_location = Vconstructor (Var "Exception",0)
let nomatch_location = Vapply(exception_location,nomatch_string)
(*
let un_store = add2store (Vconstructor (Var "Un",0))
let ref_store = add2store (Vconstructor (Var "Ref",0))
*)

let printString = function
| Vdatum (String s) -> Printf.printf "%s" s;flush stdout
| Vwildcard "void" -> Printf.printf "..." ;flush stdout
| (* t *) _ -> basicError "expected a string"  

let printLineString = function
| Vdatum (String s) -> Printf.printf "%s\n" s;flush stdout
| Vwildcard "void" -> Printf.printf "...\n" ;flush stdout
| (* t *) _ -> basicError "expected a string"

let printChar = function
| Vdatum (Char c) -> Printf.printf "%c" c ;flush stdout 
| Vwildcard "void" -> Printf.printf "..." ;flush stdout
| (* t *) _ -> basicError "expected a character"  

(*** evaluation *)

let rec patval vEnv = function
    Tvar (x, (* n *) _) -> Vvar x
  | Twildcard str -> Vwildcard  str
  | Tconstructor (x,n) -> Vconstructor(x,n)
  | Datum d -> Vdatum d
  | Oper("as",[p1;p2]) -> Vas (patval vEnv p1,patval vEnv p2)
  | Oper("where",[p1;t1]) -> Vwhere(patval vEnv p1,t1)
  | Oper("view",[t1;p1]) -> Vview(eval (vEnv,t1),patval vEnv p1)
  | Apply(Tconstructor (Var "Ref",_),p2) -> Vref (ref(patval vEnv p2))
  | Apply(p1,p2) -> Vapply (patval vEnv p1, patval vEnv p2)
  | p -> termError [p] "not a static pattern"


and  (eval : value_env * i_term -> value) = fun (vEnv,term) ->
  (*> CPC *)
  (* Allow multiple evaluation threads to balance better. The argument to
   * Random.int is approximately how many eval cycles to go through
   * before yielding to another thread. This number can be played with
   * for best results... later.
   * Note that the number should be greater then 1, otherwise it is useless. *)
  if Random.int 2 = 0 then Thread.yield ();
  (*< CPC *)
  match term with 
  | Tvar (x,n) -> evalVar vEnv x n 
  | Tnextvar -> Vconstructor(nextvar(),0)
  | Tsuper (x,n) -> Vsuper (evalVar vEnv x n) 
  | Twildcard str -> Vwildcard str
  | Twildstring -> Vwildstring
  | Tconstructor (x,n) -> Vconstructor (x,n)
  | Datum d -> Vdatum d
  | Oper("eqcons",[t1;t2]) -> eval_eqcons (eval (vEnv,t1)) (eval (vEnv,t2)) 
  | Oper("as",[t1;t2]) -> Vas(eval(vEnv,t1),eval(vEnv,t2))
  | Oper("view",[t1;t2]) -> Vview(eval(vEnv,t1),eval(vEnv,t2))
  | Oper("where",[t1;t2]) -> Vwhere (eval(vEnv,t1),t2)
  | Oper("prim2string",[t1]) -> pToString(eval (vEnv,t1))
  | Oper("printstring",[t1]) -> printString(eval (vEnv,t1)); Vdatum Un
  | Oper("printlnstring",[t1]) -> printLineString(eval (vEnv,t1)); Vdatum Un
  | Oper("printchar",[t1]) -> printChar(eval (vEnv,t1)); Vdatum Un
  | Oper("isRef",[t1]) -> evalIsRef vEnv t1
  | Oper("isArray",[t1]) -> evalIsArray vEnv t1
  | Oper("assign",[t1;t2]) -> evalAssign (eval(vEnv,t1)) (eval(vEnv,t2))
  | Oper("deref",[t1]) -> evalDeref (eval(vEnv,t1))
  | Oper("seq",[t1;t2]) -> evalSeq vEnv t1 t2
  | Oper("while",[t1;t2]) -> evalWhile vEnv t1 t2
  | Oper("lengthv",[t1]) -> evalLengthv (eval(vEnv,t1))
  | Oper("entry",[t1;t2]) -> evalEntry (eval(vEnv,t1)) (eval(vEnv,t2))
  | TnewArr (t,n) -> eval_new_arr (eval (vEnv,t)) (eval (vEnv,n))
  | Oper(d,args) -> eval_oper vEnv d args
  | Apply(x,y) -> evalAp vEnv x y 
  | Lam(x,s) -> Vlam(x,ref vEnv,s)
  | Case(theta_opt,p,s) -> eval_case vEnv (theta_opt,p,s)  
  | Choice(s,t) -> eval_choice vEnv s t 
  | Addcase (x,t,ty_opt) -> eval_add_case vEnv x t ty_opt
  | Tlet(Simple,x,u,s) -> evalLet vEnv x u s 
  | Tlet(Recursive,x,u,s) -> evalLetRec vEnv x u s
  | Tlet(Extensible,x,u,s) -> evalLetExt vEnv x u s
  | Tlet(Discontinuous,x,u,s) -> evalLetExt vEnv x u s
  | _ -> basicError "Not currently evaluated!"


and evalVar vEnv x n = 
  if TMap.mem x vEnv 
  then TMap.find x vEnv
  else 
    try fst (snd (envFind n x globalVEnv)) 
    with Not_found -> termError [Tvar(x,n)] "is not recognised"   


and get_datum vEnv t = 
  match (eval(vEnv,t)) with 
    Vdatum d -> d
  | Vwildcard str -> basicError str
  | _ -> basicError "get_datum" 



and pToString x = 
  let str = 
    match x with 
    | Vconstructor (Var x, (* n *) _) -> x
    | Vdatum x -> string_of_datum_value x
    | Vwildcard str -> "_"^str
    | (* t *) _ -> "..." 
  in
  Vdatum (String str)

and evalIsRef vEnv t1 =
let x1 = eval (vEnv,t1) in 
  match x1 with 
  | Vref _ -> Vdatum (Bool true)
  | _ -> Vdatum (Bool false)

and evalIsArray vEnv t1 =
let x1 = eval (vEnv,t1) in 
  match x1 with 
  | Varray _ -> Vdatum (Bool true)
  | _ -> Vdatum (Bool false)


and evalSeq vEnv t1 t2  = 
  let x1 = eval (vEnv,t1) in 
  match x1 with 
  | Vapply(Vconstructor(Var "Exception",0), (* x3 *) _) -> x1
  | _ -> eval (vEnv,t2)

and evalAssign = function
| Vref x -> (fun y -> x := y; Vdatum Un)
| _ -> basicError "assigning to non-reference"

and evalDeref = function
| Vref x -> !x
| _ -> basicError "dereferencing a non-reference"

and evalWhile vEnv t1 t2 = 
match eval (vEnv,t1) with 
| Vdatum(Bool true) -> evalSeq vEnv t2 (Oper("while",[t1;t2]))
| _ -> Vdatum Un


and evalLengthv = function
| Varray xs -> Vdatum (Int (Array.length xs))
| _ -> basicError "unable to determine length of non-array"

and evalEntry = function
| Varray xs -> (function | Vdatum (Int i) -> Array.get xs i
                          | _ -> basicError "Not a valid index")
| _ -> basicError "Not an array."

and eval_oper vEnv d args = 
  try Vdatum (eval_datum d (map (get_datum vEnv) args))
  with 
    Error "void" -> Vapply(Vconstructor (Var "Exception",0),Vdatum (String "void"))
  | Error (* str *) _ -> 
      if get_mode "nomatch" = Show_on 
      then nomatch_location 
      else basicError "a datum operation was mis-applied, perhaps to a wildcard" 


and eval_eqcons x1 x2 =
let res =
match (x1,x2) with
| Vconstructor (y1,n1), Vconstructor (y2,n2) -> (y1,n1) = (y2,n2)
| Vdatum y1, Vdatum y2 -> y1 = y2
| _ -> false
in
Vdatum (Bool res)

and evalAp_opt x0 arg =
  (* produces a variable option, None for match failure *) 
  match x0 with 
  | Vlam(x,vEnv,s) -> Some (eval(TMap.add x arg !vEnv,s))
  | Vcase(x,vEnv,s) -> 
      begin 
	match patternmatch (Some !vEnv) x arg with 
	  Some vEnv1 -> Some (eval (vEnv1,s))
	| None -> None 
      end
 
  | Vchoice(x1,x2) -> 
      begin 
	match evalAp_opt x1 arg with 
	| None -> evalAp_opt x2 arg 
	| Some(Vapply(Vconstructor (Var "Exception",_),Vdatum (String "dynamic_case_inner"))) -> 
                    Some(Vapply(Vconstructor (Var "Exception",0),Vdatum (String "dynamic_case")))
	| Some(Vapply(Vconstructor (Var "Exception",_),Vdatum (String "dynamic_case"))) -> 
                    evalAp_opt x2 arg 
        | y -> y 
      end
  | Vconstructor (Var "Ref",_) -> Some (Vref (ref arg))
  | Vsuper (Vext g) ->   evalSuper !g arg 
  | Vsuper _ -> basicError "super must be applied to a method"
  | Vext g -> evalAp_opt !g arg
  | Vwildstring -> 
      begin 
        match arg with 
        | Vwildcard str -> Some (Vdatum (String str))
        | _ -> Some(Vdatum(String "tame"))
      end 

  | _ -> Some (Vapply(x0,arg))


and evalSuper = function 
    Vchoice(y1,y2) -> fun arg -> 
      begin 
	match evalAp_opt y1 arg with 
	  None -> evalSuper y2 arg 
	| Some _ -> evalAp_opt y2 arg 
      end 		  
  |_ -> basicError "match failure in super"
  

and evalAp vEnv x y =
  match evalAp_opt (eval(vEnv,x)) (eval(vEnv,y)) with 
    Some z -> z 
  | None->  if get_mode "nomatch" = Show_on 
	    then nomatch_location 
	    else termError [Apply(x,y)]  "produces a match failure" 



(* this drops the option which is necessary to handle super! 

and evalApp app arg =
   match app with
   | Vlam(x,vEnv,s) -> eval(TMap.add x arg !vEnv,s)
   | Vcase(x,vEnv,s) ->
                (match patternmatch (Some !vEnv) x arg with
                | Some vEnv1 -> eval (vEnv1,s)
                | None -> if get_mode "nomatch" = Show_on
                          then nomatch_location
                          else basicError "match failure")
   | Vchoice(Vcase(x,vEnv,s),c2) ->
                (match patternmatch (Some !vEnv) x arg with
                | Some vEnv1 -> eval (vEnv1,s)
                | None -> evalApp c2 arg)
   | Vconstructor (Var "Ref",_) -> Vref (ref arg)
   | Vsuper sup ->  evalSuper sup arg 
   | _ -> Vapply(app,arg)

*) 


and (patternmatch : value_env option -> value -> value -> value_env option) = fun vEnv xp y ->
  let check_opt b = if b then vEnv else None  
  in 
  match xp with 
  | Vvar x -> 
      begin 
	match vEnv with 
	| None -> None 
	| Some env -> Some (TMap.add x y env) 
      end 
  | Vwildcard "" -> vEnv
  | Vwildcard "ref" -> 
      begin 
	match y with 
	  Vref _ ->  vEnv
	| _ -> None 
      end 
  | Vwildcard str -> 
      begin 
	match y with 
	  Vdatum d -> check_opt (str = datum_type_string d)
	| Vapply(x1, _) -> 
	    begin
	      match x1 with 
		Vconstructor (Var "Ref",_) -> check_opt (str = "ref") 
	      | _ -> check_opt false 
	    end
	| Varray _ -> check_opt (str = "array")  
	| Vref _ -> check_opt (str = "ref")  
	| Vwildcard str1 -> check_opt (str = str1) 
	|_ -> None 
      end 
  | Vconstructor _  as v -> check_opt (v = y)
  | Vdatum _ as v -> check_opt (v = y)
  | Vapply(x1,x2) -> 
      begin 
	match y with 
	  Vapply(y1,y2) -> patternmatch (patternmatch vEnv x1 y1) x2 y2
      	| _ -> None 
      end
  | Vas(p1,x) -> 
      begin
	match patternmatch vEnv x y with 
	| None -> None
	| vEnv1 -> patternmatch vEnv1 p1 y 
      end 
  | Vview(x1,x2)  -> 
      begin
	match evalAp_opt x1 y with 
	  Some z -> patternmatch vEnv x2 z 
	| None ->  None 
      end 
  | Vwhere(p1,test) -> 
      begin
	match patternmatch vEnv p1 y with
	| Some vEnv1 ->
		begin
		  match eval (vEnv1,test) with
		  | Vdatum(Bool true) -> Some vEnv1
		  | _ -> None
		end
	| None -> None
      end
  | Vref x1 -> 
      begin 
	match y with 
	  Vref y1 -> patternmatch vEnv !x1 !y1 
	| _ -> None 
      end 
  | _ -> None


(* for use with dynamic to static patterns 

and eval_case vEnv (p,s) = Vcase(patval vEnv p,ref vEnv,s)

*) 


and eval_case vEnv (theta_opt,p,s) = 
  let p1 = 
    match theta_opt with 
      None -> patval vEnv p
    | Some theta -> 
	let aux vEnv x = 
	  let y = Vvar x in 
	  TMap.add x y vEnv 
	in 
	let vEnv1 = fold_left aux vEnv theta 
	in 
	eval (vEnv1,p)
  in 
  Vcase(p1,ref vEnv,s) 


and eval_choice vEnv t1 t2 = 
  let x1 = eval (vEnv,t1)
  and x2 = eval (vEnv,t2) 
  in 
  Vchoice(x1,x2)

and eval_add_case vEnv x case (* ty_opt *) _ =
  let newcase = eval (vEnv,case) in
  let oldcaseref =
  try
    (match TMap.find x vEnv with
    | Vext g -> g 
    | _ -> basicError "Extending non-abstraction")
  with Not_found ->
    try
      match fst(snd(envFind 0 x globalVEnv)) with
      | Vext g -> g
      |  _ -> termError [Tvar(x,0)] "is not recognised in eval_add_case"
     with
      TermError(xs,m) -> termError xs m 
    |  _ -> termError [Tvar(x,0)] "is not recognised in eval_add_case"
  in
  oldcaseref := Vchoice(newcase,!oldcaseref);
  Vdatum Un


and evalLet vEnv x u s = 
  let y = eval (vEnv,u) in 
  eval (TMap.add x y vEnv,s) 


and evalLetRec (vEnv : value_env ) x u s =
  let u1 = eval (TMap.remove x vEnv,u) in
  update_envs x u1 u1;
  let vEnv2 = TMap.add x u1 vEnv in
  eval (vEnv2,s)

and update_envs x u = function 
  | Vlam(_,vE,_) 
  | Vcase(_,vE,_) -> vE := TMap.add x u !vE
  | Vchoice (f,g) -> update_envs x u f; update_envs x u g
  | _ -> ()

and evalLetExt vEnv x u s =
  let u1 = Vext (ref (eval (TMap.remove x vEnv,u))) in
  update_envs x u1 u1;
  let vEnv2 = TMap.add x u1 vEnv in
  eval (vEnv2,s)

and eval_new_arr v = function
| Vdatum (Int n) -> 
    let vs = Array.make n v in 
    for i = 0 to (n-1) do Array.set vs i (Vref (ref v)) done;
    Varray vs  (* Varray (Array.make n (Vref (ref v))) *) 
| _ -> basicError "non-integer in length of new array"

and print_value x = 
  let thePrinter = 
  try 
    eval(TMap.empty,tvar "print")
  with _ -> basicError "no default printer--"
  in 
  let _ = evalAp_opt thePrinter x in 
  print_flush()

let evaluate term = eval (TMap.empty,term)

