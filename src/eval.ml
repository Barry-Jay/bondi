open List
open Format
open Datum
open P_data
open Environments
open Infer


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

(*> CPC *)
(* A queue to store CPC processes structures that need to be
 * added to the process environment. Each entry in the queue
 * should be a tuple of a lock, unlock, value environment and
 * the process (i_term). *)
let proc_queue = ref [];;

(* Locks for the process queue. *)
let pqlock,pqunlock = new_lock ();;

(*< CPC *)

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
(*> CPC *)
  (* Note that spawn and sleep are updated/new with CPC, but not
   * part of CPC conceptually. *)
  | Oper("spawn",[t1]) -> eval_spawn vEnv t1
  | Oper("sleep",[Datum(Float f)]) -> Thread.delay f; Vdatum Un
  | Prll(p1,p2) -> eval_parallel_composition vEnv p1 p2
  | Rest(x,p) -> eval_restriction vEnv x p
  | Repl(p) -> eval_replication vEnv p
  | Pcase(_,_) -> eval_process_case vEnv term
(*< CPC *)
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

(*> CPC *)
(* Using threads or jocaml "spawn" leaks memory, instead use CPC code.
 * Create a new (unique) name like a restriction and then spawn two
 * CPC processes that will only match that protected new name. One
 * reduces to the term we wanted to spawn, the other to nothing/unit. *)
and eval_spawn vEnv t =
  let n = nextvar () in
  let vEnv1 = TMap.add n (Vvar(n)) vEnv in
  let pTy = TyV(nextTypeVar(),0) in
  let p = Tname(P_data.Protected,n,0,pTy) in
  let t1 = Prll(Pcase(p,t),Pcase(p,Datum(Datum.Un))) in
  eval (vEnv1,t1)

(* Top level parallel composition, simply evaluate the processes
 * individually. *)
and eval_parallel_composition vEnv p1 p2 =
  let pA,pB = if Random.int 2 = 1 then p1,p2 else p2,p1 in
  let _ = eval (vEnv,pA) in
  let _ = eval (vEnv,pB) in
  Vdatum Datum.Un

(* Instantiate the restricted name to a fresh machine variable
 * and then continue evaluation.
 * Note: restrictions can occur over any bondi term here, but should
 * be caught in parsing. *)
and eval_restriction vEnv name proc =
  let name1 = nextvar () in
  let vEnv1 = TMap.add name (Vvar(name1)) vEnv in
  eval(vEnv1,proc)

(* Helper function to add a tuple to the process queue. *)
and add_to_proc_queue x =
  pqlock();
  proc_queue := x::!proc_queue;
  pqunlock();
  Vdatum Datum.Un

(* Remove excess replications, continue until the process
 * under the replication is either a restriction or a case. *)
and eval_replication pEnv = function
  (* !(P|Q) is close enough to !P|!Q that we shall use the second form
   * to simplify the matching algorithm. *)
  | Prll(p1,p2) -> let _ = (eval_replication pEnv p1,
                            eval_replication pEnv p2) in
                   Vdatum Datum.Un
  (* !(!P) is close enough to !P that we use the latter. *)
  | Repl(p) -> eval_replication pEnv p
  (* Replications can always be locked and require no effect to unlock. *)
  | p ->  let l,ul = (fun () -> true),(fun () -> ()) in
          add_to_proc_queue (l,ul,pEnv,Repl(p))

(* Just add the CPC case to the queue, the rest is done
 * by the CPC engine later. *)
and eval_process_case pEnv pcase =
  let l,ul = optlock () in
  add_to_proc_queue (l,ul,pEnv,pcase)
;;

(* Determines if a pattern is communicable and
 * also the type information for the pattern. *)
let rec communicable = function
  | Tname(P_data.Variable,_,_,ty) -> (true,ty)
  | Tcname(P_data.Variable,_,_,ty) -> (true,ty)
  | Tdname(P_data.Variable,Datum((* d *) _ ),ty) -> (true,ty)
  | Tpapp(l,r,ty) ->
      begin
        match communicable l with
        | (false,_) -> (false,ty)
        | (true, (* funcTy *) _) -> let (ok, (* argTy *) _) = 
           communicable r in
           (ok,ty)
      end
  | _ -> (false,TyV(nextTypeVar(),0))
;;

(* We have bound a communicable pattern, strip out CPC details. *)
let rec unCPCPattern = function
  | Tname(_,v,n,_) -> Tvar(v,n)
  | Tcname(_,v,n,_) -> Tconstructor(v,n)
  | Tdname(_,d,_) -> d
  | Tpapp(l,r,_) -> Apply(unCPCPattern l,unCPCPattern r)
  | _ -> Tconstructor (Var "Exception",0)
;;

(* A pattern is a free pattern if it contains no binding names.
 * Note: as this is required for type safety, when the type
 *       system is disabled, always return true (pattern
 *       unification will handle the rest). *)
let freePattern patt =
  let rec inner = function
  | Tname(P_data.Binding,_,_,_) -> false
  | Tpapp(l,r,_) -> inner l && inner r
  | _ -> true
  in
  if get_mode "types" = Show_off
  then true
  else inner patt
;;

(* Get a type substitution from an environment.
 * This only works for the "special" type substitution
 * stored as machine variable -1, reserved for CPC. *)
let getTySub env =
  try
    begin
      match TMap.find (Mvar(-1)) env with
      | VtySub(s) -> s
      | _ -> TyMap.empty
    end
  with Not_found -> TyMap.empty
;;

(* Try to unify two patterns with respective environments and
 * built up substtitions, success is Some of substitutions,
 * failure is None. *)
let rec unify1 (pEnv,qEnv) (subp,subq) = function
  (* When simple names/variables are involved, compare their evaluated values. *)
  | (Tname(P_data.Variable,pv,pn,_),Tname(P_data.Variable,qv,qn,_))
  | (Tname(P_data.Variable,pv,pn,_),Tname(P_data.Protected,qv,qn,_))
  | (Tname(P_data.Protected,pv,pn,_),Tname(P_data.Variable,qv,qn,_))
  | (Tname(P_data.Protected,pv,pn,_),Tname(P_data.Protected,qv,qn,_))
          -> if evalVar pEnv pv pn = evalVar qEnv qv qn then Some (subp,subq) else None
  (* If one pattern is a binding name then ensure the other is
   * communicable and determine it's type. Check that
   * the binding is type safe, if so bind, otherwise fail. *)
  | (Tname(P_data.Binding,bp,_,pTy),qv) ->
          begin
            match communicable qv with
            | (false,_) -> None
            | (true,qTy) ->
                try
                  begin
                    let sub = unify_for_cpc (getTySub pEnv) (getTySub qEnv) pTy qTy in
                    Some(TMap.add bp (eval (qEnv,(unCPCPattern qv)))
                            (TMap.add (Mvar(-1)) (VtySub(sub)) subp),
                         subq)
                  end
                with _ -> None
          end
  | (pv,Tname(P_data.Binding,qb,_,qTy)) ->
          begin
            match communicable pv with
            | (false,_) -> None
            | (true,pTy) ->
                try
                  begin
                    let sub = unify_for_cpc (getTySub qEnv) (getTySub pEnv) qTy pTy in
                    Some (subp,
                          TMap.add qb (eval (pEnv,(unCPCPattern pv)))
                              (TMap.add (Mvar(-1)) (VtySub(sub)) subq))
                  end
                with _ -> None
          end 
  (* Do application component wise. *)
  | (Tpapp(p1,p2,_),Tpapp(q1,q2,_)) ->
          begin
            match unify1 (pEnv,qEnv) (subp,subq) (p1,q1) with
            | Some (subp1,subq1) -> unify1 (pEnv,qEnv) (subp1,subq1) (p2,q2)
            | None -> None
          end
  (* One is an application and the other is a non-binding name,
   * should evaluate the name to see if it is also an application
   * (bondi data structure).
   * WARNING: current implementation does not consider compounds
   *          that have binding names in them. Binding names
   *          require type unification/checking and this is not
   *          possible for the components of arbitrary compounds. *)
  (* A first improvement, if there are no binding names in the compound
   * pattern then no typing issues can occur, proceed.
   * NOTE: the type information passed through is WRONG, this
   *       is fine as no bindings occur and so types do not
   *       need to be unified. *)
  | (Tpapp(_,_,_) as p,Tname(qf,qv,qn,qTy)) when qf != P_data.Binding && freePattern p ->
          begin
            match evalVar qEnv qv qn with
            | Vapply(qVal1,qVal2) -> let qv1 = nextvar () in
                                     let qv2 = nextvar () in
                                     let qEnv1 = TMap.add qv1 qVal1 (TMap.add qv2 qVal2 qEnv) in
                                     let q1 = Tname(qf,qv1,0,qTy) in
                                     let q2 = Tname(qf,qv2,0,qTy) in
                                     unify1 (pEnv,qEnv1) (subp,subq) (p,Tpapp(q1,q2,qTy))
            | _ -> None
          end
  | (Tname(pf,pv,pn,pTy),(Tpapp(_,_,_) as q)) when pf != P_data.Binding && freePattern q ->
          begin
            match evalVar pEnv pv pn with
            | Vapply(pVal1,pVal2) -> let pv1 = nextvar () in
                                     let pv2 = nextvar () in
                                     let pEnv1 = TMap.add pv1 pVal1 (TMap.add pv2 pVal2 pEnv) in
                                     let p1 = Tname(pf,pv1,0,pTy) in
                                     let p2 = Tname(pf,pv2,0,pTy) in
                                     unify1 (pEnv1,qEnv) (subp,subq) (Tpapp(p1,p2,pTy),q)
            | _ -> None
          end
  (* Constructors in patterns can add complexities, easiest to augment local
   * environment. *)
  | (Tcname(pt,pv,pn,pTy),q) ->
          let pv1 = nextvar () in
          let pEnv1 = TMap.add pv1 (Vconstructor (pv,pn)) pEnv in
          unify1 (pEnv1,qEnv) (subp,subq) (Tname(pt,pv1,0,pTy),q)
  | (p,Tcname(qt,qv,qn,qTy)) ->
          let qv1 = nextvar () in
          let qEnv1 = TMap.add qv1 (Vconstructor (qv,qn)) qEnv in
          unify1 (pEnv,qEnv1) (subp,subq) (p,Tname(qt,qv1,0,qTy))
  (* Datum in patterns, simply treat like a constructor. *)
  | (Tdname(pt,Datum(pd),pTy),q) ->
          let pv1 = nextvar () in
          let pEnv1 = TMap.add pv1 (Vdatum pd) pEnv in
          unify1 (pEnv1,qEnv) (subp,subq) (Tname(pt,pv1,0,pTy),q)
  | (p,Tdname(qt,Datum(qd),qTy)) ->
          let qv1 = nextvar () in
          let qEnv1 = TMap.add qv1 (Vdatum qd) qEnv in
          unify1 (pEnv,qEnv1) (subp,subq) (p,Tname(qt,qv1,0,qTy))
  (* Unable to unify other things, fail. *)
  | _ -> None
;;

(* Unification, begin with empty substitutions on both sides. *)
let unify pEnv qEnv p q = unify1 (pEnv,qEnv) (TMap.empty,TMap.empty) (p,q);;

(* A new attempt to see if two processes can interact for general
 * process forms; i.e. cases, replications and restrictions.
 * Result is if there is interaction between p and q, internal
 * interactions within p or q will not be accounted for!
 * Note that the process is locked, so we can mess with it here,
 * but will need to account for cleaning up and things like that. *)
let rec interactable1 pE qE p q =
  match(p,q) with
  (* Restrictions that must be underneath a replication, can
   * instantiate the name to try and match. *)
  | (Rest(n,p1),_) ->   let n1 = nextvar() in
                        let pE1 = TMap.add n (Vvar(n1)) pE in
                        interactable1 pE1 qE p1 q
  | (_,Rest(n,q1)) ->   let n1 = nextvar() in
                        let qE1 = TMap.add n (Vvar(n1)) qE in
                        interactable1 pE qE1 p q1
  (* Parallel composition underneath a replication/restriction.
   * Note that this only tests against p and q matching each
    * other, internal reductions are done elsewhere. *)
  | (Prll(p1,p2),_) ->
        begin
          let pA,pB = if Random.int 2 = 1 then p1,p2 else p2,p1 in
          match interactable1 pE qE pA q with
          | Some cont -> Some (fun () -> cont (); ignore (eval(pE,pB)))
          | None ->
              begin
                match interactable1 pE qE pB q with
                | Some cont -> Some (fun () -> cont (); ignore (eval(pE,pA)))
                | None -> None
              end
        end
  | (_,Prll(q1,q2)) ->
        begin
          let qA,qB = if Random.int 2 = 1 then q1,q2 else q2,q1 in
          match interactable1 pE qE p qA with
          | Some cont -> Some (fun () -> cont (); ignore (eval(qE,qB)))
          | None ->
              begin
                match interactable1 pE qE p qB with
                | Some cont -> Some (fun () -> cont (); ignore (eval(qE,qA)))
                | None -> None
              end
        end
  (* Replication, just try to interact with a copy. If successful we
   * are under a restriction already so we must have a copy of
   * the replicating process with the right restriction/scoping. *)
  | (Repl(p1),_) ->
        begin
          match interactable1 pE qE p1 q with
          | Some cont -> Some (fun () -> cont (); ignore (eval(pE,Repl(p1))))
          | None -> None
        end
  | (_,Repl(q1)) ->
        begin
          match interactable1 pE qE p q1 with
          | Some cont -> Some (fun () -> cont (); ignore (eval(qE,Repl(q1))))
          | None -> None
        end
  (* Two cases, try to match their patterns. *)
  | (Pcase(pp,pb),Pcase(qp,qb)) ->
        begin
          match unify pE qE pp qp with
          | Some (ps,qs) -> Some (fun () ->
                begin
                (* Generate the processes to continue with. *)
                  let pE1 = TMap.fold TMap.add ps pE in
                  let qE1 = TMap.fold TMap.add qs qE in
                  let _,_ = (eval (pE1,pb)),(eval (qE1,qb)) in ()
                end)
          | None -> None
        end
  | _ -> None (* Should never happen, this is a sanity check! *)
;;

(* A zero step in attempting interaction. If the replication is top
 * level then the outer behaviour will handle it. Otherwise, the
 * inner interactable will add the replicating process to the results. *)
let interactable pEnv qEnv p q =
  match (p,q) with
  | (Repl(p1),Repl(q1)) -> interactable1 pEnv qEnv p1 q1
  | (Repl(p1),_) -> interactable1 pEnv qEnv p1 q
  | (_,Repl(q1)) -> interactable1 pEnv qEnv p q1
  | _ -> interactable1 pEnv qEnv p q
;;

(* A function to invoke self interaction in replicating processes
 * in the process environment.
 * Note that this will never delete a process, only create more. *)
let self_interaction _ (_,_,pEnv,proc) =
  let rec inner_interaction pEnv = function
    | Repl(p) -> inner_interaction pEnv p
    | Rest(n,p) -> let n1 = nextvar() in
                   let pEnv1 = TMap.add n (Vvar(n1)) pEnv in 
                   inner_interaction pEnv1 p
    | Prll(p1,p2) ->
        begin
          (* Add some randomness to prevent deterministic interactions. *)
          let pA,pB = if Random.int 2 = 1 then p1,p2 else p2,p1 in
          let one = fun () ->
            match inner_interaction pEnv pA with
            | Some cont -> Some (fun () -> cont (); ignore (eval(pEnv,pB)))
            | None ->
              begin
                match inner_interaction pEnv pB with
                | Some cont -> Some (fun () -> cont (); ignore (eval(pEnv,pA)))
                | None -> None
              end
          and two = fun () -> interactable1 pEnv pEnv pA pB in
          let first,second = if Random.int 2 = 1 then one,two else two,one in
          match first () with
          | Some cont -> Some cont
          | None -> second ()
        end
    | _ -> None
  in
  match proc with
  | Repl(p) ->
        begin
          match inner_interaction pEnv p with
          | Some cont -> cont ()
          | None -> ()
        end
  | _ -> ()
;;

(* Determine if a process should be removed or not. *)
let to_clean pid ks = function
  | Repl(_) -> ks
  | _ -> pid::ks
;;

(* A foldable function that attempts to interact a CPC process
 * with it's ID (ppid), environment pqE), processes (p) against
 * every other process (qE,q) in the environment. Result is
 * either false if no interaction and the input, or true if
 * there is a interaction with the list of processes IDs to
 * remove from the environment. *)
let foldinteract qpid (ql,qul,qE,q) (succ,ppid,pE,p,ks) =
  if succ || not (ql ())
  then (succ,ppid,pE,p,ks)
  else match interactable pE qE p q with
       | Some cont -> (cont (); (true,ppid,pE,p,to_clean qpid ks q))
       | None -> (qul();(succ,ppid,pE,p,ks))
;;

(* A top level fold that tries to interact every process in
 * the process environment with every other process. Uses
 * foldinteract (above) with each process to try every 
 * possible pair of processes. Accumulates whether any
 * interactions have occurred (succ) and also a list of
 * processes to be removed from the process environment (ks).
 * Note: Now updated to do multiple interactions per pass. *)
let topfoldinteract ppid (pl,pul,pE,p) (succ,ks) =
  if pl()
  then
    begin
      let (r,_,_,_,ks1) = Hashtbl.fold foldinteract procEnv (false,ppid,pE,p,ks) in
      if r
      then (true,to_clean ppid ks1 p)
      else (pul();(succ,ks))
    end
  else (succ,ks)
;;

(* Due to addition usage for generating process IDs and
 * also using process IDs as hash keys the matching tends
 * to favour interactions in order of declaration. To
 * solve this create a random iteration over lists to add
 * the processes from the queue. 
 * Note: Probably not efficient! *)
let randomiter f l =
  let rec donth n = function
    | x::xs when n = 0 -> f x;xs
    | x::xs -> x::(donth (n-1) xs)
    | [] -> []
  in
  let rec inner n = function
  | [] -> ()
  | l -> inner (Random.int (List.length l)) (donth n l)
  in
  let ll = List.length l in
  if ll > 0
  then inner (Random.int ll) l
  else ()
;;

(* An evaluation engine for CPC, goes through a constant
 * cycle to add processes to the environment, try to match them all
 * and then clean up. *)
let procManager () =
  let addprocs () =
    pqlock();
    randomiter (fun x -> Hashtbl.add procEnv (procGen ()) x) !proc_queue;
    proc_queue := [];
    pqunlock()
  in
  while true do
    Thread.delay 0.1;
    addprocs ();
    Hashtbl.iter self_interaction procEnv; 
    let (r,ks) = Hashtbl.fold topfoldinteract procEnv (false,[]) in
    if r
    then List.iter (Hashtbl.remove procEnv) ks
  done
;;

(* Spawn a number of different CPC process managers in
 * separate threads.
 * Note: each manager uses ~8MB memory. *)
let createManagers n =
  let rec inner i xs =
    if i = n
    then xs
    else inner (i+1) ((Thread.create procManager ())::xs)
  in
  inner 0 []
;;

(* Create two process managers *)
let tids = createManagers 2;;

(*< CPC *)

let evaluate term = eval (TMap.empty,term)

