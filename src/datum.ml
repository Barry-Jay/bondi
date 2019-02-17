open List
open Format

module OrderedStrings  = 
  struct 
    type t = string
    let compare str1 str2 = String.compare str1 str2 
  end

(* A string map to hold ALL the operators *)
module StringMap = Map.Make(OrderedStrings);;

(* A string map to hold the N-ary operators, note that they will also
 * appear in the generic string map above, this is an optimisation *)
module NStringMap = Map.Make(OrderedStrings);;

type datum_value =
    Int of int
  | Float of float
  | Char of char
  | String of string
  | Bool of bool 
  | Socket     of Unix.file_descr * Pervasives.in_channel * (Pervasives.out_channel * bool) * string 
  (* Sockets are linked to uni file descriptors and all have an input and an output channel as
   * well as a description. The boolean determines if an output channel can be flushed.
   * Note that server sockets (but not clients) cannot be flushed and the code uses this
   * detail to prevent any reading/writing on server channels. This is overly protective, you can
   * read and write to a server socket - but the behaviour is unspecified and may generate exceptions,
   * do so as your own risk! *)
  | Host       of Unix.host_entry
  | Un
;;


exception Error of string;;
let basicError msg = raise (Error msg)

let datum_equal = function
    (Int x1,Int x2) ->  x1 == x2 
  | (Float x1,Float x2) -> x1 == x2 
  | (Char x1,Char x2) -> x1 == x2 
  | (String x1,String x2) -> x1 == x2 
  | (Bool x1,Bool x2) -> x1 == x2
  | (Un,Un) -> true
  | _ -> false 

let datum_type_string = function
    Int _ -> "Int" 
  | Float _ ->  "Float" 
  | Char _ -> "Char"
  | String _ -> "String" 
  | Bool _ ->  "Bool"
  | Socket     _ ->  "Socket"
  | Host       _ ->  "Host"
  | Un           ->  "Unit"         

let int_ops_bss = [
  
  "plusint";
  "minusint";
  "timesint";
  "divideint";
  "modint"
] 

and int_ops1 = [
  "negateint";
  "randomint";
]


and float_ops1 = [

  "acos";
  "asin";
  "atan";
  "ceil";
  "cos";
  "cosh";
  "exponential";
  "fabs";
  "floor";
  "log";
  "log10";
  "negatefloat";
  "randomfloat";
  "sin";
  "sinh";
  "sqrt";
  "tan";
  "tanh"
] 

and float_ops_bss = [ 

  "plusfloat";
  "minusfloat";
  "timesfloat";
  "dividefloat";
  "atan2";
  "fmod";
  "pow"
]

and int_rels = [ 

  "lessthanint";
  "lessthanorequalint";
  "greaterthanint";
  "greaterthanorequalint"
] 

and float_rels = [ 
  "lessthanfloat";
  "lessthanorequalfloat";
  "greaterthanfloat";
  "greaterthanorequalfloat"
] 

and char_rels = [ 
  "lessthanchar";
  "lessthanorequalchar";
  "greaterthanchar";
  "greaterthanorequalchar"
] 

and string_rels = [ 
  "lessthanstring";
  "lessthanorequalstring";
  "greaterthanstring";
  "greaterthanorequalstring"
] 


let binary str op = StringMap.add op ([str;str], str) 
let unary str op = StringMap.add op ([str], str) 
let rel_op str op = StringMap.add op ([str;str], "Bool") 

(* All the operators 
 * NOTE: Type signature in the list is in REVERSE ORDER to the usage!!!!!! *)
let all_ops =
fold_right (binary "Int") int_ops_bss (
  fold_right (binary "Float") float_ops_bss (
  fold_right (unary "Int") int_ops1 (
  fold_right (unary "Float") float_ops1 (
  fold_right (rel_op "Int") int_rels (
  fold_right (rel_op "Float") float_rels (
  fold_right (rel_op "Char") char_rels (
  fold_right (rel_op "String") string_rels (
  StringMap.add "char2int" (["Char"],"Int") (
  StringMap.add "int2float" (["Int"],"Float") (
  StringMap.add "int2string" (["Int"],"String") (
  StringMap.add "float2string" (["Float"], "String") (
  StringMap.add "truncate" (["Float"],"Int") (
  StringMap.add "concat" (["String";"String"],"String") (
  StringMap.add "getcharstring" (["Int";"String"],"Char") (
  StringMap.add "makestring" (["Char";"Int"],"String") (
  StringMap.add "indexstring" (["Char";"String"],"Int") (
  StringMap.add "rindexstring" (["Char";"String"],"Int") (
  StringMap.add "containsstring" (["Char";"String"],"Bool") (
  StringMap.add "copystring" (["String"],"String") (
  StringMap.add "escapedstring" (["String"],"String") (
  StringMap.add "escapecsv" (["String"], "String") (
  StringMap.add "lengthstring" (["String"],"Int") (
  StringMap.add "uppercasestring" (["String"],"String") (
  StringMap.add "substring" (["Int";"Int";"String"],"String") (
  StringMap.add "indexfromstring" (["Char";"Int";"String"],"Int") (
  StringMap.add "containsfromstring" (["Char";"Int";"String"],"Bool") (
  StringMap.add "capitalizestring" (["String"],"String") (
  StringMap.add "printchar" (["Char"],"Unit") ( 
  StringMap.add "printstring" (["String"],"Unit") ( 
  StringMap.add "printlnstring" (["String"],"Unit") (
  StringMap.add "string2bool"  (["String"],"Bool") (
  StringMap.add "string2int"   (["String"],"Int") (
  StringMap.add "string2float" (["String"],"Float") (
(* System calls *)
  StringMap.add "sysexec" (["String"],"Int") (
(* Networking operations *)
  StringMap.add "openserver" (["Int";"Host"],"Socket") (
  StringMap.add "opentcp" (["Int";"Host"],"Socket") (
  StringMap.add "openfile" (["String"],"Socket") (
  StringMap.add "gethost"   (["String"],"Host") (
  StringMap.add "write" (["Socket";"String"],"Unit") (
  StringMap.add "writeline" (["Socket";"String"],"Unit") (
  StringMap.add "readline" (["Socket"],"String") (
  StringMap.add "readall" (["Socket"],"String") (
  StringMap.add "close" (["Socket"],"Unit") (
  StringMap.add "acceptclient" (["Socket"],"Socket") (
  StringMap.empty
)))))))))))))))))))))))))))))))))))))))))))))
;;


(* These are needed seperately by the parser and so duplicated from the above "all_ops"
 * this is purely an optimisation, they could be seperated entirely if that would be clearer 
 * NOTE:  Type signature in the list is in REVERSE ORDER to the usage!!!!!! *)
let nary_ops = 
  NStringMap.add "substring" (["Int";"Int";"String"],"String") (
  NStringMap.add "indexfromstring" (["Char";"Int";"String"],"Int") (
  NStringMap.add "containsfromstring" (["Char";"Int";"String"],"Bool") (
(* Networking operations *)
  NStringMap.add "openserver" (["Int";"Host"],"Socket") (
  NStringMap.add "opentcp" (["Int";"Host"],"Socket") (
  NStringMap.add "openfile" (["String"],"Socket") (
  NStringMap.add "gethost"   (["String"],"Host") (
  NStringMap.add "write" (["Socket";"String"],"Unit") (
  NStringMap.add "writeline" (["Socket";"String"],"Unit") (
  NStringMap.add "readline" (["Socket"],"String") (
  NStringMap.add "readall" (["Socket"],"String") (
  NStringMap.add "close" (["Socket"],"Unit") (
  NStringMap.add "acceptclient" (["Socket"],"Socket") (
  NStringMap.empty 
)))))))))))))


(* Helper function to read all the data from a socket until the end of the connection *)
let read in_chan =
    let rec read_inner accum =
      try 
        let ln = input_line in_chan in
        read_inner ((ln ^ "\n")::accum)
      with _ -> accum
    in
    String.concat "" (List.rev (read_inner []))
;;


(* Evaluate a datum d
 * NOTE: In this section the type signature is in the right order... go figure!!!!!! *)
let eval_datum d = function
       	[Int m] -> (
	  match d with 
	    "negateint" -> Int (- m)
	  | "randomint" -> Int (Random.int m)
	  | "int2float" -> Float (Pervasives.float m)
	  | "int2string" -> String (string_of_int m)
	  | _ -> basicError (d^ " is not a unary integer op")
		)
		
      |	[Int m;Int n] -> (
	  match d with 

	    "plusint"   -> Int (m + n)
	  | "timesint"   -> Int (m * n) 
	  | "minusint"   -> Int (m - n)
	  | "divideint" -> Int (m / n)
	  | "modint" -> Int (m mod n)

	  | "lessthanint"  -> 
	      if m < n then (Bool true) else (Bool false)
	  | "lessthanorequalint" -> 
	      if m <= n then (Bool true) else (Bool false)
	  | "greaterthanint"   -> 
	      if m > n then (Bool true) else (Bool false)
	  | "greaterthanorequalint"  -> 
	      if m >= n then (Bool true) else (Bool false)
	  | _ -> basicError (d^" is not a binary integer op")
	    )

      |	[Float n] -> (
	  match d with 
	    "negatefloat" -> Float (-. n) 
	  | "randomfloat" -> Float (Random.float n)
	  | "float2string" -> String (string_of_float n) 
	  | "acos" -> Float (acos n)
	  | "asin" -> Float (asin n)
	  | "atan" -> Float (atan n)
	  | "ceil" -> Float (ceil n)
	  | "cos"  -> Float (cos n)
	  | "cosh" -> Float (cosh n)
	  | "exponential"  -> Float (exp n)
	  | "fabs" -> Float (abs_float n)
	  | "floor"-> Float (floor n)
	  | "log"  -> Float (log n)
	  | "log10"-> Float (log10 n)
	  | "sin"  -> Float (sin n)
	  | "sinh" -> Float (sinh n)
	  | "sqrt" -> Float (sqrt n)
	  | "tan"  -> Float (tan n)
	  | "tanh" -> Float (tanh n)
	  | "truncate" -> Int (truncate n)  
	  | _ -> basicError (d^" is not a unary float op")
		)
      |	[Float m;Float n] -> (
	  match d with 
	  | "plusfloat"  ->Float(m +. n) 
	  | "minusfloat"  -> Float(m -. n) 
	  | "timesfloat"  -> Float(m *. n) 
	  | "dividefloat"  -> Float(m /. n) 
	  | "atan2" -> Float(atan (m/.n))
	  | "fmod"  -> Float(mod_float m n)
	  | "pow"   -> Float(m**n)

	  | "lessthanfloat"  -> 
	      if m < n then (Bool true) else (Bool false) 
	  | "lessthanorequalfloat" -> 
	      if m <= n then (Bool true) else (Bool false)
	  | "greaterthanfloat"   -> 
	      if m > n then (Bool true) else (Bool false) 
	  | "greaterthanorequalfloat"  -> 
	      if m >= n then (Bool true) else (Bool false)
	  | _ -> basicError (d^" is not a binary float op")
		)

      |	[Char m;Char n] -> (
	  match d with 
	  | "lessthanchar"  -> 
	      if m < n then (Bool true) else (Bool false) 
	  | "lessthanorequalchar" -> 
	      if m <= n then (Bool true) else (Bool false)
	  | "greaterthanchar"   -> 
	      if m > n then (Bool true) else (Bool false) 
	  | "greaterthanorequalchar"  -> 
	      if m >= n then (Bool true) else (Bool false)
	  | _ -> basicError (d^" is not a binary character op")
		)

      |	[Char c] -> (
	  match d with 
          | "char2int"  -> Int(Char.code c)
	  | _ -> basicError (d^" is not a unary character op")
		)

      |	[String m;String n] -> (
	  match d with 
	  | "concat"  -> String (m^n)
          | "lessthanstring"  -> 
	      if m < n then (Bool true) else (Bool false) 
	  | "lessthanorequalstring" -> 
	      if m <= n then (Bool true) else (Bool false)
	  | "greaterthanstring"   -> 
	      if m > n then (Bool true) else (Bool false) 
	  | "greaterthanorequalstring"  -> 
	      if m >= n then (Bool true) else (Bool false)
	  | _ -> basicError (d^" is not a binary string op")
		)

      |	[String s] -> (
	  match d with 
          | "sysexec"     -> (match Unix.system s with
                              |   Unix.WEXITED i 
                              |   Unix.WSIGNALED i
                              |   Unix.WSTOPPED i -> Int i)
	  | "copystring"	 -> String s
	  | "escapedstring" -> String (String.escaped s)
          | "lengthstring" -> Int (String.length s)
	  | "capitalizestring" -> String (String.capitalize_ascii s)
	  | "uppercasestring" -> String (String.uppercase_ascii s)
          | "string2bool"  -> Bool (bool_of_string s)
          | "string2int"   -> Int (int_of_string s)
          | "string2float" -> Float (float_of_string s)
	  | "gethost"  -> Host(Unix.gethostbyname s)
          | "openfile" -> let newSock = Unix.openfile s [Unix.O_RDWR; Unix.O_CREAT; Unix.O_APPEND] 0o644 in
                                  let inc = Unix.in_channel_of_descr newSock and
                                      ouc = Unix.out_channel_of_descr newSock in
                                  Socket (newSock,inc,(ouc,true),s)
    | "escapecsv" -> String (Str.global_replace (Str.regexp_string "\"") "\"\"" s)                           
	  | _ -> basicError (d^" is not a unary string op")
		)
(* String operations *)

      | [String s ;Int n] -> (
	  match d with 
	  | "getcharstring"  ->  Char (String.get s n)
	  | _ -> basicError (d^" arguments of type string and int expected")
		)
		
      | [Int len ;Char c] -> (
	  match d with 
	  | "makestring"  ->  String (String.make len c)
	  | _ -> basicError (d^" arguments of type int and char expected")
		)

      | [String s ;Char c] -> (
	  match d with 
	  | "indexstring"  ->  Int (String.index s c)
	  | "rindexstring"  ->  Int (String.rindex s c)
 	  | "containsstring"  ->  
	     if (String.contains s c) then (Bool true) else (Bool false)
	  | _ -> basicError (d^" arguments of type string and char expected")
		)

	| [String s ;Int start; Int len] -> (
	  match d with 
	  | "substring"  ->  String (String.sub s start len)
	  | _ -> basicError (d^" arguments of type Int Int and String are expected")
		)

	| [String s ;Int start; Char c] -> (
	  match d with 
	  | "indexfromstring"  ->  Int (String.index_from s start c)
          | "containsfromstring" -> Bool(String.contains_from s start c)
	  | _ -> basicError (d^" arguments of type Int Int and String are expected")
	
	)
(* Networking operations *)
	| [Host host; Int port] -> (
	  match d with 
          | "openserver" ->  let newSock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
                                     let _ = Unix.setsockopt newSock Unix.SO_REUSEADDR true         in
				     let host_address   = host.Unix.h_addr_list.(0) in
                                     let _ = Unix.bind newSock (Unix.ADDR_INET (host_address, port)) in
                                     let _ = Unix.listen newSock 100  in (* 100 is a magic number that is ignored *)
                                        let inc = Unix.in_channel_of_descr newSock 
				        and ouc = Unix.out_channel_of_descr newSock in 
				     Socket (newSock,inc,(ouc,false),("Server on port "^(string_of_int port)))
          | "opentcp" ->  let newSock = Unix.socket Unix.PF_INET Unix.SOCK_STREAM 0 in
				  let host_address   = host.Unix.h_addr_list.(0) in
				  Unix.connect newSock (Unix.ADDR_INET (host_address, port));
				  let inc = Unix.in_channel_of_descr newSock and
				      ouc = Unix.out_channel_of_descr newSock in
				  Socket (newSock,inc,(ouc,true),((host.Unix.h_name) ^":"^(string_of_int port)))
	  | _ -> basicError (d^" is an unknown Host and Int operator")
	
	)
    (* [Socket (s, i, (o,f), desc)] *)
	| [Socket (s, i, (_,f), _)] -> (
	  match d with 
          | "readline" ->  if f
                                    then String(input_line i)
                                    else String("")
	  | "readall" -> if f
                                    then String(read i)
                                    else String("")
          | "acceptclient" ->  let (clientSock, (* caller *) _) = Unix.accept s in
                                let clientIn  = Unix.in_channel_of_descr clientSock
                                and clientOut = Unix.out_channel_of_descr clientSock in
                                Socket (clientSock,clientIn,(clientOut,true),"Serving client")
	  | "close"   -> Unix.close s;
				Un
	  | _ -> basicError (d^" is an unknown Socket operator")
	
	)           (* Socket (s, i, (o,f), desc) *)
	| [String m; Socket (_, _, (o,f), _)] -> (
	  match d with 
	  | "write" -> if f
                                  then (output_string o m; flush o);
                                  Un
	  | "writeline"  ->  if f
                                      then (output_string o (m^"\n"); flush o);
                                      Un
	  | _ -> basicError (d^" is an unknown String and Socket operator")
	
	)
  	  | (* args *) _ -> printf "%s is an unknown operator" d; basicError (d^" has unsuitable arguments") 
;;	

let prec_op = function

	  | "concat" 
	  | "plusint" 
	  | "minusint" 
	  | "negatint" 
	  | "randomint"
    | "int2string"
    | "float2string"
	  | "plusfloat" 
	  | "minusfloat" 
	  | "negatefloat" 
	  | "randomfloat"
	  | "acos"
	  | "asin"
	  | "atan"
	  | "atan2"
	  | "ceil"
	  | "cos"
	  | "cosh"
	  | "exponential"
	  | "fabs"
	  | "floor"
	  | "fmod"
	  | "int2float"
	  | "log"
	  | "log10"
	  | "pow"
	  | "sin"
	  | "sinh"
	  | "sqrt"
	  | "tan"
	  | "tanh"
	  | "truncate"	  -> 7

	  | "timesint" 
	  | "divideint" 
	  | "timesfloat" 
	  | "divfloat"  -> 8


	  | (* str *) _ -> 6

(* Create a table for all the operators *)
let oper_table = 
  let tbl = Hashtbl.create 53
  in let addEntry s _ = Hashtbl.add tbl s s
  in 
  StringMap.iter addEntry all_ops;
  Hashtbl.add tbl "prim2string" "prim2string" ;
  tbl;;

(* Create a hash table of nary ops, assume 5 as first size as we have 3 currently *)
let noper_table = 
  let tbl = Hashtbl.create 10
  in let addEntry s _ = Hashtbl.add tbl s s
  in 
  NStringMap.iter addEntry nary_ops;
  tbl;

