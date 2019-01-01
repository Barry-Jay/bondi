
(* type of user commands in shell *)

open Printf
open List
open Datum
open P_data
open Environments
open Declare


(*** initialising bondi environments *)

let initial_type_environment() =
  (* dropped "pairF" *) 
  let g name = gTyEnvAdd (TyVar name) 0 (Synonym(cvar name))
  in 
  iter g initial_types 
;;


let constructors = 
  [
   ("Un", cvar "Unit");

  (let x = nextTypeVar() in 
  ("Exception", Quant(x,TyV(x,0))));

   (let x = nextTypeVar() in 
   let y = TyV(x,0) in 
   ("Ref", Quant(x,funty y (Ref y)))) ;

(* make Ref an operator??? *) 


 ]

let add_constructors (name,sch) = 
  envAdd (Var name) 0 (sch,Linear) globalCEnv ;;

let initial_term_environment() = 
List.iter add_constructors constructors

(*** Filesystem *)

let chdir dir =
  Sys.chdir dir; (* raises [Sys_error message] if it fails *)
  print_endline ("New directory: " ^ Sys.getcwd ())

let file_exists = Sys.file_exists
let basic_paths = "." :: (try [System.standard_library] with Not_found -> [])

(* Resolving file names  *)

let full_name name dir = 
  let dir_name = Filename.concat dir name 
  in 
  if file_exists dir_name
  then Some dir_name
  else 
    let bon_name = dir_name ^ ".bon" 
    in 
    if file_exists bon_name
    then Some bon_name
    else None 

let rec path_name name = function 
  | [] -> None 
  | dir :: dirs -> 
      match full_name name dir with 
	None -> path_name name dirs 
      | Some full_name -> Some full_name 



(*** Console *)

(* construct a console lexer object:
   if stdin is a terminal, use gnu_readline if available,
   else, stdin is redirected, just use a standard lexer
 *)


(* let isatty = Config.isatty;; *)
let isatty () = Unix.isatty Unix.stdin;;
let buffer = ref Bytes.empty;;
let action_text = "sourcing"


let ps1 = ref "~~ ";;
let ps2 = ref "> ";;
let (prompt:string ref) = ref !ps1;;

let set_ps1 s = ps1 := s;;
let set_ps2 s = ps2 := s;;
let set_start() = prompt := !ps1;;
let get_prompt() = 
  let tmp = !prompt in
    prompt := !ps2;
    tmp
;;


let prompt_switch = ref false;;
let echo_switch = ref false;;
let number_switch = ref false;;
let line_number = ref 0;;

let set_stdin_prompt_mode (value:bool) = 
  prompt_switch := value;;

let set_stdin_echo_mode (value:bool) = 
  echo_switch := value;;

let set_stdin_number_mode (value:bool) = 
  number_switch := value;;

let std_lexer_func get_line (s:bytes) (maxfill:int)  =
  begin (* prime the buffer *)
    if !buffer = Bytes.empty then begin
      if !prompt_switch then begin
        if !number_switch 
        then print_string (" " ^ (string_of_int !line_number));
        print_string (get_prompt()) 
      end;
      flush stdout;

      begin
        try 
          buffer := (Bytes.of_string (get_line() ^ "\n")); 
          incr line_number
        with  _ ->  buffer := Bytes.empty
      end;
      
      if !number_switch && not !prompt_switch  (* CHANGED & TO && !!!! *)
      then print_string ((string_of_int !line_number) ^ ": ");
      
      if !echo_switch then begin
        print_bytes !buffer; 
        flush stdout
      end
    end
  end;

  let buffer_length = Bytes.length !buffer in
  let toCopy = min maxfill buffer_length in
    Bytes.blit !buffer 0 s 0 toCopy; (* blit the head across *) 
    buffer := Bytes.sub !buffer toCopy (buffer_length - toCopy); 
      (* cut it out of the buffer *)
    toCopy 
;;

let input_channel_line chan () = input_line chan;;

let parseShellListFromChannel chan =
  Lex.runParser
    Parse.parseShellActionList
    (Lexing.from_function (std_lexer_func (input_channel_line chan)))

(*** shell actions and loading *) 

let rec process_action action = 
  f_string_tbl := [];
  f_counter := "";
  let _ = get_declaration_counter() in 
  match action with
  | Let_decl(identifier,(Plet(status,_,_,_) as sourceTerm)) -> 
      declare status identifier sourceTerm
  | Let_decl(identifier,sourceTerm) -> 
      declare Simple identifier sourceTerm
  | Lin_decl(identifier,sourceTerm) -> 
      declare Linear identifier sourceTerm 
  | Let_type decl ->  
      declare_type decl 
  | Let_type_synonym (identifier,ty) -> 
      declare_type_synonym identifier ty
  | Let_class (tyv,args,super_opt,(mds,add_cases)) -> 
      declare_class tyv args super_opt mds add_cases 
  | Directive (directive,s) -> 
      match directive with 
      | "show" -> set_mode s Show_on
      | "hide" -> set_mode s Show_off
      | "cd" -> chdir s
      | "open" -> load s
      | "quit" -> printf "\b~~~\n"; exit 0
      | str1 -> basicError (str1^" is an unknown directive") 

and load name =
  let source = 
    match path_name name basic_paths with 
    | Some fullname -> fullname
    | None -> raise Not_found 
  in 
  let save_modes = !modes in
  modes := ("prompt", Show_off) :: ("echo", Show_off) :: !modes;
  let chan = open_in source in
  Printf.printf "(* Begin %s \"%s\"... *)\n" action_text source;
  flush stdout;
  begin
    try
      List.iter process_action (parseShellListFromChannel chan);
      (* defined recursively, below *) 
      close_in chan
    with e ->
      modes := save_modes;
      close_in chan;
      raise e
  end;
  Printf.printf "(* Finished %s \"%s\" *)\n" action_text source;
  flush stdout;
  set_mode "echo" Show_on;
  set_mode "prompt" Show_on;
  ()

(*** Top level loop *)


let error_stop_mode = ref false

let handleTopLoopException exn = 
  begin match exn with

  (* system-defined *)

  | Invalid_argument s -> pf (sprintf "Invalid_argument %s" s)
  | Sys_error s -> pf s
  | Sys.Break -> pf "Break ..."
  | Not_found -> pf "Not_found"

  (* failures in named O'Caml functions *)

  | Failure s -> pf (sprintf "Failure in %s" s)

  (* exported from source files *)

  | Lex.SyntaxError (line,col,message) ->  
(*      Printf.eprintf "Syntax error at line %d, column %d : %s\n"
            line col message;  *)
      Printf.printf "Syntax error at line %d, column %d : %s"
            line col message; 
  | Error s       -> Printf.printf "error: %s" s
  | PtypeError (tys,s) -> formatTypeError idSub (map convert_type tys,s)
  | TypeError (tys,s) -> formatTypeError idSub (tys,s)
  | PTermError (ts,s)  -> formatPTermError (ts,s)
  | TermError (ts,s)  -> formatTermError (ts,s)
  | Wrong_index m -> 
      Printf.printf "index %d is too small in the environment" m
  | e -> Printf.printf "Unexpected exception: %s" (Printexc.to_string e)
  end;
  if !error_stop_mode then exit 1
;;

let makeConsoleLexbuf () =
  Lexing.from_function 
    (std_lexer_func read_line)
   (*  (if isatty () then readline_lexer_func else std_lexer_func read_line) *)
;;


let readEvalPrint () =
  let mode x = get_mode x = Show_on in
  let parseShell = Lex.runParser Parse.parseShellAction
  in
  let lexbuf = ref (makeConsoleLexbuf ()) in
  set_ps1 "~~ ";
  set_ps2 "";
  while (true) do
    set_stdin_prompt_mode (mode "prompt");
    set_stdin_echo_mode (mode "echo");
    set_stdin_number_mode (mode "number");
    set_start();
    try
      let action = parseShell !lexbuf
      in process_action action
    with exn ->
      handleTopLoopException exn;
      flush stdout;
      print_newline();
      lexbuf := makeConsoleLexbuf ()
  done
;;




let general_load name =
  let save_line_number = !Lex.line_number and save_modes = !modes in
  try
    Lex.line_number := 1;
    let y = load name in
    Lex.line_number := save_line_number; modes := save_modes; y
  with e ->
    Lex.line_number := save_line_number; modes := save_modes; 
    handleTopLoopException e;
    Printf.printf "Error processing %s, continuing\n" name;
    flush stdout;
    exit 1

let theShell () =
  let command_line =
    if !Sys.interactive
    then {cl_std = true; cl_errorstopmode = false; cl_files = []}
    else parse_command_line Sys.argv
  in
  let interactive = command_line.cl_files = [] && isatty () in
  error_stop_mode := command_line.cl_errorstopmode;
  let startUps = if command_line.cl_std then ["prelude/standard_prelude"] else [] in
  Sys.catch_break true;
  initial_type_environment();
  initial_term_environment();


  if startUps <> [] then begin
    if interactive then pf "Loading startup files ... ";
    List.iter general_load startUps
  end;
  if interactive then begin
    pf "" ;
    pf "" ;
    pf ("Welcome to bondi version " ^ System.version);
    pf "No warranty expressed or implied" ;
    pf ("Standard library: " ^ System.standard_library);
    pf "See README for details" ;
    pf "type `%quit;;' to exit" ;
    set_mode "echo" Show_on;
    set_mode "prompt" Show_on;
  end;
  if command_line.cl_files = [] then readEvalPrint () 
  else
  List.iter general_load command_line.cl_files
;;

let () =
  Random.init (truncate (Unix.gettimeofday ()));
  if !Sys.interactive then
    print_endline "Type \"Shell.theShell ();;\" to start a session."
  else theShell ()
;;
