
(* lex.mll -- OCaml lex file *)

{

(* header code *)      

open Lexing
open Parsing
open Datum
open P_data
open Parse


(* generates an Ocaml Hashtbl from a list of key/value pairs.
   Used to store mathematical functions and keywords.   *)

let hash_table_from_list n lst =
  let tbl = Hashtbl.create n
  in let addEntry (s,kw) = Hashtbl.add tbl s kw
  in 
  List.iter addEntry lst;
  tbl
;;     

type token = EOS | Word of string | Err;;


    (* keywords *)

let keyword_table =          (* 97 is a prime larger than table size *)
  hash_table_from_list 97 [  

  "all",                 ALL;
  "and",       		 AND;
  "array",               ARRAY; 
  "as",                  AS;
  "begin",               BEGIN;
  "class",               CLASS;
(*> CPC *)
  "cpc",                 CPC;         (* Used to denote process cases from CPC *)
(*< CPC *)
  "datatype",  		 DATATYPE;
  "do",                  DO;
  "discontinuous",       DISCONTINUOUS;
  "else",     		 ELSE;
  "end",                 END;
  "entry",               ENTRY;
  "eqcons",              EQCONS;
  "ext",                 EXT;
  "extends",             EXTENDS;
  "False",               FALSE;
  "for",                 FOR;
  "fun",       		 FUN;
  "generalise",          GENERALISE;
  "if",        		 IF;
  "in",        		 IN;
  "lengthv",             LENGTHV;
  "let",       		 LET;
  "lin",       		 LIN;
  "match",     		 MATCH;
  "method",              METHOD;
  "new",                 NEW;
  "newarray",            NEWARRAY;
  "of",        		 OF;
  "rec",                 REC;
  "Ref",                 REFCONS;
  "ref",                 REF;
(*> CPC *)
  "rest",                REST;              (* Used to denote restrictions *)
(*< CPC *)
  "sleep",               SLEEP;
  "spawn",               SPAWN;
  "static",              STATIC;
  "super",               SUPER;
  "then",      		 THEN;
  "to",        		 TO;
  "True",                TRUE;
  "type",      		 TYPE;
  "Un",                  UN;
  "view",                VIEW;
  "where",               WHERE;
  "isRef",		 ISREF;
  "isArray",		 ISARRAY;
  "while",               WHILE;
  "with",      		 WITH
 ] 
;;


let stringParser lexer lexbuf = 
let wordlist =
let rec next strList =
match lexer lexbuf with
EOS -> strList
| Word(s) -> next (s::strList)
| Err -> next strList
in
next []
in
List.fold_right (^) (List.rev wordlist) ""
;;


let symbol_table =
  (* alphabetical by token *) 
  hash_table_from_list 29 [
  "!",          BANG;
  "|",          BAR;
  "&&",         BOOL_AND;
  "||",         BOOL_OR;
  ":",          COLON;
  "::",         DBLCOLON; 
  ".",          DOT;
  "=",          EQUAL;
  "==",         EQUALOP;
  ">",          GREATERTHAN;
  "<",          LESSTHAN;
  "-->",        LONGRARROW;
  "-",          MINUS;
  "%",          PERCENT;
  "+=",         PLUSEQUAL;
  "->",         RARROW

]

let is_rel_op s = 
  let rec test = function
      -1 -> false
    | i -> match s.[i] with
        '<' | '=' | '>' -> true
      | _ -> test (i - 1)
  in
  s.[0] != ':' &&
  test (String.length s - 1)

let rec symbol s =
  try Hashtbl.find symbol_table s
  with Not_found ->
    if is_rel_op s then RELOP s else
    match s.[0] with
      '$' | '.' | '?' | '^' -> MISCOP s
    | '-' | '+' | '|' -> ADDOP s
    | '*' when String.length s >= 2 && s.[1] == '*' -> EXPOP s
    | '*' | '/' | '%' | '&' -> MULTOP s
    | _ -> basicError (s^" is not a recognised symbol") 


let hex_char2int s =
  let c = Char.code s
  in 
  match s with
    _ when (s >= '0' && s <= '9') -> (* CHANGED & TO && !!!! *)
      c - (Char.code '0') 
  | _ when (s >= 'a' && s <= 'f') -> (* CHANGED & TO && !!!! *)
      (c - (Char.code 'a')) + 10 
  | _ when (s >= 'A' && s <= 'F') -> (* CHANGED & TO && !!!! *)
      (c - (Char.code 'A')) + 10 
  | _ -> basicError "in hexadecimal character"
;; 


(* hexint_of_string : string -> int *)

(* converts a string representing a hex number to integer value *)
(* assumes that string begins with "0x" or "0X"                 *)

let hexint_of_string s =
  let len = String.length s
  in if (s.[0] = '-') then 
    let value = ref (- (hex_char2int s.[3]))
    in 
    for i = 4 to (len - 1) do
      value := !value * 16 - (hex_char2int s.[i])
    done;
    !value
  else
    let value = ref (hex_char2int s.[2])
    in 
    for i = 3 to (len - 1) do
      value := !value * 16 + (hex_char2int s.[i])
    done;
    !value
;;


let lexeme_length lexbuf = lexbuf.lex_curr_pos - lexbuf.lex_start_pos


let buf_pos = ref 0
let last_buf_pos = ref 0
let comment_depth = ref 0
let line_number = ref 1    (* line number tracking for %use *)
;;
let incr_lex_counters lexbuf =
  incr line_number;
  last_buf_pos := !buf_pos;
  buf_pos := lexeme_end lexbuf
;;


let spRegexp = "((\\\\n) | (\\\\t))*";;

let subSpChar  inputStr =
match inputStr with
| "\\\\n" -> "\n"
| "\\\\t" -> "\t"
| "\\\\" -> "\\"
| _ as s -> s
;;

}

let letters = ['a'-'z' 'A'-'Z']+
let digits = ['0'-'9']+
let datumConstants = ['!' '#'-'&' '*''+' '-''.''/' ':' '<'-'@' '^' '|' '_' '>' ';' '?' '|' '{' '}' '=' '%' '^' '*' '(' ')'',' '`' '[' ']' '\'']+

(* lexing rules *)

rule mainLex = parse

| eof   { EOF }

    (* whitespace *)
| [' ' '\t' ] + { mainLex lexbuf }
| "\n"  { incr_lex_counters lexbuf; mainLex lexbuf }

    (* begin comment *)
| "(*"                
    { comment_depth := 1;
      commentLex lexbuf; 
      mainLex lexbuf }

    (* begin line comment *)
| "//"                
    { lineCommentLex lexbuf; 
      mainLex lexbuf }

| "#!/"                
    { lineCommentLex lexbuf; 
      mainLex lexbuf }
| "#!"                
    { lineCommentLex lexbuf; 
      mainLex lexbuf }

    (* characters and strings *)

| "'\\a'"                       { CHARACTER '\007' }
| "'\\b'"                       { CHARACTER '\b' }
| "'\\e'"                       { CHARACTER '\027' }
| "'\\f'"                       { CHARACTER '\012' }
| "'\\n'"                       { CHARACTER '\n' }
| "'\\r'"                       { CHARACTER '\r' }
| "'\\t'"                       { CHARACTER '\t' }
| "'\\\\'"                      { CHARACTER '\\' }
| "'\\\''"                      { CHARACTER '\'' }
| "'\\013'"                     { CHARACTER '\013' }  
(* | "'\\" _ "'"                { CHARACTER (lexeme_char lexbuf 2) } *)
| "'" [^ '\'' '\\'] "'"         { CHARACTER (String.get (lexeme lexbuf) 
1) }
| '"'                           {STRING (stringParser stringLex lexbuf)}

  (* numerics *)

  (* hexadecimal integer *)
| ("0x" | "0X")['0' - '9' 'A' - 'F' 'a' - 'f']+ 
   { INTEGER (hexint_of_string (lexeme lexbuf)) }

  (* floating-point --- can omit decimal part, or exponential part, not both *)
| ['0' - '9']+ ('.' ['0' - '9']* )? (('e' | 'E') ('+' | '-')? ['0' - '9']+)
| ['0' - '9']+ ('.' ['0' - '9']* )
   { FLOAT (float_of_string (lexeme lexbuf)) }

  (* decimal integer *)
| [ '0' - '9' ]+  
   { INTEGER (int_of_string (lexeme lexbuf)) }

(* Special characters *)

| "("   { LPAREN }
| ")"   { RPAREN }
| "["   { LBRACKET }
| "]"   { RBRACKET }
| "{"   { LBRACE }
| "}"   { RBRACE }
| ","   { COMMA }
(*> CPC *)
| "\\"  { CPCBIND }         (* Used to denote binding names in process-cases. *)
| "~"   { CPCPRO }          (* Used to denote protected names in process-cases. *)
(*< CPC *)
| ';'+  { if lexeme_length lexbuf == 1 then SEMICOLON else SEMISEMI }


(* infix datum constants - datum versions *)

| ['!' '#'-'&' '*''+' '-''.''/' ':' '<'-'@' '^' '|' ]+
    { symbol (lexeme lexbuf) }

  (* keyword, combinators, coercions, type keyword, datum
     constants, identifiers... *)
|   [ 'a' - 'z'] [ 'A' - 'Z' 'a' - 'z' '_' '0' - '9'] *
    {
      let s = lexeme lexbuf in
      try Hashtbl.find keyword_table s
      with Not_found -> try Hashtbl.find symbol_table s
      with Not_found -> try NOPER (Hashtbl.find noper_table s)
	(* It is important that NOPER comes before OPER as all the nary opers
	 * are also in the oper_table, this is to optimise other parts of the
	 * code in inference *)
      with Not_found -> try OPER (Hashtbl.find oper_table s)
      with Not_found -> L_IDENT s
    }
|   [ 'A' - 'Z' ] [ 'A' - 'Z' 'a' - 'z' '_' '0' - '9'] *
    {
      let s = lexeme lexbuf in
      try Hashtbl.find keyword_table s
      with Not_found -> try Hashtbl.find symbol_table s
      with Not_found -> U_IDENT s
   }

|  [ '_' ]  [ 'A' - 'Z' 'a' - 'z' '_' '0' - '9'] *  
   {
      let str = lexeme lexbuf in 
      WILDCARD (String.sub str  1 (String.length str -1))
   }

and commentLex = parse

    "(*" { incr comment_depth; commentLex lexbuf }

  | "*)" { decr comment_depth;
	   if !comment_depth == 0 
	   then () 
	   else commentLex lexbuf 
	 }
  | "\n" { incr_lex_counters lexbuf; commentLex lexbuf }
  | eof  { basicError "unterminated comment" }
  | _    { commentLex lexbuf }

and lineCommentLex = parse

    "\n" { incr_lex_counters lexbuf; () }
  | eof { () }
  | _   { lineCommentLex lexbuf }

  and stringLex = parse

  | "\\b"                                      { Word "\b" }
  | "\\n"                                      { Word "\n" }
  | "\\r"                                      { Word "\r" }
  | "\\t"                                      { Word "\t" }
  | "\\\\"                                     { Word "\\" }
  | ' '					       { Word " "  }
  | '\n'				       { Word "\n"  }
  | '"'                                        { EOS       }
  | '\\'					       {Word "\\"  }
  | "\\\""				       { Word "\"" }
  | ( letters | digits | datumConstants )* as word { Word(word) }
  | _	{ Err }
  (* | _  { basicError ("here->"^(lexeme lexbuf)^"<-")} *)



(* trailer code *)      

{ 

exception SyntaxError of int * int * string (* line, column *)

(* post-lexer, pre-parser *)

(* The postlexer/preparser recognises directives. A "%" followed by an
   identifier ID at the beginning of a phrase means that the phrase is a
   directive, but all the lexer can produce is the infix operator "%" followed
   by ID. *)

let directive_alist =
  ["quit",      DIRECTIVE_quit;
   "hide",      DIRECTIVE_hide;
   "show",      DIRECTIVE_show;
   "cd",        DIRECTIVE_cd;
   "open",      DIRECTIVE_open;
(*> CPC *)
   "status",    DIRECTIVE_status]       (* Directive to display the process environment. *)
(*< CPC *)

let lookup_directive = Hashtbl.find (hash_table_from_list 12 directive_alist)

type post_processor_state =
  | Pp_start
  | Pp_directive
  | Pp_normal
let pp_state = ref Pp_start

let rec post_process lexer lexbuf =
  match lexer lexbuf with
  | L_IDENT id when !pp_state = Pp_directive ->
      begin try
        let directive = lookup_directive id in
        pp_state := Pp_normal; directive
      with Not_found -> raise Parse_error
      end
  | _ when !pp_state = Pp_directive ->
      raise Parse_error
  | SEMISEMI -> pp_state := Pp_start; SEMISEMI
  | PERCENT when !pp_state = Pp_start ->
      pp_state := Pp_directive; post_process lexer lexbuf
  | tok -> pp_state := Pp_normal; tok



(* lex, parse, report syntax errors *)

let runParser pr lexbuf =
  pp_state := Pp_start;
  line_number := 1;
  buf_pos := lexeme_end lexbuf;
  try pr (post_process mainLex) lexbuf
  with 
    Parse_error -> 
      let cur_pos = lexeme_start lexbuf 
      in	
      if (cur_pos >= !buf_pos)
      then raise 
	  (SyntaxError 
	     (!line_number,cur_pos - !buf_pos + 1,""))
      else raise (* last valid lexeme on previous line *)
	  (SyntaxError 
	     (!line_number - 1,cur_pos - !last_buf_pos + 1,""))
  | Failure message -> 
      let cur_pos = lexeme_start lexbuf 
      in	
      if (cur_pos >= !buf_pos)
      then raise 
	  (SyntaxError 
	     (!line_number,cur_pos - !buf_pos + 1,message))
      else raise (* last valid lexeme on previous line *)
	  (SyntaxError 
	     (!line_number - 1,cur_pos - !last_buf_pos + 1,message))
;;




} 
