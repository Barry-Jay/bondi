/* parse.mly
  References:
              "bison for yacc - see school home pages"
              "O'Reilly book on lex and yacc".

*/


%{ (* header *)

open List
open Datum
open P_data


let bintype op l r = 
  let fr = 
    match op with 
      "*" -> pconstTy "Binprod"
    | "+" -> pconstTy "Bincoprod"
    | _ -> pconstTy op  
  in 
  PapplyF(PapplyF(fr,l),r)

let make_nested_let bindings body =
  let bind (x,ps,r) t = Plet (Simple,x,multilam ps r,t)
  in 
  fold_right bind bindings body 

let make_letrec (x,ps,r) t = Plet(Recursive,x,multilam ps r,t)

let make_letext (x,ps,r) t = Plet(Extensible,x,multilam ps r,t)

let make_letmethod (x,ps,r) t = Plet(Method,x,multilam ps r,t)

let make_letdiscontinuous (x,ps,r) t = Plet(Discontinuous,x,multilam ps r,t)

(*
let make_nested_new bindings body = 
  let bind (x,ps,r) t = 
    if ps = [] 
    then Papply(Plam(x,t),r)
    else pTermError [x] "is a location holding a function" 
  in 
  fold_right bind bindings body
*)

let tuple xs = 
  let f x y = ap2 (Pconstructor "Pair") y x  in 
  match rev xs with 
    [] ->  Pconstructor "Un"
  | x :: xs0 -> fold_left f x xs0

let l_nil() = Pconstructor "Nil" 
let l_cons x y = ap2 (Pconstructor "Cons") x y 
let make_list cars = fold_right l_cons cars (l_nil());;


%} 

              /* shell directives */

%token DIRECTIVE_quit, DIRECTIVE_open, DIRECTIVE_hide, DIRECTIVE_show, DIRECTIVE_cd, DIRECTIVE_status   // CPC


              /* strings (for filenames) */
 

%token <string> STRING

              /* identifiers */

%token <string> L_IDENT U_IDENT 
        /* lower and upper case initial, leading "\" */ 

              /* datum constants = d's in paper */

%token <int>    INTEGER
%token <float>  FLOAT
%token <char>   CHARACTER
%token <string> STRING
%token <string> WILDCARD 


              /* other keywords */

%token ALL AND AS BEGIN CLASS CLONE CPC DATATYPE DISCONTINUOUS DO 
%token ELSE END ENTRY EQCONS EXT EXTENDS FALSE FOR FUN GENERALISE
%token IF IN LENGTHV LET LIN MATCH METHOD NEW NEWARRAY ARRAY OF REC REF REST REFCONS SLEEP SPAWN
%token STATIC SUPER THEN TO TRUE TYPE UN VIEW WHERE WHILE WITH ISREF ISARRAY

              /* the symbol table */ 

%token BANG BAR BOOL_AND BOOL_OR CPCBIND CPCPRO COLON DBLCOLON DOT EQUAL EQUALOP 
%token GREATERTHAN LESSTHAN LONGRARROW MINUS PERCENT PLUSEQUAL RARROW 

%token <string> ADDOP EXPOP MISCOP MULTOP NOPER OPER RELOP


              /* Special characters  */

%token EOF 
%token LPAREN RPAREN
%token LBRACKET RBRACKET
%token LBRACE RBRACE 
%token COMMA SEMICOLON SEMISEMI


              /* precedences */

%right LET LIN NEW NEWARRAY IN 
%right AND

%left COLON
%right prec_match prec_fun 
%right BANG 
%right RARROW LONGRARROW prec_case
%nonassoc prec_list
%right SEMICOLON
%right IF THEN ELSE IS WHILE DO 
%nonassoc REF REFCONS
%left EQUAL PLUSEQUAL
%left BOOL_OR
%left BOOL_AND
%nonassoc RELOP EQUALOP EQCONS LESSTHAN GREATERTHAN
%right MISCOP
%left ADDOP MINUS
%left MULTOP PERCENT
%left EXPOP
%right prec_unary_minus
%left DOT prec_app prec_compose
%left prec_suffix
%left AS



               /* entry points for shell parser */

%type <P_data.shell_action> parseShellAction
%start parseShellAction	

%type <P_data.shell_action list> parseShellActionList
%start parseShellActionList 

%type <P_data.p_term> pTerm
%start pTerm

%%



/*** shell ***/

parseShellAction:
    shellAction { $1 }
  | EOF { Directive ("quit","")}
;

parseShellActionList:
    shellActionList { $1 }
;

shellActionList:
    EOF { [] }
  | shellAction shellActionList { $1::$2 }
;

shellAction:
    directive SEMISEMI
      { $1 }

  | pTerm SEMISEMI
      { Let_decl(Ptvar "it",$1) }

  | LET binding SEMISEMI
      { 
    match $2 with 
    | (x,ps,r) -> Let_decl(x,multilam ps r)
		 } 

  | LIN binding SEMISEMI
      { 
    match $2 with 
    | (x,ps,r) -> Lin_decl(x,multilam ps r)
		 } 

  | LET REC binding SEMISEMI 
      {
     match $3 with 
    | (x,ps,r) -> 
	let y = 
	  match x with 
	    Ptyped(x1,_) -> x1 
	  |_ -> x 
	in Let_decl(x,Plet(Recursive,x,multilam ps r, y))		 }  
   
  | LET EXT binding SEMISEMI 
      {
     match $3 with 
    | (x,ps,r) -> 
	let y = 
	  match x with 
	    Ptyped(x1,_) -> x1 
	  |_ -> x 
	in Let_decl(x,Plet(Extensible,x,multilam ps r, y))		 }  
   
  | LET METHOD binding SEMISEMI 
      {
     match $3 with 
    | (x,ps,r) -> 
	let y = 
	  match x with 
	    Ptyped(x1,_) -> x1 
	  |_ -> x 
	in Let_decl(x,Plet(Method,x,multilam ps r, y))		 }  

  | LET DISCONTINUOUS binding SEMISEMI 
      {
     match $3 with 
    | (x,ps,r) -> 
	let y = 
	  match x with 
	    Ptyped(x1,_) -> x1 
	  |_ -> x 
	in Let_decl(x,Plet(Discontinuous,x,multilam ps r, y))		 }  

  | TYPE typeBinding SEMISEMI
      { match $2 with (x,t) ->
        Let_type_synonym (x,t) }
     
  | DATATYPE type_constant_or_punct simpleBondiTypeList EQUAL datatype  
      WITH addCaseList SEMISEMI 
      {  Let_type ($2, [($3,$5)],$7) }

  | DATATYPE type_constant_or_punct EQUAL datatype  
      WITH addCaseList SEMISEMI 
      {  Let_type ($2, [([],$4)],$6) }
    
  | DATATYPE type_constant_or_punct simpleBondiTypeList EQUAL datatype SEMISEMI 
      {  Let_type ($2, [($3,$5)],[]) }

  | DATATYPE type_constant_or_punct EQUAL datatype SEMISEMI 
      { Let_type ($2, [([],$4)],[]) }

  | CLASS tyconstant parameterCommaListOpt extendsOpt  LBRACE attributeList 
      WITH addCaseList RBRACE   
      { Let_class ($2, $3,$4, ($6,$8)) } 

  | CLASS tyconstant parameterCommaListOpt extendsOpt  LBRACE attributeList 
     RBRACE   
      { Let_class ($2, $3,$4, ($6,[])) } 
;

directive:

  | DIRECTIVE_cd STRING         { Directive ("cd",$2) }
  | DIRECTIVE_show L_IDENT        { Directive ("show",  $2) }
  | DIRECTIVE_hide L_IDENT        { Directive ("hide", $2) }
  | DIRECTIVE_quit              { Directive ("quit","")}
  /*> CPC */
  | DIRECTIVE_status            { Directive ("status","") }
  /*< CPC */
  | DIRECTIVE_open     STRING    { Directive ("open",$2) }
;

/*** bindings and parameters ***/


typeBinding:
  type_constant_or_punct EQUAL pType { ($1,$3) }

bindingList:
    binding { [$1] }
  | binding AND bindingList { $1 :: $3 }
;

binding:
  | parameter simpleBondiTermList EQUAL pTerm {($1,$2,$4) } 
; 

parameter:
  | term_id { Ptvar $1  }
  | parameter COLON pType         { Ptyped($1,$3) }
  | LPAREN parameter RPAREN        {       $2    }
  | LPAREN infix_op RPAREN { Ptvar $2 } 
;

attributeList: 
  | { [],[] }
  | field attributeList { 
     match $2 with (fds,methds) -> ($1::fds,methds) }
  | methd attributeList { 
     match $2 with (fds,methds) -> (fds,$1::methds) }
;

field:
  | parameter SEMICOLON { $1 } 

methd: 
  | L_IDENT EQUAL LBRACE pTerm RBRACE
      { (Method,$1,$4) } 
  | STATIC REC L_IDENT EQUAL LBRACE pTerm RBRACE
      { (Recursive,$3,$6) } 
  | STATIC EXT L_IDENT EQUAL LBRACE pTerm RBRACE   
      {	(Extensible,$3,$6) }
  | STATIC DISCONTINUOUS L_IDENT EQUAL LBRACE pTerm RBRACE
      { (Discontinuous,$3,$6) } 
  | STATIC L_IDENT EQUAL LBRACE pTerm RBRACE
      { (Simple,$2,$5) } 

/*** terms ***/

pInfixTerm:
  | simpleBondiTerm simpleBondiTermList %prec prec_app   { 
    let apdot t = function 
	Pinvoke(arg,mthd,b) -> Pinvoke(ap t arg,mthd,b)
      | arg -> ap t arg 
    in 
    fold_left apdot $1 $2 }
  | MINUS pInfixTerm %prec prec_unary_minus        { ap (zvar "negate") $2 }
  | pInfixTerm exp_op pInfixTerm %prec EXPOP     { ap2 (zvar $2) $1 $3}
  | pInfixTerm mult_op pInfixTerm %prec MULTOP   { ap2 (zvar $2) $1 $3}
  | pInfixTerm add_op pInfixTerm %prec ADDOP     { ap2 (zvar $2) $1 $3}
  | pInfixTerm misc_op pInfixTerm %prec MISCOP   { ap2 (zvar $2) $1 $3}
  | pInfixTerm OPER pInfixTerm %prec MISCOP      { Poper($2,[$1;$3]) }
  | OPER pInfixTerm %prec MISCOP      { Poper($1,[$2]) }
  | NOPER simpleBondiTermList %prec MISCOP	{ Poper($1,$2) }

pRelTerm:
  | pInfixTerm                                                       { $1 }
  | pInfixTerm rel_op pInfixTerm                 { ap2 (zvar $2) $1 $3 }
;
/* FIXME !! 
  | pInfixTerm rel_op pInfixTerm pRelTerms
      { 
        (* The term is {t0 op1 t1 op2 ... opN tN}; N >= 2. *)
        (* $1 = t0; ($2,$3) :: $4 = [op1, t1; ...; opN, tN] *)
        (* Meaning: {t0 op1 t1 && t1 op2 t2 && ... && tN-1 opN tN} *)
        let t0 = $1 and op1 = zvar $2 and t1 = $3 in
        match $4 with
          [] -> assert false
        | (op2, t2) :: tail -> build_rel_term t0 op1 t1 op2 t2 tail
      }
;
pRelTerms:
  | rel_op pInfixTerm                                     { [zvar $1, $2] }
  | rel_op pInfixTerm pRelTerms                  { (zvar $1, $2) :: $3 }
;
*/

pTerm:
  | pRelTerm                                                         { $1 }
  | pTerm BOOL_AND pTerm  %prec MULTOP           { ap2 (zvar "&&") $1 $3 }
  | pTerm BOOL_OR pTerm  %prec ADDOP             { ap2 (zvar "||") $1 $3 }
  | IF pTerm THEN pTerm ELSE pTerm    { Poper("cond",[$2;$4;$6]) }
  | FUN simpleBondiTermList RARROW pTerm  { multilam $2 $4 }
/*
  | FUN simpleBondiTermList LONGRARROW pTerm  { multilin $2 $4 }
*/
  | LET bindingList IN pTerm { make_nested_let $2 $4 }
  | LET REC binding IN pTerm { make_letrec $3 $5 }
  | LET EXT binding IN pTerm { make_letext $3 $5 }
  | LET METHOD binding IN pTerm { make_letmethod $3 $5 }
  | LET DISCONTINUOUS binding IN pTerm { make_letdiscontinuous $3 $5 }
  | patternMatchList { Pcases $1 }  
  | MATCH pTerm WITH  pTerm  { ap $4 $2}  
  | pTerm EQUAL pTerm  { Poper("assign", [$1; $3]) } 
  | term_id PLUSEQUAL patternMatch   { Paddcase ($1,$3) }
  | GENERALISE term_id  { Psubcase $2 } 
  | pTerm EQCONS pTerm  { Poper("eqcons",[$1; $3]) } 
  | pTerm SEMICOLON pTerm       { Poper("seq", [$1; $3]) } 
  | SLEEP pTerm  { Poper("sleep", [$2]) }
  | SPAWN pTerm  { Poper("spawn", [$2]) }
  | pTerm  COLON pType     { Ptyped ($1, $3) }
  | NEW tyconstant classParams { Pnew ($2,$3) } 
  | NEWARRAY simpleBondiTerm simpleBondiTerm  { PnewArr($2,$3) } 
  | LENGTHV pTerm  { Poper("lengthv",[$2]) }
  | ENTRY LPAREN pTerm COMMA pTerm RPAREN { Poper("entry",[$3;$5]) }
  | WHILE pTerm DO pTerm { Poper("while",[$2;$4]) }
  | FOR term_id EQUAL pTerm TO pTerm DO pTerm 
       { ap (ap2 (zvar "forall") $4 $6) (lam (zvar $2) $8)}
  | pTerm AS pTerm { Poper("as",[$1;$3]) }
  | VIEW LPAREN pTerm COMMA pTerm RPAREN {Poper("view",[$3;$5])}
  | pTerm WHERE pTerm { Poper("where",[$1;$3])}
  | ISREF pTerm { Poper("isRef",[$2])}
  | ISARRAY pTerm {Poper("isArray",[$2])}
;


simpleBondiTermMethodList:
    /* empty */ { [] }
  | simpleBondiTermList DOT L_IDENT simpleBondiTermMethodList { ($1,Some $3)::$4 }
  | simpleBondiTermList { [ $1,None ] } 
;


simpleBondiTermList:
    /* empty */ { [] }
  | simpleBondiTerm simpleBondiTermList { $1::$2 }
;

simpleBondiTerm:
  | tyconstant DOT  L_IDENT { Ptvar ($1^"."^$3) }  /* static methods are just functions */
  | LPAREN pTerm RPAREN        { $2 }
  | BEGIN pTerm END        { $2 } 
  | parameter           { $1 } 
  | constructor_id      { Pconstructor $1 } 
  | LPAREN RPAREN       { Pconstructor "Un" } 
  | WILDCARD            { Pwildcard $1 }
  | INTEGER             { p_datum (Int $1) }
  | FLOAT               { p_datum (Float $1) }
  | CHARACTER           { p_datum (Char $1) }
  | STRING              { p_datum (String $1) }
  | TRUE                { p_datum (Bool true) }
  | FALSE               { p_datum (Bool false)} 
  | UN                  { Pconstructor "Un" } 
  | REFCONS             { Pconstructor "Ref" } 
  | LBRACKET pTermCommaList RBRACKET
    { make_list $2 }
  | LPAREN pTermCommaList RPAREN         { tuple $2 }
  | SUPER DOT L_IDENT  { Pinvoke(zvar "this",$3,true) }
  | BANG simpleBondiTerm {Poper("deref",[$2]) }
  | simpleBondiTerm COLON pType         { Ptyped($1,$3) } 
  | simpleBondiTerm  DOT L_IDENT  { Pinvoke($1,$3,false)} 
;

patternMatchList:
    patternMatch  { [$1] }
  | patternMatch  patternMatchList
	{ $1 :: $2 }

patternMatch: 
  | BAR pTerm  RARROW pTerm { (None,$2,None,$4) }
  | BAR LBRACE parameterCommaList RBRACE pTerm  RARROW pTerm {  
     (Some $3,$5,None,$7) }


pTermCommaList:
    /*empty*/ { [] }
  | pTerm { [$1] }
  | pTerm COMMA pTermCommaList { $1::$3 }
;

parameterCommaList:
    /*empty*/ { [] }
  | L_IDENT { [$1] }
  | L_IDENT COMMA parameterCommaList { $1::$3 }
;

parameterCommaListOpt: 
     { [] } 
  | LESSTHAN parameterCommaList GREATERTHAN {map (fun x -> TyVar x) $2 }
;


extendsOpt: 
      EXTENDS U_IDENT {Some $2}
  | { None }
;

/*** types ***/

/* It seems that ocamlyacc uses %prec directives to compare the precedence of
   different operators but not to determine associativity. This is
   unfortunate, because "+" and "*" must associate to the left in terms, but
   to the right in types. So one of the two (types or terms) has to be done by
   hand. I do types by hand as they are simpler. */
pType:
    pSumType { $1 }
  | pType misc_op pType %prec MISCOP                { bintype $2 $1 $3 }
  | pType RARROW pType                              { Pfunty($1,$3) }
/* delete !!  | pType LONGRARROW pType                              { Pfunty(Plinty $1,$3) }
*/
  | allwithvar pType                        { Pquant(TyVar $1,$2) } 
;

allwithvar:
  ALL type_id DOT { $2 }

pSumType:
    pProdType { $1 }
  | pProdType add_op pSumType                       { bintype $2 $1 $3 }
;
pProdType:
    type_composition { $1 }
  | type_composition exp_op pProdType                  { bintype $2 $1 $3 }
  | type_composition mult_op pProdType                 { bintype $2 $1 $3 }

;
type_composition:
    simpleBondiTypeList
      { match $1 with
          h::t -> fold_left (fun x y -> PapplyF(x,y)) h t  
        | _ -> basicError "in simpleBondiTypeList"  }
;

simpleBondiTypeList:
  | simpleBondiType  { [ $1 ] }
  | simpleBondiType simpleBondiTypeList %prec prec_compose { $1::$2 }
;
simpleBondiType:
  | type_id  { PtyV (TyVar  $1) }
  | tyconstant classParams restParam { pclass ($1,$2,$3)  }
  | LPAREN infix_op  RPAREN  { pconstTy $2 }
  | LPAREN pType RPAREN { $2 }
  | REF simpleBondiType { Pref $2} 
  | ARRAY simpleBondiType { Parr $2 }
  | LIN simpleBondiType { Plinty $2 } 
;


classParams:
  | LESSTHAN typeCommaList GREATERTHAN  { $2 }
  | { [] }
;

restParam:
  | LBRACKET pType RBRACKET {$2 }
  |  { Pconstant "Top" } 
;

typeCommaList:
  | pType  { [ $1 ] }
  | pType COMMA typeCommaList %prec prec_compose { $1::$3 }
;



/*** datatypes ***/

datatype:
   opt_bar datatype_alternatives { $2 }
;

datatype_alternatives:
    datatype_alternative { [$1] }
  | datatype_alternative BAR datatype_alternatives { $1 :: $3 }
;
 
datatype_alternative:
    constructor_id
      { $1, [] }
  | constructor_id OF datatype_factors
      { $1, $3 }
;

datatype_factors:
    datatype_factor { [$1] }
  | datatype_factor AND datatype_factors { $1 :: $3 }
;

datatype_factor:
    pType { $1 }
;

addCaseList: 
    addCase { [$1] }
  | addCase AND addCaseList 
      { $1 :: $3}
  
addCase: 
    term_id PLUSEQUAL patternMatch   { ($1,$3) }
  | U_IDENT DOT L_IDENT PLUSEQUAL patternMatch   { ($1 ^ "." ^ $3,$5) }




/*** Trivia ***/

opt_bar:        { () }     | BAR         { () };

type_id:
      L_IDENT       { $1 }

tyconstant: 
    | U_IDENT       { $1 }
;
type_constant_or_punct:
    tyconstant     { $1 }
  | LPAREN  infix_op RPAREN { $2 }
  | LPAREN type_constant_or_punct RPAREN { $2 }
;
term_id:
    L_IDENT       { $1 }
  | U_IDENT DOT L_IDENT { ($1^"."^$3) } 
;
constructor_id:
    U_IDENT       {  $1 }
;

exp_op:
  | EXPOP       { $1 }
;
mult_op:
  | MULTOP      { $1 }
  | PERCENT     { "%" }
;
add_op:
  | ADDOP       { $1 }
  | MINUS       { "-" }
;
misc_op:
  | MISCOP      { $1 }
;
rel_op:
  | BOOL_AND    { "&&" }
  | BOOL_OR     { "||" }
  | EQUALOP     { "==" }
  | GREATERTHAN { ">" } 
  | LESSTHAN    { "<" }
  | RELOP       { $1 } 
;
infix_op:
  | add_op      { $1 }
  | exp_op      { $1 }
  | misc_op     { $1 }
  | mult_op     { $1 }
  | rel_op      { $1 }
;

%%

(* no trailer *)

