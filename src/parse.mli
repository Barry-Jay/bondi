type token =
  | DIRECTIVE_quit
  | DIRECTIVE_open
  | DIRECTIVE_hide
  | DIRECTIVE_show
  | DIRECTIVE_cd
  | DIRECTIVE_status
  | STRING of (string)
  | L_IDENT of (string)
  | U_IDENT of (string)
  | INTEGER of (int)
  | FLOAT of (float)
  | CHARACTER of (char)
  | WILDCARD of (string)
  | ALL
  | AND
  | AS
  | BEGIN
  | CLASS
  | CLONE
  | CPC
  | DATATYPE
  | DISCONTINUOUS
  | DO
  | ELSE
  | END
  | ENTRY
  | EQCONS
  | EXT
  | EXTENDS
  | FALSE
  | FOR
  | FUN
  | GENERALISE
  | IF
  | IN
  | LENGTHV
  | LET
  | LIN
  | MATCH
  | METHOD
  | NEW
  | NEWARRAY
  | ARRAY
  | OF
  | REC
  | REF
  | REST
  | REFCONS
  | SLEEP
  | SPAWN
  | STATIC
  | SUPER
  | THEN
  | TO
  | TRUE
  | TYPE
  | UN
  | VIEW
  | WHERE
  | WHILE
  | WITH
  | ISREF
  | ISARRAY
  | BANG
  | BAR
  | BOOL_AND
  | BOOL_OR
  | CPCBIND
  | CPCPRO
  | COLON
  | DBLCOLON
  | DOT
  | EQUAL
  | EQUALOP
  | GREATERTHAN
  | LESSTHAN
  | LONGRARROW
  | MINUS
  | PERCENT
  | PLUSEQUAL
  | RARROW
  | ADDOP of (string)
  | EXPOP of (string)
  | MISCOP of (string)
  | MULTOP of (string)
  | NOPER of (string)
  | OPER of (string)
  | RELOP of (string)
  | EOF
  | LPAREN
  | RPAREN
  | LBRACKET
  | RBRACKET
  | LBRACE
  | RBRACE
  | COMMA
  | SEMICOLON
  | SEMISEMI

val parseShellAction :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> P_data.shell_action
val parseShellActionList :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> P_data.shell_action list
val pTerm :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> P_data.p_term
