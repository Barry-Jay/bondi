val buf_pos : int ref
val last_buf_pos : int ref
val line_number : int ref
val incr_lex_counters : Lexing.lexbuf -> unit
exception SyntaxError of int * int * string
val runParser :
  ((Lexing.lexbuf -> Parse_fish.token) -> Lexing.lexbuf -> 'a) ->
  Lexing.lexbuf -> 'a
