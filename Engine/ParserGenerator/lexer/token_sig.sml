

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
 
   filename      : token_sig
   programmar    : Victor Winter
   last modified : 4/23/97
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


(* ------------------------------------------------------------------ *)
signature TOKEN_OPS =
sig
    type t_token
    val make_lexer               : (int -> string) -> unit -> t_token
    val extract_token            : t_token -> string
    val extract_SHELL_value      : t_token -> string 
    val extract_SHELL_pos        : t_token -> {line: word, column: word}
    val extract_SDT_value        : t_token -> CONCRETE_REPRESENTATION.TREE 
    val IsTokenIdEqualTokenValue : t_token -> bool
    val IsSDT                    : t_token -> bool
    val print_token              : t_token -> unit
    val token_string             : t_token -> string
end;
(* ------------------------------------------------------------------ *)
