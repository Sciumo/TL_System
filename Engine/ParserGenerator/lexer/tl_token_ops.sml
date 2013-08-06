
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
 
   filename      : tl_token_ops
   programmar    : Victor Winter
   last modified : 7/25/2001
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


(* ------------------------------------------------------------------ *)
(* In general, the parse program requires access to (1) the parse 
   representation of a token (which is a string), and (2) the value 
   that is associated with a token (e.g., a number, the actual string
   of an id, etc.)


   From a general user perspective a convenient representation of a
   lex token for the target grammar is:
 
                        SHELL( token_id, token_value, token_pos )

   Here the parameter token_id contains the string representation of
   the token as it appears in the target grammar. For example, consider
   the following grammar production:

                         F -> num

    where num stands for any number. In this case, LEX needs to
    return the token 

                        SHELL("num", value, getNextTokenPos())

    whenever it encounters a number. Now suppose that lex encounters
    the number 471. In this case the following token should be
    returned:

                        SHELL("num", "471", getNextTokenPos())

    Note that a string representation of the number is returned. This
    is perfectly fine for the purposes of the parser.  

    Finally, the reason the above token representation is required
    (imposed) is to relieve the user of the burden of having to write
    routines that convert from the lex representation of a token and the
    parser representation of a token. I encountered many name clash
    difficulties when I used something like:

          datatype PARSE_TOKEN = .....

    For this reason I resorted to having parse tokens be represented
    by strings. I believe this shift will make the system more robust
    for general grammars. 

    Another note:

    In HATS, two parsers are constructed: one for the target grammar
    and the other for the tranformation language grammar. Each grammar
    has its own token format.
*)


(* ------------------------------------------------------------------ *)


(* ------------------------------------------------------------------ *)
(*open TextIO;
use ("C:\\hats\\HATS_0.09\\lexer\\token_sig");
use ("C:\\hats\\HATS_0.09\\auxiliary\\tree_datatypes");
*)

functor TL_LEX_OPS_FN(val getNextTokenPos : string -> {line: word, column: word};
                      val call_aux_parser : string -> (int -> string) -> CONCRETE_REPRESENTATION.TREE) : TOKEN_OPS =
struct

structure TL_Lex = TL_LexFn(val getNextTokenPos = getNextTokenPos; val call_aux_parser = call_aux_parser)

type t_token = TL_Lex.UserDeclarations.lexresult;

fun make_lexer(yyinput) =
  let
    val lexer = TL_Lex.makeLexer(yyinput)
   in
    fn () => lexer() handle TL_Lex.LexError => raise auxiliary_universal.ParseError("TL Lexer: " ^ auxiliary_universal.posToString(getNextTokenPos "") ^ ": syntax error")
  end

val extract_token = fn

   ( TL_Lex.UserDeclarations.SHELL(x,y,pos) ) => x
 | ( TL_Lex.UserDeclarations.SDT(x,y,pos) )   => x;

val extract_SHELL_value = fn

   ( TL_Lex.UserDeclarations.SHELL(x,y,pos) ) => y
 | ( TL_Lex.UserDeclarations.SDT(x,y,pos) )   => raise General.Fail("an_error");

val extract_SHELL_pos = fn

   ( TL_Lex.UserDeclarations.SHELL(x,y,pos) ) => pos
 | ( TL_Lex.UserDeclarations.SDT(x,y,pos) )   => pos;

val extract_SDT_value = fn

   ( TL_Lex.UserDeclarations.SHELL(x,y,pos) ) => raise General.Fail("an_error")
 | ( TL_Lex.UserDeclarations.SDT(x,y,pos) )   => y;


val IsTokenIdEqualTokenValue = fn

   ( TL_Lex.UserDeclarations.SHELL(x,y,pos) ) => x = y
 | ( TL_Lex.UserDeclarations.SDT(x,y,pos) )   => false;

val IsSDT = fn

   ( TL_Lex.UserDeclarations.SHELL(x,y,pos) ) => false
 | ( TL_Lex.UserDeclarations.SDT(x,y,pos) )   => true;

(* ------------------------------------------------------------------ *)
val print_token = fn

    TL_Lex.UserDeclarations.SHELL(x,y,pos) =>  

            (print("\n  SHELL(");
             print(x:string);
             print(",");
             print(y:string);
             print(") \n")
            )

  | TL_Lex.UserDeclarations.SDT(x,y,pos)   =>  

            (print("\n SDT("); 
             print(x:string);
             print(",a_tree");
             print(") \n")
            );

(* ------------------------------------------------------------------ *)
val token_string = fn

    TL_Lex.UserDeclarations.SHELL(x,y,pos) =>  

          "Token ID = " ^ x ^ "  Token Value = " ^ y

  | TL_Lex.UserDeclarations.SDT(x,y,pos)   =>  

          "Token ID = " ^ x ^ "  Token Value = an SDT in the target language";
            


end; (* structure *)
(* ------------------------------------------------------------------ *)



