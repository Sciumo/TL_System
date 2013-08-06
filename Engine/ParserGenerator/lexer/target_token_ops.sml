

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
 
   filename      : target_token_ops
   programmar    : Victor Winter
   last modified : 9/9/97
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


(* ================================================================== *)
functor TARGET_LEX_OPS_FN(val getNextTokenPos : string -> {line: word, column: word}) : TOKEN_OPS =
struct
																				
	structure Target_Lex = Target_LexFn(val getNextTokenPos = getNextTokenPos)
																
	type t_token = Target_Lex.UserDeclarations.lexresult;
													
	(* ------------------------------------------------------------------ *)
	fun make_lexer(yyinput) =
		let
			val lexer = Target_Lex.makeLexer(yyinput)
		in
			fn () => lexer() handle Target_Lex.LexError => raise auxiliary_universal.ParseError("Target Lexer: " ^ auxiliary_universal.posToString(getNextTokenPos "") ^ ": syntax error")
		end
				
	(* ------------------------------------------------------------------ *)		
	fun extract_token( Target_Lex.UserDeclarations.SHELL(x,y,pos) ) = x;
	fun extract_SHELL_value( Target_Lex.UserDeclarations.SHELL(x,y,pos) ) = y;
	fun extract_SHELL_pos( Target_Lex.UserDeclarations.SHELL(x,y,pos) ) = pos;
	fun extract_SDT_value(x) = raise General.Fail("an_error");
					
	val IsTokenIdEqualTokenValue = fn Target_Lex.UserDeclarations.SHELL(x,y,pos) => x = y;
				
	val IsSDT = fn (x) => false;
				
	(* ------------------------------------------------------------------ *)
	fun print_token ( Target_Lex.UserDeclarations.SHELL(x,y,pos) ) =
		(
			print("\n  SHELL(");
			print(x:string);
			print(",");
			print(y:string);
			print(") \n")
		);
						
	(* ------------------------------------------------------------------ *)
	fun token_string ( Target_Lex.UserDeclarations.SHELL(x,y,pos) ) =
		"Token ID    = " ^ x ^ "\n                 Token Value = " ^ y;
						
end; (* structure *)
(* ================================================================== *)

