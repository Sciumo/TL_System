(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   filename      : build_hats_parser
   programmer    : Gary Fuehrer
   last modified : 06/25/02

   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* ====================================================================== *)
(*                   BUILD HATS PARSER                                    *)
(* ====================================================================== *)

functor BuildHatsParserFn
  (
    structure token_operations : TOKEN_OPS
  ) :> PARSER where type parse_result = CONCRETE_REPRESENTATION.TREE =
  struct
																									
    datatype LR_parse_result = SUCCESS of CONCRETE_REPRESENTATION.TREE 
							 | FAILED  of {symbol:string, pos:{line: word, column: word}, expected:AtomSet.set}
																					
  (* ================================================================================================================================================== *)
  local
  
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
	structure TL_Token =
      struct
		type token = token_operations.t_token
        fun toAtom(token) = Atom.atom(token_operations.extract_token token)
        val lexer = token_operations.make_lexer
      end
								
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
    structure TL_ParseTree =
      struct
        type token      = TL_Token.token
        type parse_tree = CONCRETE_REPRESENTATION.TREE

        open CONCRETE_REPRESENTATION
		
		(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
        fun terminalNode(token) =
            let
                val node_name = token_operations.extract_token token
				val node_info = convertToInfo(token_operations.extract_SHELL_pos token) ;
            in
				if node_name = "schema_variable" then  (* schema variable in TL *)
                     let
                         val schema_name = if token_operations.IsTokenIdEqualTokenValue(token) 
                                           then raise General.Fail("\nIn build_hats_parser.terminal_node: schema variable must be a domain variable") 
                                           else token_operations.extract_SHELL_value token
                     in


                           tree(t_node("schema_variable", node_info), 
						          [ tree(schema_var (schema_name, node_info) , []) ] )

                     end

                else (* build t_node tree *)
                     tree(t_node(node_name, node_info),
                          if token_operations.IsSDT(token) then [token_operations.extract_SDT_value token]
                          else if token_operations.IsTokenIdEqualTokenValue(token) then []
                          else [tree(t_node(token_operations.extract_SHELL_value token, node_info), [])]
                         )
            end
		(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)				
        fun nonterminalNode{symbkey, trees} = 
				case trees of
				  [] 													 => tree(t_node(Atom.toString symbkey, getCurrentInfo()), [tree(t_node("", getCurrentInfo()), [])])
				| [tree(t_node(s,_), [tree(t_node(t, node_info) , [])])] =>	( 
																				if String.isPrefix "!#schema_variable_" s
																				then tree(schema_var(t, node_info), [])
																				else tree(t_node(Atom.toString symbkey, node_info), trees)
																			)
				| _ 													 => tree(t_node( Atom.toString symbkey, inferCurrentInfo (getInfo (hd trees), getInfo (List.last trees))), trees )
									
    end	(* struct *)			
							
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
    structure TL_ParseEvents =
      struct
        type token 			= TL_Token.token
        type parse_tree 	= TL_ParseTree.parse_tree
        type parse_result 	= LR_parse_result

		(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
        fun initialParseResult() = FAILED{symbol="", pos={line=0w0, column=0w0}, expected=AtomSet.empty}
					
		(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
        fun
          parseSuccessEventHandler(parse_tree, FAILED _) = SUCCESS parse_tree
        | parseSuccessEventHandler(parse_tree1, SUCCESS parse_tree2) = raise CONCRETE_REPRESENTATION.AmbiguousParse(parse_tree1, parse_tree2)
							
        open CONCRETE_REPRESENTATION
							
		(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
        fun tokenNotFoundEventHandler(_, success as SUCCESS _) = success
          | tokenNotFoundEventHandler({token=token', expected=expected'}, FAILED(failed as {symbol, pos=pos as {line, column}, expected})) =
				let
					val symbol' = token_operations.extract_token token'
					val pos' as {line=line', column=column'} = token_operations.extract_SHELL_pos token'
				in
					if line > line' then FAILED failed
					else if line < line' then FAILED{symbol=symbol', pos=pos', expected=AtomSet.addList(AtomSet.empty, expected')}
					else if column > column' then FAILED failed
					else if column < column' then FAILED{symbol=symbol', pos=pos', expected=AtomSet.addList(AtomSet.empty, expected')}
					else FAILED{symbol=symbol, pos=pos, expected=AtomSet.addList(expected, expected')}
				end
							
      end (* struct *)
	  (* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
							
  in
    structure LrParser = LR_ParserFn(
										structure Token 		= TL_Token 
										structure ParseTree 	= TL_ParseTree 
										structure ParseEvents 	= TL_ParseEvents
									)
						
  end (* local *)
  (* ================================================================================================================================================== *)
													
    datatype grammar 		= LR_GRAMMAR of LrParser.grammar
    datatype parser 		= LR_PARSER of LrParser.parser
    type parse_result 		= CONCRETE_REPRESENTATION.TREE
    datatype which_parser 	= USE_LR_PARSER 
													
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
    fun getWhichParserToUse(istream) =
		let
			val gram_type = TextIO.inputLine(istream)
		in
			if String.isPrefix("USE_LR_PARSER")(valOf(gram_type))
							
			then USE_LR_PARSER
			else raise General.Fail("Error: file = build_hats_parser.sml, function = getwhichParserToUse. Unsupported/unknown parser.\n")
		end
					
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
    fun readGrammar(istream, stream_name) =
			case getWhichParserToUse(istream) of
				USE_LR_PARSER => LR_GRAMMAR(LrParser.readGrammar(istream, stream_name))
							
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)		  
    fun makeParser(LR_GRAMMAR grammar) = LR_PARSER(LrParser.makeParser(grammar))
											
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)	  
    fun (* BUG fix me to insert parser kind at start of stream.  readParser below will use this *)
      writeParser(ostream, LR_PARSER parser) = LrParser.writeParser(ostream, parser)
	  
	fun readParser(istream) = LR_PARSER (LrParser.readParser istream)
							
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)
    fun composeParseErrors(errors) =
		let
			fun concat_string(t, s) = (if String.size(s) > 0 then s ^ ", " else "") ^ "'" ^ t ^ "'"
				
			fun compose_error({pos, expected, encountered, message}, s) =
				s ^ "\n  Line " ^ auxiliary_universal.posToString(pos) ^ ":  " ^ message ^ (if String.size(encountered) <= 0 then ""
				else " '" ^ encountered ^ "'.  Expected: " ^ (List.foldl concat_string "" expected))
		in
			"Every alternative failed to parse.  A list of syntax errors follows:"
			^ (List.foldl compose_error "" errors) ^ "\n"
		end
					
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)	  
    fun parse(LR_PARSER parser) = 
			(fn start_symbol => fn inputN =>
				case LrParser.parse(parser)(start_symbol)(inputN) of
					SUCCESS tree => tree
				  | FAILED{symbol, pos, expected} => raise auxiliary_universal.ParseError(composeParseErrors[{pos=pos, expected=List.map Atom.toString (AtomSet.listItems expected), encountered=symbol, message="Unexpected input"}])
			)
			
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)	  
	(* -------------------------------------------------------------------------------------------------------------------------------------------------- *)	  
	fun getGrammar( LR_GRAMMAR grammar ) = LrParser.getGrammar grammar 
												
  end; (* struct *)

(* ====================================================================== *)
(*                   end BUILD HATS PARSER                                *)
(* ====================================================================== *)
