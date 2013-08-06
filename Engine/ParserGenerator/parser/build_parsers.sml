(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   filename      : build_parsers.sml
   programmer    : Gary Fuehrer
   last modified : 07/25/01

   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* ====================================================================== *)
(*                           TARGET PARSER                                *)
(* ====================================================================== *)

(* -------------------------------------------------------------------- *)
signature target_parser_sig = 
sig
     val parse     : {start_symbol:string} -> (int -> string) -> CONCRETE_REPRESENTATION.TREE
	 val auxParser : string -> (int -> string) -> CONCRETE_REPRESENTATION.TREE
     val writeParser : BinIO.outstream -> unit
end;
(* -------------------------------------------------------------------- *)

functor target_parserFN(
							structure FilePath :
							sig
                                val isGrammar : bool (* true means it's a bnf, otherwise a .parser file *)
								val file : string
							end
						) : target_parser_sig =
							
struct
		(* ==================================================================== *)
		local
			(* parser to be used while parsing the tl program *)
			
			val parser_description = "Target Language Parser";
						
			val getNextTokenPos = auxiliary_universal.makeGetNextTokenPos(auxiliary_universal.targetLex_TokenStartPos_ref)
					
			(* -------------------------------------------------------------------- *)
			structure HatsTargetParser = BuildHatsParserFn
			(
				structure token_operations = TARGET_LEX_OPS_FN
				(
					val getNextTokenPos = getNextTokenPos
				)
			)
			(* -------------------------------------------------------------------- *)
			fun buildParser() =
                let
                    val istream = TextIO.openIn(FilePath.file)
                    val grammar = HatsTargetParser.readGrammar(istream, {stream_name=parser_description})
                                    
                    val _      = TextIO.closeIn(istream)
                    val _      = print("\nBUILDING THE TARGET PARSER...\n")
                    val parser = HatsTargetParser.makeParser(grammar)
                    val _      = print("DONE BUILDING THE TARGET PARSER\n\n")
                in
                    parser
                end
                
            fun readParser() =
                let
                    val istream = BinIO.openIn(FilePath.file)
                    val _      = print("\nREADING THE TARGET PARSER...\n")
                    val parser = HatsTargetParser.readParser(istream)
                    val _      = BinIO.closeIn(istream)
                    val _      = print("DONE READING THE TARGET PARSER\n\n")
                in
                    parser
                end
                
            val parser = if FilePath.isGrammar then
                            buildParser()
                         else
                            readParser()
                            
		(* ==================================================================== *)
		in (* local *)
					
			(* -------------------------------------------------------------------- *)
			(* parser to be used while parsing the input (target) program *)
			fun parse{start_symbol}(inputN) =
				let
					val _ = auxiliary_universal.targetLex_TokenStartPos_ref := {line = 0w1, column = 0w1}
				in
					HatsTargetParser.parse(parser){start_symbol=start_symbol}(inputN)
				end
				
			(* -------------------------------------------------------------------- *)
			(* parser to be used while parsing pieces of the target program *)
			(* that are embeded in the transformation program                *)
			fun auxParser(ds) =
				let
					val utf8_rbracket = 0wxef  (* this is the first byte in the 3-byte sequence: 239 128 154 *)
					
					fun	aux_extract[] 		= raise General.Fail("an_error -- see file build_parsers.sml")
					  | aux_extract(x::xs) 	= if (x <> #"[" andalso Byte.charToByte(x) <> utf8_rbracket)
											  then x::aux_extract(xs)
											  else [] (* finished *)
												
					fun extract_nonterminal(ds) = implode(aux_extract(explode(ds)));
								
					val nt = extract_nonterminal(ds);
				in
					fn (yyinput) =>
					let
						val _ 		= auxiliary_universal.targetLex_TokenStartPos_ref := !auxiliary_universal.tlLex_TokenStartPos_ref
						val tree 	= HatsTargetParser.parse(parser){start_symbol=nt}(yyinput)
						val _ 		= auxiliary_universal.tlLex_TokenStartPos_ref := !auxiliary_universal.targetLex_TokenStartPos_ref
					in
						tree
					end
				end
				
			fun writeParser(ostream) = HatsTargetParser.writeParser(ostream, parser)
								
		end (* local *)
		(* ==================================================================== *)
		
	end (* struct *)


(* ====================================================================== *)
(*                         end TARGET PARSER                              *)
(* ====================================================================== *)


(* ====================================================================== *)
(*                           TL PARSER                                    *)
(* ====================================================================== *)

(* -------------------------------------------------------------------- *)
signature TL_parser_sig = 
sig
     val parse     : {start_symbol:string} -> (int -> string) -> CONCRETE_REPRESENTATION.TREE
     val writeParser : BinIO.outstream -> unit
end;

(* -------------------------------------------------------------------- *)
functor TL_parserFN(
							structure ParserSupport :
							sig
                                val isGrammar : bool (* true means it's a bnf, otherwise a .parser file *)
								val file : string
								val auxParser   : string -> (int -> string) -> CONCRETE_REPRESENTATION.TREE
							end
						) : TL_parser_sig =
			
struct
		local
			val getNextTokenPos = auxiliary_universal.makeGetNextTokenPos(auxiliary_universal.tlLex_TokenStartPos_ref)
							
			(* -------------------------------------------------------------------- *)
			structure HatsTlParser = BuildHatsParserFn
			(
				structure token_operations = TL_LEX_OPS_FN
				(
					val getNextTokenPos = getNextTokenPos
					val call_aux_parser = ParserSupport.auxParser
				)
			)
			(* -------------------------------------------------------------------- *)
			val parser_description = "TL Parser:";
							
			fun buildParser() =
                let
                    val istream = TextIO.openIn(ParserSupport.file)
                    val grammar = HatsTlParser.readGrammar(istream, {stream_name=parser_description})
                                    
                    val _      = TextIO.closeIn(istream)
                    val _      = print("\nBUILDING THE TL PARSER...\n")
                    val parser = HatsTlParser.makeParser(grammar)
                    val _      = print("DONE BUILDING THE TL PARSER\n\n")
                in
                    parser
                end
                
            fun readParser() =
                let
                    val istream = BinIO.openIn(ParserSupport.file)
                    val _      = print("\nREADING THE TL PARSER...\n")
                    val parser = HatsTlParser.readParser(istream)
                    val _      = BinIO.closeIn(istream)
                    val _      = print("DONE READING THE TL PARSER\n\n")
                in
                    parser
                end
                
            val parser = if ParserSupport.isGrammar then
                            buildParser()
                         else
                            readParser()
						
		in
			(* parser to be used while parsing the transformation program *)
			fun parse(start_symb)(inputN) =
				let
					val _ = auxiliary_universal.tlLex_TokenStartPos_ref := {line = 0w1, column = 0w1}
				in
					HatsTlParser.parse(parser)(start_symb)(inputN)
				end
                
			fun writeParser(ostream) = HatsTlParser.writeParser(ostream, parser)
		end
  end (* struct *)
					
(* ====================================================================== *)
(*                           end TL PARSER                                *)
(* ====================================================================== *)
