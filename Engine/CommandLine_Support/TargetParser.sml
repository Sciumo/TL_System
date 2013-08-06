
(* ================================================================================================================ *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(*                                       Target Parser                                                              *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* ================================================================================================================ *)

(*
    Defined in Environment:
        TGT_Grammar
        start_symbol
*)   
structure Target =
struct

    val the_start_symbol  = CommandLineArgs.startSymbol
    val the_target_parser = OS.Path.joinDirFile {dir = OS.Path.joinDirFile {dir = Environment.getTransformationFolder (), file = "bin"}, file = OS.Path.joinBaseExt {base = "Target", ext = SOME "parser"}}

    (* ---------------------------------------------------------------------------------------------------------------- *)
    structure targetGrammar = 
    struct 
        val isGrammar = false
        val file = the_target_parser
    end;
                            
    structure target_parser = target_parserFN( structure FilePath = targetGrammar )
                            
    
    (* ---------------------------------------------------------------------------------------------------------------- *)
    (*   Read in the target grammar                                                                                     *)
    (* ---------------------------------------------------------------------------------------------------------------- *)
    val getNextTokenPos = auxiliary_universal.makeGetNextTokenPos(auxiliary_universal.targetLex_TokenStartPos_ref)
    structure HatsTargetParser = BuildHatsParserFn    (    structure token_operations = TARGET_LEX_OPS_FN
                                                                                        (
                                                                                            val getNextTokenPos = getNextTokenPos
                                                                                        )
                                                      )
                                                        
    (* val tgt_istream = TextIO.openIn(the_target_grammar)
    val tgt_grammar = HatsTargetParser.getGrammar( HatsTargetParser.readGrammar(tgt_istream, {stream_name="Target Language Grammar"}) )
    val _             = TextIO.closeIn(tgt_istream)     *)
                            
(* ================================================================================================================ *)
    fun parseStream is label start_symbol =
        let
            (* ------------------------------------------------------------------------------ *)
            val _  = CONCRETE_REPRESENTATION.setLabel(label)                
            val target_tree = target_parser.parse{start_symbol=start_symbol}(fn n => TextIO.inputN(is, n))
                               handle CONCRETE_REPRESENTATION.AmbiguousParse(parse_tree1, parse_tree2) => (
                                                                                                            TextIO.output(TextIO.stdErr, "ambiguous parse\n");
                                                                                                            raise General.Fail("target_program parse failed due to an ambiguous parse (redesign the grammar)")
                                                                                                          ) 
                                   | auxiliary_universal.ParseError(error_msgs)                        => (
                                                                                                            TextIO.output(TextIO.stdErr, "Target program parse failed.\n" ^ error_msgs ^ "\n\n" );
                                                                                                            raise General.Fail("target_program parse failed")
                                                                                                          ) 
                                   | General.Fail(error_msgs)                                           => (
                                                                                                            TextIO.output(TextIO.stdErr, error_msgs);
                                                                                                            raise General.Fail(error_msgs)
                                                                                                           ) 
                                   | e                                                                 => (
                                                                                                            TextIO.output(TextIO.stdErr, exnName e);
                                                                                                            raise e 
                                                                                                         )
            val _ = TextIO.closeIn(is)
                                    
            (* ------------------------------------------------------------------------------ *)
            val adjusted_target_tree     = CONCRETE_REPRESENTATION.adjustInfo( target_tree) ; 
                            
            val target_itree             = CONCRETE_REPRESENTATION.convertToITREE( adjusted_target_tree )
        in
            target_itree 
        end
        
    fun parseString str start_symbol =
        let
            val is = TextIO.openString str
            val target_itree = parseStream is "string" start_symbol
            val _ = TextIO.closeIn is
        in
            target_itree
        end
        
    fun parser input_filename infilespec =
        let 
            val is = TextIO.openIn infilespec
            val target_itree = parseStream is input_filename the_start_symbol
            val _ = TextIO.closeIn is
        in
            target_itree
        end
                            
      
end; (* struct *)
(* ================================================================================================================ *)
