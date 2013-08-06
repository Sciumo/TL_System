local
    structure OSP = OS.Path

    val [transformation_folder, bnf, start_symbol] = CommandLine.arguments();  (* ex. ["c:\foo\", "grammar.bnf", "CompilationUnit"] *)
    
    val parser_dir = OSP.joinDirFile {dir = transformation_folder, file = "bin"}
    
    val parser_file = OSP.joinDirFile {dir = parser_dir, file = "parser"}
    
    val TGT_parser_file = OSP.joinDirFile {dir = parser_dir, file = OSP.joinBaseExt {base = "Target", ext = SOME "parser"}}
    val TL_parser_file  = OSP.joinDirFile {dir = parser_dir, file = OSP.joinBaseExt {base = "TL",     ext = SOME "parser"}}
    
    val TGT_grammar = OSP.joinDirFile {dir = OSP.joinDirFile {dir = transformation_folder, file = "Syntax"}, file = bnf}
    val TL_grammar  =
        OSP.joinDirFile {dir =
        OSP.joinDirFile {dir =
        OSP.joinDirFile {dir =
        OSP.joinDirFile {
            dir = OSP.parentArc,
            file = "Engine"},
            file = "ParserGenerator"},
            file = "parser"},
            file = "tl_grammar"}
    
(* ---------------------------------------------------------------------------------------------- *)
(* build parser tables *)
(* ---------------------------------------------------------------------------------------------- *)
    
    val _ = print ("Creating target parser tables...\n")
    
    structure targetGrammar = 
        struct 
            val isGrammar = true
            val file      = TGT_grammar
        end;
    structure target_parser = target_parserFN (structure FilePath = targetGrammar)
    
    val _ = print ("Creating TL parser tables...\n")
    
    structure TL_parserSupport = 
        struct
            val isGrammar = true
            val file      = TL_grammar
            val auxParser = target_parser.auxParser
        end;
    structure TL_parser = TL_parserFN (structure ParserSupport = TL_parserSupport)
    
    val _ = print ("Done creating parser tables.\n");
    
(* ---------------------------------------------------------------------------------------------- *)
(* read in the target grammar *)
(* ---------------------------------------------------------------------------------------------- *)
    
    val _ = print ("Reading target grammar...\n")
    
    val getNextTokenPos = auxiliary_universal.makeGetNextTokenPos (auxiliary_universal.targetLex_TokenStartPos_ref)
    structure HatsTargetParser = BuildHatsParserFn (structure token_operations =
        TARGET_LEX_OPS_FN (val getNextTokenPos = getNextTokenPos)
    )
    
    val tgt_istream = TextIO.openIn (TGT_grammar)
    val tgt_grammar = HatsTargetParser.getGrammar( HatsTargetParser.readGrammar(tgt_istream, {stream_name="Target Language Grammar"}) )
    val _           = TextIO.closeIn (tgt_istream)
    
    val _ = print ("Done reading grammar.\n")
    
(* ---------------------------------------------------------------------------------------------- *)
(* parser functions *)
(* ---------------------------------------------------------------------------------------------- *)
    
    fun ParseTarget (input_filename, infilespec, outfilespec) =
        let
            val _  = CONCRETE_REPRESENTATION.setLabel (input_filename)
            val is = TextIO.openIn (infilespec)
            val target_tree =
                target_parser.parse {start_symbol = start_symbol} (fn n => TextIO.inputN (is, n))
                handle CONCRETE_REPRESENTATION.AmbiguousParse (parse_tree1, parse_tree2) =>
                        (
                            CONCRETE.toFile (
                                outfilespec ^ ".Ambiguous1.parsed", 
                                infilespec, 
                                CONCRETE_REPRESENTATION.convertToITREE (parse_tree1)
                            );
                            
                            CONCRETE.toFile (
                                outfilespec ^ ".Ambiguous2.parsed", 
                                infilespec, 
                                CONCRETE_REPRESENTATION.convertToITREE (parse_tree2)
                            );
                            
                            TextIO.output (TextIO.stdErr, "ambiguous parse\n");
                            raise General.Fail ("target_program parse failed")
                        ) 
                   | auxiliary_universal.ParseError (error_msgs) =>
                        (
                            TextIO.output (TextIO.stdErr, "Target program parse failed.\n" ^ error_msgs ^ "\n\n");
                            raise General.Fail ("target_program parse failed")
                        ) 
                   | General.Fail (error_msgs) =>
                        (
                            TextIO.output (TextIO.stdErr, error_msgs);
                            raise General.Fail (error_msgs)
                        ) 
                   | e =>
                        (
                            TextIO.output(TextIO.stdErr, exnName e);
                            raise e 
                        )
            val _ = TextIO.closeIn(is)
            
            (* ---------------------------------------------------------------------------------- *)
            
            val adjusted_target_tree    = CONCRETE_REPRESENTATION.adjustInfo (target_tree);
            
            val target_itree            = CONCRETE_REPRESENTATION.convertToITREE (adjusted_target_tree)
            val _                       = CONCRETE.toFile (outfilespec, infilespec, target_itree)
        in
            OS.Process.exit OS.Process.success
        end
    
(* ---------------------------------------------------------------------------------------------- *)
    
    fun ParseTL (TL_input_folder, TL_output_folder, tl_file_without_extension) =
        let
            fun aux_ParseTL (module_name, infile, outfile) =
                let
                    val _  = print("Parsing " ^ module_name ^ "\n");
                    val _  = CONCRETE_REPRESENTATION.setLabel (module_name)
                    val is = TextIO.openIn (infile);
                    val raw_TL_Unit = 
                        TL_parser.parse {start_symbol="TL_Unit"} (fn _ => TextIO.inputN(is, 1))
                        handle CONCRETE_REPRESENTATION.AmbiguousParse(parse_tree1, parse_tree2) =>
                            (
                                CONCRETE.toFile (
                                    outfile ^ ".Ambiguous1.parsed", 
                                    infile, 
                                    CONCRETE_REPRESENTATION.convertToITREE( parse_tree1 )
                                );
                                            
                                CONCRETE.toFile (
                                    outfile ^ ".Ambiguous2.parsed", 
                                    infile, 
                                    CONCRETE_REPRESENTATION.convertToITREE( parse_tree2 )
                                );
                                
                                TextIO.output (TextIO.stdErr, "ambiguous parse\n");
                                raise General.Fail ("tl_program parse failed")
                            )
                        |  auxiliary_universal.ParseError (error_msgs) =>
                            (
                                TextIO.output (TextIO.stdErr, "TL program parse failed.\n" ^ error_msgs ^ "\n\n");
                                raise General.Fail ("tl_program parse failed")
                            ) 
                        |  General.Fail (error_msgs) =>
                            (
                                TextIO.output(TextIO.stdErr, error_msgs);
                                raise General.Fail(error_msgs)
                            ) 
                        |  e =>
                            (
                                TextIO.output (TextIO.stdErr, exnName e);
                                raise e
                            )
                    val _ = TextIO.closeIn(is)
                in
                    raw_TL_Unit
                end
                
            (* ---------------------------------------------------------------------------------- *)
            
            val input_file  = OSP.joinDirFile {dir = TL_input_folder, file = OSP.joinBaseExt {base = tl_file_without_extension, ext = SOME "tlp"}}
            val output_file = OSP.joinDirFile {dir = TL_output_folder, file = tl_file_without_extension}
            val raw_TL_Unit = aux_ParseTL (tl_file_without_extension, input_file, output_file)
            
            val _ = modulePreprocessor.setTL_input_folder (TL_input_folder);
            val _ = modulePreprocessor.setTL_output_folder (TL_output_folder);
            val ((precision, verbosity), raw_tl_program) =  modulePreprocessor.process (aux_ParseTL, raw_TL_Unit);
            
            (* ---------------------------------------------------------------------------------- *)
            
            val adjusted_tl_program =
                CONCRETE_REPRESENTATION.liftSchemaVar ( 
                    CONCRETE_REPRESENTATION.adjustInfo (raw_tl_program)
                ); 
                                                                
            val abstract_tl_program = OPTIMIZE.optimize ( 
                precision,
                verbosity,
                
                tgt_grammar,    
                ABSTRACT.fromConcrete (adjusted_tl_program)
            )
                                                        
            val _ = ABSTRACT.EXPR_toXML (output_file ^ ".parsed", input_file, abstract_tl_program)
        in
            OS.Process.exit OS.Process.success
        end
    
(* ---------------------------------------------------------------------------------------------- *)
    
    fun ParseFile (arg0, ["TGT", input_folder, output_folder, input_filename_with_extension]) =
        let
            val (input_filename, extension) = Basic_Support.splitExtension(input_filename_with_extension)
        in
            ParseTarget (
                input_filename,
                OSP.joinDirFile {dir = input_folder, file = input_filename_with_extension},
                OSP.joinDirFile {dir = output_folder, file = OSP.joinBaseExt {base = input_filename, ext = SOME "parsed"}}
            )
            handle e => HANDLER.handleException ("", e)  
        end
        
      | ParseFile (arg0, ["TLP", Transformation_folder, tl_file_without_extension]) =
        let
            val TL_input_folder  = OSP.joinDirFile {dir = Transformation_folder, file = "TL_Modules"}
            val TL_output_folder = OSP.joinDirFile {dir = Transformation_folder, file = "bin"}
        in
            ParseTL (
                TL_input_folder,
                TL_output_folder,
                tl_file_without_extension
            )
            handle e => HANDLER.handleException ("", e)
        end
        
      | ParseFile _ = OS.Process.exit (OS.Process.failure); 
    
(* ---------------------------------------------------------------------------------------------- *)
    
    fun writeTargetParser () = 
        let
            val ostream = BinIO.openOut (TGT_parser_file)
            val _ = target_parser.writeParser (ostream)
        in
            BinIO.closeOut (ostream)
        end

    fun writeTLParser () = 
        let
            val ostream = BinIO.openOut (TL_parser_file)
            val _ = TL_parser.writeParser (ostream)
        in
            BinIO.closeOut (ostream)
        end

(* ---------------------------------------------------------------------------------------------- *)
in
(* ---------------------------------------------------------------------------------------------- *)
    
    val _ = print ("Writing target parser table: " ^ TGT_parser_file ^ "\n")
    val _ = writeTargetParser ()
    
    val _ = print ("Writing TL parser table: " ^ TL_parser_file ^ "\n")
    val _ = writeTLParser ()
    
    val _ = print ("Writing parser: " ^ parser_file ^ "\n")
    val _ = SMLofNJ.exportFn (parser_file, ParseFile)
    
    val _ = print ("Done building parser.")
end
