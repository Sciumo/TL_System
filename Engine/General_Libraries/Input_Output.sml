local
    structure OSP = OS.Path
in
structure Input_Output =
struct	

(* ------------------------------------------------------------------------------------------- *)
fun toDot programTerm =
    let
        val program = Strategic_Values.getTerm programTerm
        
        val targetBase = Environment.getTargetFileName ()
        val filename = OSP.joinBaseExt {base = targetBase, ext = SOME "dot"}
        
        val outFilename = OSP.concat (Environment.getOutputFolder (), filename)
        val _ = FileUtility.mkDirs (OSP.dir outFilename)

        val _ = FileUtility.mkDirs (OSP.dir outFilename)
        val outStream = TextIO.openOut outFilename
    in
        CONCRETE_REPRESENTATION.ITREE_toDot (targetBase, outStream, program);
        TextIO.closeOut outStream
    end

(* ------------------------------------------------------------------------------------------- *)
fun outputXML (transformedProgramTerm, outFilenameTerm) =
    CONCRETE.toFile (outFilenameTerm, "DUMMYNAME", transformedProgramTerm)
    handle e => HANDLER.handleException ("\nIn Input_Output.outputXML.\n", e)

(* ------------------------------------------------------------------------------------------- *)
fun multiFileInput targetRelativeFilePathTerm =
    let
        val filePath = CONCRETE.getLeaf (Strategic_Values.getTerm targetRelativeFilePathTerm)

        val targetFilePath = OS.Path.concat (Environment.getInputFolder (), filePath)
        val targetFilename = OS.Path.file filePath
        val {base = targetBase, ext = targetExtension} = OS.Path.splitBaseExt targetFilename

        val tree =
            if isSome targetExtension andalso
               (valOf targetExtension = Environment.getTargetParsedExtension () orelse
                valOf targetExtension = Environment.getTransformedTargetExtension())
            then
                CONCRETE.ITREE_fromFile targetFilePath
            else
                Environment.getTargetParser () targetBase targetFilePath
    in
        ABSTRACT.makeTerm
            (
                tree,
                CONCRETE_REPRESENTATION.dummy_node_info  (* the target program has no "position" in the tlp program *)
            )
    end

(* ------------------------------------------------------------------------------------------- *)
fun parse({hasExtension=filename_has_extension, isQuoted=filename_is_quoted}, tgt_file) =
	let
		(* ------------------------------------------------------------------------------------------------ *)
		fun stripQuotes( x ) =
			let
				fun stripLast (x :: []) = []
				| stripLast (x :: xs) = x :: stripLast xs
				| stripLast _         = raise General.Fail("Error in UserDefined.stripLast.\n");

				fun aux_stripQuotes (x::xs) = stripLast xs
				| aux_stripQuotes _       = raise General.Fail("Error in UserDefined.stripQuotes.\n");
			in
				implode( aux_stripQuotes (explode x) )
			end
			
		(* ------------------------------------------------------------------------------------------------ *)
		val raw_file = CONCRETE.getLeaf (Strategic_Values.getTerm tgt_file)
		val unqualified_filename = if filename_is_quoted then stripQuotes( raw_file ) else raw_file
		
		val input_filename = if filename_has_extension 
							 then Environment.getInput_filename_wo_extension( unqualified_filename )
							 else Environment.getInput_filename( unqualified_filename )
		
		val _ = print("Including: " ^ unqualified_filename ^ "\n");
		val _ = print("Full path: " ^ input_filename ^ "\n");
	   (* val here = OS.FileSys.getDir(); *)		
	   
		val parsedFile     = Environment.getTargetParser() unqualified_filename input_filename 
		                     handle e => (
										    print("could not open the file " ^ input_filename ^ "\n");
											print("Directory = " ^ OS.FileSys.getDir() ^ "\n");
											HANDLER.handleException("could not open the file " ^ input_filename ^ "\n",e)

							             )
										 
	(* ------------------------------------------------------------------------------------------- *)	
	in

		ABSTRACT.makeTerm(
							parsedFile
							,
							CONCRETE_REPRESENTATION.dummy_node_info  (* the target program has no "position" in the tlp program *)
						)
	end

  
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*                                 Exported Function List                                      *)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
local
    type internal_tl_type = (ABSTRACT_REPRESENTATION.EXPR list * ABSTRACT_REPRESENTATION.EXPR list) list
    fun execVoid f (arg : internal_tl_type ) =
    (
        f arg;
        ABSTRACT_REPRESENTATION.TRUE
    )


    fun TL_toDot [programTerm] = toDot programTerm
      | TL_toDot _ = raise Fail "Input_Output.TL_toDot: expects 1 argument"
      
    (* ------------------------------------------------------------------------------------------- *)
    fun xmlToFile [ programTerm ] =
        let
            val program        = Strategic_Values.getTerm programTerm
            val targetFileName = Environment.getTargetFileName()
            val filename       = OSP.joinBaseExt {base = targetFileName, ext = SOME "xml"}
            
            val outFilename = OSP.concat (Environment.getOutputFolder (), filename)

            val _ = FileUtility.mkDirs (OSP.dir outFilename)
        in
            CONCRETE.toFile (outFilename, targetFileName, program)
            handle e => HANDLER.handleException ("\nIn Input_Output.xmlToFile.\n", e)
        end
        
      | xmlToFile [ programTerm,  fileNameString ] =
        let
            val fileNameStr    = Strategic_Values.getString fileNameString
            val program        = Strategic_Values.getTerm programTerm
            val targetFileName = Environment.getTargetFileName()
            val filename       = OSP.joinBaseExt {base = fileNameStr, ext = SOME "xml"}
            
            val outFilename = OSP.concat (Environment.getOutputFolder (), filename)

            val _ = FileUtility.mkDirs (OSP.dir outFilename)
        in
            CONCRETE.toFile (outFilename, targetFileName, program)
            handle e => HANDLER.handleException ("\nIn Input_Output.xmlToFile.\n", e)
        end
      
in
    val functions =
        [
            ("toDot"    , execVoid TL_toDot),
            ("xmlToFile", execVoid xmlToFile)
        ]
end

end (* struct *)
end (* local *)
