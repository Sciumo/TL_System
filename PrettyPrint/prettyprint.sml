(* -------------------------------------------------------------------------------------------------- *)
local
    structure PRETTYPRINT_ENGINE = PRETTYPRINT_ENGINE_FN(structure UserStyles = PRETTYPRINT_STYLES);
    
    (* new sml doesn't pass executable name in CommandLine.arguments() *)
	fun getArgs( [ filename_w_extension] ) = filename_w_extension
	  | getArgs _ 				           = raise General.Fail("Error in prettyprint_tree.getArgs -- wrong number of arguments on the command line.\n")
	  
	val filename_w_extension = getArgs(CommandLine.arguments())
    
in
	fun prettyprinter() =
		let
			val (filename, extension) = Basic_Support.splitExtension filename_w_extension
		    val input_file            = filename ^ ".transformed"
			val output_file           = filename ^ ".pp" ;
			val input_tree            = CONCRETE.ITREE_fromFile input_file;
			
			val startTime    = ref Time.zeroTime;
			fun getTime()    = IntInf.toString(Time.toSeconds(Time.-(Time.now(),(!startTime))))
			fun startClock() = startTime := Time.now() 
			fun stopClock () = print("Elapsed Time for SML portion of pretty printing = " ^ getTime() ^ "\n\n") 
			
			val LM = "";
			val output_file = TextIO.openOut(output_file);
		in
			startClock();
			PRETTYPRINT_ENGINE.prettyprint(output_file, input_tree);
			stopClock();
			TextIO.closeOut(output_file)
		end;
end; 
(* -------------------------------------------------------------------------------------------------- *)

let
	val _ = prettyprinter() handle e => HANDLER.handleException("In prettyprint:prettyprinter()", e); 
in
	print("\n");
	OS.Process.exit OS.Process.success
end;
