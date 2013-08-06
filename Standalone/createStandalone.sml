
(* ---------------------------------------------------------------------------------------------------------------- *)
(* In sml 110.0.7, CM.make has argument type unit, and by default the file named "sources.cm" is loaded:

  CM.make ();
  
  E.g.,
  
  CM.make() handle _ => ignore(OS.Process.exit(0w1));
  

	OS.Process.success = 0wx0 : Word32.word
	OS.Process.failure = 0wx1 : Word32.word
	
	DOS: The standard error stream is file descriptor 2. 

*)
(* --------------------------------------------------------------------------------------------- *)
  

(* -------------------------------------------------------------------------
    start_symbol = the start symbol of the target language grammar.
    Note that the start symbol for TL is hardcoded in the parseTLP
    function below.	
	
	parser_file = a string identifier whose value denotes the name of the
	              exported parser function.
				  
    The GUI version is parameterized on both of these values. In the
	standalone (e.g., commandline.bat) version, these values are hardwired.
   -------------------------------------------------------------------------	
*)



(* put handleException in environment *)
CM.destabilize'("initial.cm");
CM.stabilize'("initial.cm",true);  
CM.make'("initial.cm"); 



CM.destabilize'("support.cm");
CM.stabilize'("support.cm",true) handle e => HANDLER.handleException("In createStandalone:CM.stabilize support.cm", e); 
CM.make'("support.cm")           handle e => HANDLER.handleException("In createStandalone:CM.make support.cm", e);


CM.destabilize'("standalone.cm");
CM.stabilize'("standalone.cm",true) handle e => HANDLER.handleException("In createStandalone:CM.stabilize standalone.cm", e); 
CM.make'("standalone.cm") 			handle e => HANDLER.handleException("In createStandalone:CM.make standalone.cm", e);


(* ================================================================================================================ *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(*                                       Create Standalone                                                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* ================================================================================================================ *)

Environment.setTransformationFolder(CommandLineArgs.transformation_folder);
Environment.setTL(CommandLineArgs.tlp);
Environment.setIsUnParsedTargetProgram();
Environment.setTargetParser( Target.parser );


SMLofNJ.exportFn(OS.joinDirFile {dir = OS.joinDirFile {dir = CommandLineArgs.transformation_folder, file = "bin"}, file = CommandLineArgs.standalone_name}, Transform_Support.standaloneExe) 
         handle e => HANDLER.handleException("Error in creating transform executable",e); 
		 
		 
print("\n\nCreation of paradigm standalone completed.\n");

OS.Process.exit OS.Process.success; 
	
(* --------------------------------------------------------------------------------------------- *)


