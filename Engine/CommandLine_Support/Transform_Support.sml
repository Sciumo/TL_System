
structure Transform_Support =
struct

	
	structure SEMANTICS = SEMANTICS_FN(structure UserDefined = UserDefined); 

	(* --------------------------------------------------------------------------------------------- *)
	fun splitExtension str =
		let
			fun aux (#"." :: xs, extAcc) = (implode (rev xs), implode extAcc)
			  | aux (x :: xs   , extAcc) = aux (xs, x :: extAcc)
			  | aux ([], _)              = raise General.Fail ("Error in Transform_support.splitExtension.\n")
		in
			aux (rev (explode str), [])
		end

	(* --------------------------------------------------------------------------------------------- *)
	fun transform( strategy, term ) = 
		let
			val _      = METRICS.setStartTime();
			val result = SEMANTICS.applyMain( strategy, term )
						 handle e => HANDLER.handleException("\nError in Transform_Support.transform.\n",e)
			val _      = METRICS.printMetrics();
		in
			result
		end;
		
	(* --------------------------------------------------------------------------------------------- *)

    fun transformFile (targetFilename) =
        let
            val _ = print ("transformations:\t" ^ Environment.getTransformationFolder() ^ "\n");
            val _ = print ("tlp:\t"             ^ Environment.getTL_ParsedFileName () ^ "\n")
            val _ = print ("inputs:\t"          ^ Environment.getInputFolder () ^ "\n")
            val _ = print ("outputs:\t"         ^ Environment.getOutputFolder () ^ "\n")
            val _ = print ("target:"            ^ targetFilename ^ "\n")
            
            val (targetFilenameBase, targetFilenameExtension) = splitExtension targetFilename
                                                                handle e => HANDLER.handleException ("\nIn Transform_Support.transformeExe: expected file with dot extension.\n",e)
            
            val _ = Environment.setTargetFileName (targetFilenameBase);
            val _ = Environment.setTargetExtension (targetFilenameExtension);
            
            val strategy = Environment.getStrategy ()
            val tgt_term = Environment.getTerm ()
                           handle e => HANDLER.handleException("Error in Transform_Support.transformExe: unable to read target term.", e); 

            val _      = print ("\n\n=========RUN TRANSFORM=============\n\n");
            val result = transform (strategy, tgt_term)  
                         handle e => HANDLER.handleException ("Error in Transform_Support.transformExe: unable to transform target term.", e); 
        in
            OS.Process.exit OS.Process.success 
        end

    fun transformExe (arg0, args) =
        let
            val (opts, args) = CommandLineArgs.parseArgs (args)
            
            val [targetFilename] = args
                                   handle Bind => raise General.Fail ("error: exactly one target must be specified")
        in
            transformFile (targetFilename)
        end
    
	(* --------------------------------------------------------------------------------------------- *)
		fun standaloneExe(arg0, [target_filename]) =
		let
			val (target_filename_without_extension, extension) = splitExtension target_filename
																 handle e => HANDLER.handleException("\nIn Transform_Support.standaloneExe: expected file with dot extension.\n",e)

			val _ = Environment.setStandalone(true);
			val _ = Environment.setTargetFileName( target_filename_without_extension );
			val _ = Environment.setTargetExtension( extension );
			
			val tgt_term = Environment.getTerm()
						   handle e => HANDLER.handleException("Error in Transform_Support.standaloneExe: unable to read target term.",e); 

			val strategy = Environment.getStrategy();
			val result   = transform(strategy, tgt_term )
						   handle e => HANDLER.handleException("Error in Transform_Support.standaloneExe: strategy not found.",e); 
		in
			OS.Process.exit OS.Process.success 
		end
      | standaloneExe _ = raise General.Fail("\n Inappropriate number of command-line arguments.\n")

end; (* struct *)
(* --------------------------------------------------------------------------------------------- *)
