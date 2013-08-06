(* Paradigm_RelativePath_Library_V2_G01_Build_004 *)

(* ------------------------------------------------------------------------------------------- *)
signature UserDefined_Sig =
sig
    (* The structure is: (function_id_string, function implementation in SML) list *)
    val functions :
        (
            string 
            *
            (
               (ABSTRACT_REPRESENTATION.EXPR list * ABSTRACT_REPRESENTATION.EXPR list) list
               ->
               ABSTRACT_REPRESENTATION.EXPR
            )
        ) list
end
(* ------------------------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------------------------- *)
structure UserDefined : UserDefined_Sig = struct
open ABSTRACT_REPRESENTATION;


(* ------------------------------------------------------------------------------------------- *) 
(* ------------------------------------------------------------------------------------------- *)	
fun pp [ program ] =
		(
			Output.pp(program, "java1");
			TRUE 
		)
  | pp _ = raise General.Fail("Error in UserDefined.pp: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)  
fun outputTransformed [ program ] =
		(
			Output.outputTransformed(Strategic_Values.getTerm program);
			TRUE 
		)
  | outputTransformed _ = raise General.Fail("Error in UserDefined.outputTransformed: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)  
fun lineNumber( [ term ] ) =
	let
		fun getLine( info( line_and_column ) ) = #line( line_and_column )
		fun getLabel( info( line_and_column ) ) = #label( line_and_column )
		
		val an_itree      = Strategic_Values.getTerm( term )
		val x_info        = Strategic_Values.getITREE_info( an_itree )
		val (low,high)    = getLine( x_info )
		val label_info    = getLabel( x_info )
	in
		print("\nFile:" ^ label_info ^ ":" ^ "Line Range " ^ Int.toString(low) ^ "-->" ^ Int.toString(high) ^ "\n");
		TRUE
	end
	
| lineNumber _ = raise General.Fail("Error in UserDefined.lineNumber: inappropriate arguments to function.\n");	

(* ------------------------------------------------------------------------------------------- *)	
(* ------------------------------------------------------------------------------------------- *)
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
	
(* ------------------------------------------------------------------------------------------- *)  	
fun inputInclude([tgt_file]) =
	let
		val unqualified_filename = stripQuotes( CONCRETE.getLeaf (Strategic_Values.getTerm tgt_file) )
		val input_filename = Environment.getInput_filename( unqualified_filename )
		
		val _ = print("Including: " ^ unqualified_filename ^ "\n");
		
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

  | inputInclude _ = raise General.Fail("Error in UserDefined.inputInclude: inappropriate arguments to function.\n");


(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*                                 Exported Function List                                      *)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(* stub element:     ("showEnvironment", (fn [ ( [TRUE], [TRUE]) ] => TRUE)) *)

	fun member( id1, (id2, _) :: rest) = (id1 = id2) orelse member(id1, rest)
	  | member( _, [] )                = false;
	 
	fun checkUnique( (x_str, x_fun) :: rest ) = if member(x_str, rest) then raise General.Fail("Error in UserDefined: The set of TL exported functions contains the duplicate name: " ^ x_str ^ "\n") 
												else checkUnique(rest)
      | checkUnique( [] ) = true												



    val functions = 

	Clocks.functions
	@
	Environment.functions
	@
	Ids.functions
	@
	Strategic_Views.functions
	@
	
	[
		("pp",                pp),
		("outputTransformed", outputTransformed),
		
		("lineNumber",        lineNumber),
		("inputInclude",      inputInclude)		
		
	];


	val _ = checkUnique functions;
	




(* ------------------------------------------------------------------------------------------- *)

end; (* struct *)

(* ------------------------------------------------------------------------------------------- *)

