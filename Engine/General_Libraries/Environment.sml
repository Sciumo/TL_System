
(* =========================================================================================== *)
(* ------------------------------------------------------------------------------------------- *)
(*                                    Environment                                              *)
(* ------------------------------------------------------------------------------------------- *)
(* =========================================================================================== *)


(* ------------------------------------------------------------------------------------------- *)
signature ENV_Sig =
sig
        datatype Mode =
            SingleFile
          | MultiFile
        
        val setTargetFolder                 : string -> unit;
        val setTargetIndex                  : int -> unit;
        val setTransformationFolder         : string -> unit;
        val setTargetFileName               : string -> unit;
        val setTargetExtension              : string -> unit;
        val setTargetParsedExtension        : string -> unit;
        val setTransformExe                 : (string * string list -> OS.Process.status) -> unit;
        val setTL                           : string -> unit;
        val setTransformedTargetExtension   : string -> unit;
        val setStandalone                   : bool   -> unit;
        val setTargetParser                 : (string -> string -> CONCRETE_REPRESENTATION.ITREE) -> unit;
        val setTargetStringParser           : (string -> string -> CONCRETE_REPRESENTATION.ITREE) -> unit;
        
        val setTransformerMode              : Mode   -> unit
        
        val getDomainFolder                 : unit -> string;
        val getInputFolder                  : unit -> string;
        val getOutputFolder                 : unit -> string;
        val getTransformationFolder         : unit -> string;
        val getInput_filename_wo_extension  : string -> string;
        val getInput_filename               : string -> string;
        val getOutput_filename              : string * string -> string;
        val getPP_filename                  : string -> string;
        val getTransformed_filename         : unit -> string;
        val getXML_filename                 : unit -> string;
        val standalone_mode                 : unit -> bool;
        val getParser                       : unit -> string;
        val getTargetParser                 : unit -> (string -> string -> CONCRETE_REPRESENTATION.ITREE);
        val getTargetStringParser           : unit -> (string -> string -> CONCRETE_REPRESENTATION.ITREE);
        val getTargetExtension              : unit -> string;
        val getTargetParsedExtension        : unit -> string;
        val getTargetFileName               : unit -> string;
        val getTransformExe                 : unit -> (string * string list -> OS.Process.status) option;
        val getTL_ParsedFileName            : unit -> string;
        val getTransformedTargetExtension   : unit -> string;
        val getStrategy                     : unit -> ABSTRACT_REPRESENTATION.EXPR;
        val getTerm                         : unit -> ABSTRACT_REPRESENTATION.EXPR;
        
        val get_TL_System_Key               : unit -> int * int * int;

        (* The structure is: (function_id_string, function implementation in SML) list *)
        val functions : (
                            string 
                            * 
                            (
                                (ABSTRACT_REPRESENTATION.EXPR list * ABSTRACT_REPRESENTATION.EXPR list) list 
                                -> 
                                ABSTRACT_REPRESENTATION.EXPR
                            )
                        ) list;
end;
(* ------------------------------------------------------------------------------------------- *)



structure Environment : ENV_Sig =
struct

(* ------------------------------------------------------------------------------------------- *)
(*                                    Key                                                      *)
(* ------------------------------------------------------------------------------------------- *)
val BUILD_DATE = (2012,6,12)
fun get_TL_System_Key() = BUILD_DATE



(* ------------------------------------------------------------------------------------------- *)
(*                                    Internal                                                 *)
(* ------------------------------------------------------------------------------------------- *)
val EMPTY = "";

datatype Mode =
    SingleFile
  | MultiFile

val transformerMode = ref NONE : Mode option ref; 

val domain_folder        		 = ref EMPTY;
val target_folder        		 = ref EMPTY;
val target_index                 = ref 0;
val transformation_folder 		 = ref EMPTY;
val target_file_name 			 = ref EMPTY;
val target_extension    		 = ref EMPTY;
val target_parsed_extension		 = ref "parsed";
val transform_exe                = ref (NONE : (string * string list -> OS.Process.status) option);
val transformed_target_extension = ref "transformed";
val tl_parsed                    = ref EMPTY;

val parser              = ref EMPTY;

val standalone          = ref false;

val target_parser_opt        = ref (NONE : (string -> string -> CONCRETE_REPRESENTATION.ITREE) option );
val target_string_parser_opt = ref (NONE : (string -> string -> CONCRETE_REPRESENTATION.ITREE) option);

val strategy_opt        = ref (NONE : ABSTRACT_REPRESENTATION.EXPR option);

(* --------------------------------------------------------------------------------------------- *)
fun readStrategy() = ABSTRACT.getMain(
										ABSTRACT.EXPR_FromXML_TREE_FORMAT( !tl_parsed )
				 				 	 )
									 handle e => HANDLER.handleException("\nIn Environment.readStrategy\n",e);	

(* ------------------------------------------------------------------------------------------- *)
(*                                    In                                                       *)
(* ------------------------------------------------------------------------------------------- *)

(* setDomainFolder moved because it now needs getInputFolder() and getOutputFolder() *)

fun setTargetFolder( path )   									= target_folder  := path;
fun setTargetIndex( i )  									    = target_index   := i;
fun setTransformationFolder( path )  							= transformation_folder := path;
fun setTargetFileName( tgt ) 									= target_file_name := tgt;
fun setTargetExtension( tgt_extension ) 						= target_extension := tgt_extension;
fun setTargetParsedExtension( tgt_parsed_extension )			= target_parsed_extension := tgt_parsed_extension;
fun setTransformExe( tfm_exe )                                  = transform_exe := SOME tfm_exe;
fun setTL( tl_filename ) 										= (
																	tl_parsed := OS.Path.joinDirFile {dir = OS.Path.joinDirFile {dir = !transformation_folder, file = "bin"}, file = OS.Path.joinBaseExt {base = tl_filename, ext = SOME "parsed"}};
																	strategy_opt := SOME (readStrategy())
																  )
fun setTransformedTargetExtension( transformed_tgt_extension ) 	= transformed_target_extension := transformed_tgt_extension
fun setStandalone( flag ) 										= standalone := flag;
fun setTargetParser( parser ) 									= target_parser_opt := SOME( parser )
fun setTargetStringParser( parser )                             = target_string_parser_opt := SOME( parser )

fun setTransformerMode mode = transformerMode := SOME mode

(* ------------------------------------------------------------------------------------------- *)
(*                                    Out                                                      *)
(* ------------------------------------------------------------------------------------------- *)
(* getDomainFolder() moved below setDomainFolder *)
fun getTargetFolder()                           = !target_folder
fun getTargetIndex()                            = !target_index
fun getInputFolder()                            = OS.Path.joinDirFile {dir = getTargetFolder(), file = Int.toString (getTargetIndex ())}
fun getOutputFolder()                           = 
    let
        val path = OS.Path.joinDirFile {dir = getTargetFolder(), file = Int.toString (getTargetIndex () + 1)}
        val _ = FileUtility.mkDirs(path) (* make sure path exists before returning *)
    in
        path
    end
fun getTransformationFolder()                   = !transformation_folder

(* -- from In section -- *)
fun setDomainFolder() = 
	let
		fun getPrefix( x :: xs, y :: ys ) = if x = y then x :: getPrefix(xs, ys) else []
		  | getPrefix _                   = raise General.Fail("Error: input_folder or output_folder is unassigned.\n")
		 
		fun dropLast( x1 :: x2 :: [] ) = [x1]
		  | dropLast( x :: xs        ) = x :: dropLast xs
	in
		domain_folder := implode( dropLast( getPrefix( explode( getInputFolder() ), explode( getOutputFolder() ) ) ) )
		handle e => HANDLER.handleException("\nIn Environment.setDomainFolder\n",e)
	end 

fun getDomainFolder()							= (setDomainFolder(); !domain_folder)

fun getInput_filename_wo_extension(filename)    = OS.Path.concat (if !standalone then EMPTY else getInputFolder (), filename)
fun getInput_filename(filename)                 = OS.Path.concat (if !standalone then EMPTY else getInputFolder (), OS.Path.joinBaseExt {base = filename, ext = SOME (!target_extension)})
fun getOutput_filename(filename, extension)     = OS.Path.concat (if !standalone then EMPTY else getOutputFolder(), OS.Path.joinBaseExt {base = filename, ext = SOME extension})
fun getPP_filename(extension)					= getOutput_filename(!target_file_name, extension) 
fun getTransformed_filename()					= getOutput_filename(!target_file_name, !transformed_target_extension)
fun getXML_filename() 							= getOutput_filename(!target_file_name, "xml")
fun standalone_mode()							= !standalone
fun getParser()             					= !parser
fun getTargetParser()							=  valOf( !target_parser_opt ) handle e => raise General.Fail("Error in Environment.getTargetParser. TargetParser = NONE\n")	
fun getTargetStringParser()                     = valOf( !target_string_parser_opt ) handle e => raise General.Fail("Error in Environment.getTargetStringParser. TargetStringParser = NONE\n")
fun getTargetExtension()       					= !target_extension
fun getTargetParsedExtension()   				= !target_parsed_extension
fun getTargetFileName()       					= !target_file_name
fun getTransformExe()                           = !transform_exe
fun getTL_ParsedFileName()  					= !tl_parsed
fun getTransformedTargetExtension()   			= !transformed_target_extension
fun getStrategy()                               = valOf( !strategy_opt ) handle e => raise General.Fail("Error in Environment.getStrategy. Strategy = NONE\n")	





(* --------------------------------------------------------------------------------------------- *)		


fun getTerm () =
    let
        val targetBase = getTargetFileName ()
        val targetExtension = getTargetExtension ()

        val tree =
            case !transformerMode of
                SOME SingleFile =>
                    if targetExtension = getTargetParsedExtension () orelse
                       targetExtension = getTransformedTargetExtension()
                    then
                        CONCRETE.ITREE_fromFile (getInput_filename targetBase)
                    else
                        getTargetParser () targetBase (getInput_filename targetBase)
              | SOME MultipleFile =>
                    CONCRETE.ITREE_fromFile (targetBase ^ "." ^ targetExtension)
              | NONE => raise Fail ("getTerm: mode not set")
    in
        ABSTRACT.makeTerm
            (
                tree,
                CONCRETE_REPRESENTATION.dummy_node_info  (* the target program has no "position" in the tlp program *)
            )
    end

(* ------------------------------------------------------------------------------------------- *)
fun show( [] ) =
	let
		fun modeToString (SOME SingleFile) = "Single"
		  | modeToString (SOME MultiFile ) = "Multiple"
		  | modeToString (NONE           ) = "ERROR - parsed status is unknown-this is an error"
	in
		print("\n===========================================================================================\n");
		print("Environment:\n");
		print("     domain_folder          = " ^ getDomainFolder() ^ "\n");
		print("     input_folder           = " ^ getInputFolder() ^ "\n");
		print("     output_folder          = " ^ getOutputFolder() ^ "\n");		
		print("     transformation_folder  = " ^ !transformation_folder ^ "\n");
		print("     standalone             = " ^ Bool.toString(!standalone) ^ "\n\n");
		
		print("     target filename              = " ^ !target_file_name ^ "\n");						
		print("     target extension             = " ^ !target_extension ^ "\n");				
		print("     target parsed extension      = " ^ !target_parsed_extension ^ "\n");						
		print("     target transformed extension = " ^ !transformed_target_extension ^ "\n");						
		print("     target program form is       = " ^ modeToString(!transformerMode) ^ "\n");
		print("\n===========================================================================================\n");		

		ABSTRACT_REPRESENTATION.TRUE
	end
  | show _     = raise General.Fail("Error in Environment.show: inappropriate arguments to function.\n")
  
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*                                 Exported Function List                                      *)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)

	val functions =
		[
			("showEnvironment" , show)
		]



end; (* struct *)

(* =========================================================================================== *)
(* ------------------------------------------------------------------------------------------- *)
(*                                  End Environment                                            *)
(* ------------------------------------------------------------------------------------------- *)
(* =========================================================================================== *)
