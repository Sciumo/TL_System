
(* ------------------------------------------------------------------------------------------- *)
signature FILE_OPERATIONS_SIG =
sig

	val getXMLToken       			: TextIO.instream -> string
	val makeXMLToken       			: string * string * string * string -> string
	val extractXML_NodeInfo 		: string -> string * string * int * int * int * int * string
	val extractXML_NodeInfo_ITREE 	: string -> string * string list
	val XML_fileType				: string -> int
	

end;
(* ------------------------------------------------------------------------------------------- *)



(* ------------------------------------------------------------------------------------------- *)
structure FILE_OPERATIONS : FILE_OPERATIONS_SIG =
struct

val EMPTY_WORD    = "";
val GTR_THAN_STR  = ">";
val INCLUDE       = true;

val BLANK        = #" ";
val QUOTE        = #"\"";
val COLON        = #":";

(* ------------------------------------------------------------------------------------------- *)
fun XML_fileType( xml_token_str ) =	
		 if String.isPrefix "<itree"    xml_token_str then 1
	else if String.isPrefix "<abstract" xml_token_str then 2
	else 3
				
(* ------------------------------------------------------------------------------------------- *)
fun makeXMLToken( str, line_range, column_range, label_str ) =
			let
                fun convert( #"<"  :: xs ) = #"&" :: #"l" :: #"t" :: #";"                   :: convert xs
                  | convert( #">"  :: xs ) = #"&" :: #"g" :: #"t" :: #";"                   :: convert xs
                  | convert( #"&"  :: xs ) = #"&" :: #"a" :: #"m" :: #"p" :: #";"           :: convert xs
                  | convert( #"\"" :: xs ) = #"&" :: #"q" :: #"u" :: #"o" :: #"t" :: #";"   :: convert xs
                  | convert( #"'"  :: xs ) = #"&" :: #"a" :: #"p" :: #"o" :: #"s" :: #";"   :: convert xs
									
                  | convert( x     :: xs ) = x :: convert xs
                  | convert( []          ) = []
				  
				val value = "value=\"" ^ implode( convert (explode str) ) ^ "\""
			in
				value ^ " line ="  ^ "\"" ^ line_range   ^ "\""
					  ^ " column=" ^ "\"" ^ column_range ^ "\"" 
					  ^ " label="  ^ "\"" ^ label_str    ^ "\""
			end

(* ------------------------------------------------------------------------------------------- *)
(* A tag is treated as a single string -- which still needs to be decomposed.
   This string is of the form:

         <alpha>

    Internally, the symbols of alpha must be converted from xml symbols to
    corresponding strings. For example:

	&lt;  --> <
        &gt;  --> >
	etc.

*)


fun xml_symbol_to_actual(xml_token_list) = 
		let
		     fun replace(#"&" :: #"l" :: #"t" :: #";"                 :: xs) =   #"<"  :: replace(xs)
		       | replace(#"&" :: #"g" :: #"t" :: #";"                 :: xs) =   #">"  :: replace(xs)
		       | replace(#"&" :: #"a" :: #"m" :: #"p" :: #";"         :: xs) =   #"&"  :: replace(xs)
		       | replace(#"&" :: #"q" :: #"u" :: #"o" :: #"t" :: #";" :: xs) =   #"\"" :: replace(xs)
 		       | replace(#"&" :: #"a" :: #"p" :: #"o" :: #"s" :: #";" :: xs) =   #"'"  :: replace(xs)

		       | replace( x :: xs ) = x :: replace(xs)
		       | replace( [] )      = []

		in
			replace( xml_token_list )
		end
(* ------------------------------------------------------------------------------------------- *)
fun getXMLToken(in_stream) =  
		let
				(* ----------------------------------------------------------- *)
				fun get_xml_word(w, end_marker, include_end) =

				      (* note no error checking *)
	
				      let
				          val c = str(valOf(TextIO.input1(in_stream)));
				      in
				          if c = end_marker
				          then (* end of xml tag has been found *)
				               	if include_end then w^c
						else w

				          else (* still in the word *) 
				               get_xml_word(w^c ,end_marker, include_end)               
				      end;

				(* ----------------------------------------------------------- *)

				fun strip_leading_blanks(x::xs) = if Char.isSpace(x) then strip_leading_blanks(xs)
								                  else implode(x::xs)
				  | strip_leading_blanks _      = raise General.Fail("Error in FILE_OPERATIONS.get_token.strip_leading_blanks.\n")

				(* ----------------------------------------------------------- *)

				val raw_token = get_xml_word(EMPTY_WORD, GTR_THAN_STR, INCLUDE);
				val xml_token = strip_leading_blanks(explode(raw_token))
		in
			xml_token
		end

(* ------------------------------------------------------------------------------------------- *)	
val xml_token_ref = ref "";
			
fun split (xs, y) = 
	let
		fun aux(x::xs, y, acc) = if x = y then (acc, xs) (* note that y is not included in the split *)
								 else aux(xs, y, x::acc)
		
		  | aux( [], y, acc)   = raise General.Fail("Error in FILE_OPERATIONS.split.aux -- split-point not found. y = " ^ Char.toString(y) ^ " acc = " ^ implode(rev(acc)) ^ "\n")
		
		val (acc, rest) = aux(xs,y,[])  handle General.Fail(s) => (
                                                                    print(s);
                                                                    raise General.Fail(s ^ "xml_token = " ^ !xml_token_ref ^ "  xs = " ^ implode xs ^ "  y = " ^ Char.toString y)
                                                                  )   

	in
		(rev(acc), rest)
	end
	
(* ------------------------------------------------------------------------------------------- *)
fun drop_last2 ( x1::x2::[] ) = []
  | drop_last2 ( x::xs)       = x::drop_last2(xs)
  | drop_last2 ( []  )        = raise General.Fail("Error in FILE_OPERATIONS.drop_last2: input list must have a length greater than zero\n");

(* ------------------------------------------------------------------------------------------- *)
(* it is assumed that xs_0 has the form: line ="13:82" column="9:90" label="filename"> *)
fun getPositionInfo( xs_0 ) =
	let
		(* ------------------------------------------------------------------------------------------- *)						
		val (line_tag            , xs_1 ) = split(xs_0, QUOTE   )   (* line=       *)								
		val (line_low_list       , xs_2 ) = split(xs_1, COLON   )   (* x_lo        *)				
		val (line_high_list      , xs_3 ) = split(xs_2, QUOTE   )   (* x_hi        *)						
															
		val (column_tag          , xs_4 ) = split(xs_3, QUOTE   )   (* column=     *)				
		val (column_low_list     , xs_5 ) = split(xs_4, COLON   )   (* y_lo        *)						
		val (column_high_list    , xs_6 ) = split(xs_5, QUOTE   )   (* y_high      *)								

		val (label_tag           , xs_7 ) = split(xs_6, QUOTE   )   (* label=      *)				
		val (label_info_list            ) = drop_last2(xs_7     )   (* filename -- dropping the last QUOTE and the GTR_THAN character   *)						
				
		val line_low_str  			=   implode line_low_list 
		val line_high_str 			=   implode line_high_list 
							
		val column_low_str  		=   implode column_low_list  
		val column_high_str 		=   implode column_high_list 		
				
		val label_info_str			=   implode label_info_list
	in
		[line_low_str, line_high_str, column_low_str, column_high_str, label_info_str]
	end

(* ------------------------------------------------------------------------------------------- *)
fun process ((#"\\")::(#"n")::xs) = #"\n"::process(xs)
  | process ((#"\\")::(#"t")::xs) = #"\t"::process(xs)
 (* | process ((#"\"")::xs)       = process(xs) *)
  | process (x::xs)               = x::process(xs)
  | process []                    = [];
											
(* ------------------------------------------------------------------------------------------- *)
fun extractXML_NodeInfo_ITREE( xml_token ) = 
	let
		val _ = xml_token_ref := xml_token;		
										
		(* ------------------------------------------------------------------------------------------- *)
		(* it is assumed that xs_0 has the form: inode="value" line ="13:82" column="9:90"> *)
		fun get_inode xs_0 =
			let
							
				val (raw_value      , xs_1) = split(xs_0, QUOTE   )   
				val position_data_list 		= getPositionInfo(xs_1)
							
				val symbol_list    = xml_symbol_to_actual raw_value
				val value          = implode (process symbol_list)
			in
				value :: position_data_list
			end
						
		(* ------------------------------------------------------------------------------------------- *)		
		(* it is assumed that xs_0 has the form: imatch_var="nonterminal" schema_id="identifier" line ="13:13" column="9:9"> *)
		fun get_imatch xs_0 =
			let
				val (raw_nonterminal   , xs_1) = split(xs_0, QUOTE   )   (*  nonterminal" schema_id="identifier" line ="13:13" column="9:9"> 
																			 ==> 
																			(nonterminal, schema_id="identifier" line ="13:13" column="9:9"> 
																		 *)   				
				
				val (schema_id_tag     , xs_2) = split(xs_1, QUOTE   )   (* schema_id="identifier" line ="13:13" column="9:9"> 
																			==> 
																			(schema_id=, identifier" line ="13:13" column="9:9">) 
																		 *)
																		 
				val (raw_identifier     , xs_3) = split(xs_2, QUOTE   )   (* identifier" line ="13:13" column="9:9"> 
																			==> 
																			(identifier, line ="13:13" column="9:9">) 
																		  *)

				val position_data_list 		= getPositionInfo(xs_3)
				
				val nonterminal           = implode( process (xml_symbol_to_actual raw_nonterminal) )
				val identifier            = implode( process (xml_symbol_to_actual raw_identifier) )
			in
				nonterminal :: identifier :: position_data_list
			end
		(* ------------------------------------------------------------------------------------------- *)
		val xs_0                    = explode xml_token
				
		(*
			<itree inode="inode_value" line ="13:82" column="9:90">
			or
			<itree imatch_var="nonterminal" schema_id="identifier" line ="13:82" column="9:90"> 
		*)
		
		val (itree_tag      , xs_1) = split(xs_0, QUOTE   )   (* <itree inode="  or <itree imatch_var=" *)

		val node_data =      if implode itree_tag = "<itree inode="      then ("inode"     , get_inode  xs_1)
						else if implode itree_tag = "<itree imatch_var=" then ("imatch_var", get_imatch xs_1)
						else raise General.Fail("Error: in FILE_OPERATIONS.extractXML_NodeInfo_ITREE -- expected inode or imatch_var, but found " ^ implode(xs_1) ^ "\n")
	in
		node_data
	end

	
(* ------------------------------------------------------------------------------------------- *)
fun extractXML_NodeInfo( xml_token ) = 
	let
		val _ = xml_token_ref := xml_token;
		
		val xs_0                    = explode xml_token
		
		(* <abstract node="node_type" value="node_value" line ="7:12" column="1:42"> *)
		val (tree_type           , xs_1 ) = split(xs_0, QUOTE   )   (* <abstract node= *)
		val (node_type           , xs_2 ) = split(xs_1, QUOTE   )   (* a constructor from the datatype ABSTRACT.EXPR (e.g., STRING) *)
		val (node_value_tag      , xs_3 ) = split(xs_2, QUOTE   )   (* value= *)
		val (indirect_node_value , xs_4 ) = split(xs_3, QUOTE   )   (* data (e.g., a string value) *)
		
		val [line_low_str, line_high_str, column_low_str, column_high_str, label_info_str] = getPositionInfo( xs_4 )
																	
		val symbol_list         = xml_symbol_to_actual indirect_node_value
        val direct_node_value   = process symbol_list
										
		val line_low  			=   valOf( Int.fromString( line_low_str ) )
		val line_high 			=   valOf( Int.fromString( line_high_str ) )
		
		val column_low  		=   valOf( Int.fromString( column_low_str  ) )
		val column_high 		=   valOf( Int.fromString( column_high_str ) )		
	in
	   ( implode(node_type), implode(direct_node_value), line_low, line_high, column_low , column_high, label_info_str ) 
	end
																	
(* ------------------------------------------------------------------------------------------- *)
end;
(* ------------------------------------------------------------------------------------------- *)
(*                            end FILE_OPERATIONS                                              *)
(* ------------------------------------------------------------------------------------------- *)
 

























