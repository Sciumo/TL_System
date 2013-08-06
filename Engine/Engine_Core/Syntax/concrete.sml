(* ------------------------------------------------------------------------------------------- *)
signature CONCRETE_SIG =
sig

	val ITREE_fromFile     			: string -> CONCRETE_REPRESENTATION.ITREE					    (* XML representation to ITREE *)
	val ITREE_fromEmbedded 			: string -> TextIO.instream -> CONCRETE_REPRESENTATION.ITREE	(* the string is the token *)
            
    (* XML file format *)                           
    val toFile  	        		: string * string * CONCRETE_REPRESENTATION.ITREE -> unit 
    val embeddedToFile      		: TextIO.outstream -> CONCRETE_REPRESENTATION.ITREE -> unit 
                                     
	val printTree           		: string -> CONCRETE_REPRESENTATION.ITREE -> unit
	val leavesToString      		: CONCRETE_REPRESENTATION.ITREE -> string
	val leavesToStringRaw      		: CONCRETE_REPRESENTATION.ITREE -> string    
	val leavesToStringWithSep  		: CONCRETE_REPRESENTATION.ITREE * string -> string 
    
	val bottom_up           		: (CONCRETE_REPRESENTATION.ITREE -> CONCRETE_REPRESENTATION.ITREE) -> CONCRETE_REPRESENTATION.ITREE -> CONCRETE_REPRESENTATION.ITREE
	
	val size               			: CONCRETE_REPRESENTATION.ITREE -> int

	(* ------------------------------------------------------------------- *)
                                     
	val getLeaf						: CONCRETE_REPRESENTATION.ITREE                                 -> string
	val replaceLeaf					: CONCRETE_REPRESENTATION.ITREE * string                        -> CONCRETE_REPRESENTATION.ITREE
	val eqLinearInternalStructure	: CONCRETE_REPRESENTATION.ITREE * CONCRETE_REPRESENTATION.ITREE -> bool
end;
(* ------------------------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------------------------- *) 
structure CONCRETE : CONCRETE_SIG =
struct

open CONCRETE_REPRESENTATION;


(* ------------------------------------------------------------------------------------------- *)
(*                                        fromFile                                             *)
(* ------------------------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------------------------- *)
(*
  ASSUMPTIONS:

   The data streams will be syntactically correct -- so no error checking
   will need to be done. 
*)


(* ------------------------------------------------------------------------------------------- *)
(*                                     XML File Type                                           *)
(* ------------------------------------------------------------------------------------------- *)

fun buildInfo( [ line_low_str, line_high_str, column_low_str, column_high_str, label_str ] ) =
	let
		val line_low  			=   valOf( Int.fromString( line_low_str ) )
		val line_high 			=   valOf( Int.fromString( line_high_str ) )
		
		val column_low  		=   valOf( Int.fromString( column_low_str  ) )
		val column_high 		=   valOf( Int.fromString( column_high_str ) )		
	in
		info { id = getInfoId(), line = (line_low,line_high), column = (column_low,column_high), label=label_str} 
	end
  | buildInfo _ = raise General.Fail("Error in CONCRETE.buildInfo: inappropriate position data.\n")
  

(* ------------------------------------------------------------------------------------------- *)
fun build_concrete_ITREE(("inode"     , value::position_data                   ), children ) = 
		let
			val x_info = buildInfo position_data
		in
			itree(inode(value, x_info), children)
		end
  | build_concrete_ITREE(("imatch_var", nonterminal::identifier::position_data ), children ) = 
		let
			val x_info = buildInfo position_data		
		in
			itree(imatch_var (nonterminal,identifier, x_info), children )
		end
  | build_concrete_ITREE _                                                                   = raise General.Fail("Error in CONCRETE.build_concrete_ITREE.\n")
					
(* ------------------------------------------------------------------------------------------- *)
fun ITREE_fromEmbedded token in_stream =
	let
		(* ----------------------------------------------------------------------- *)
		fun 
		    get_xml_tree token =
										
			let
				val node_data  = FILE_OPERATIONS.extractXML_NodeInfo_ITREE(token)
				val children   = get_xml_tree_list()
				
				(* the end tag for this tree has been consumed by get_xml_tree_list *)
			in
				build_concrete_ITREE(node_data, children)
			end
								
		and 
		    get_xml_tree_list() =
					
			let
				val concrete_end = "</itree>"
						
				(* next_token could be begin-tree or end-tree token *)
				val next_token = FILE_OPERATIONS.getXMLToken(in_stream)
			in
				if next_token = concrete_end then (* finished collecting siblings -- and this is the close tag of the parent tree *)
				   []
							
				   else (* at least one more sibling to collect *) 
					let
						val next_tree  = get_xml_tree next_token  
					in
						next_tree:: get_xml_tree_list()
					end
			end;
							
		(* ----------------------------------------------------------------------- *)
		(* may not have an empty tree -- i.e., at least two tokens *)
			
		val a_tree = get_xml_tree(token); 
	in
	     a_tree
	end;		
								
(* ------------------------------------------------------------------------------------------- *)
fun ITREE_fromFile(infile) = 
		let
		    val in_stream = TextIO.openIn(infile);

			val header    = FILE_OPERATIONS.getXMLToken(in_stream);
						
			val token     = FILE_OPERATIONS.getXMLToken(in_stream);
			val the_tree  = case FILE_OPERATIONS.XML_fileType token of
							  1  => ITREE_fromEmbedded token in_stream 
							| 2  => raise General.Fail("Error: expected concrete tree but found abstract term.\n")
							| _	 => raise General.Fail("Error: unknown file structure.\n")
									
(* ? *)    	val header    = FILE_OPERATIONS.getXMLToken(in_stream);

			
		in
			TextIO.closeIn(in_stream);
			the_tree
		end
					
(* ------------------------------------------------------------------------------------------- *)
(*                                       toFile                                                *)
(* ------------------------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------- *)
fun convert(id) = 
	let
		fun aux_convert( #"<"  :: xs ) = #"&" :: #"l" :: #"t" :: #";"                   :: aux_convert xs
		  | aux_convert( #">"  :: xs ) = #"&" :: #"g" :: #"t" :: #";"                   :: aux_convert xs
		  | aux_convert( #"&"  :: xs ) = #"&" :: #"a" :: #"m" :: #"p" :: #";"           :: aux_convert xs
		  | aux_convert( #"\"" :: xs ) = #"&" :: #"q" :: #"u" :: #"o" :: #"t" :: #";"   :: aux_convert xs
		  | aux_convert( #"'"  :: xs ) = #"&" :: #"a" :: #"p" :: #"o" :: #"s" :: #";"   :: aux_convert xs
									
		  | aux_convert( x     :: xs ) = x :: aux_convert xs
		  | aux_convert( []          ) = []
				  
		val value = implode( aux_convert (explode id) ) 
	in
		value
	end
		  
(* ------------------------------------------------------------------------- *)
fun embeddedToFile out_stream ( itree(inode(id, x_info ), children) ) =	
		let			
			val id_data                   = "\"" ^ convert(id) ^ "\""
            val uniqueId                  = "\"" ^ CONCRETE_REPRESENTATION.makeUniqueIdAttribute x_info   ^ "\""            
			val line_data                 = "\"" ^ CONCRETE_REPRESENTATION.makeLineAttribute x_info   ^ "\""
			val column_data               = "\"" ^ CONCRETE_REPRESENTATION.makeColumnAttribute x_info ^ "\""
			val label_data				  = "\"" ^ CONCRETE_REPRESENTATION.makeLabelAttribute x_info  ^ "\""
		in
			TextIO.output(out_stream,"<itree inode=" ^ id_data ^ " line=" ^ line_data ^ " column=" ^ column_data ^ " label=" ^ label_data ^ ">");
			map (embeddedToFile out_stream) children;
			TextIO.output(out_stream,"</itree>");
			TextIO.output(out_stream,"\n")
		end
 | embeddedToFile out_stream ( itree(imatch_var(symbol_type, symbol_id, x_info),[])) =
		let
			val symbol_type_data          = "\"" ^ convert(symbol_type) ^ "\""
			val symbol_id_data            = "\"" ^ convert(symbol_id) ^ "\""			
            val uniqueId                  = "\"" ^ CONCRETE_REPRESENTATION.makeUniqueIdAttribute x_info   ^ "\""            
			val line_data                 = "\"" ^ CONCRETE_REPRESENTATION.makeLineAttribute x_info   ^ "\""
			val column_data               = "\"" ^ CONCRETE_REPRESENTATION.makeColumnAttribute x_info ^ "\""
			val label_data				  = "\"" ^ CONCRETE_REPRESENTATION.makeLabelAttribute x_info  ^ "\""
			
		in
			(* schema_var = "<" ^ symbol_type ^ ">" ^ schema_id *)
			TextIO.output(out_stream,"<itree imatch_var=" ^ symbol_type_data ^ " schema_id=" ^ symbol_id_data ^ " line=" ^ line_data ^ " column=" ^ column_data ^ label_data ^ ">");
			TextIO.output(out_stream,"</itree>");
			TextIO.output(out_stream,"\n")
		end
 | embeddedToFile _ _ = raise General.Fail("\n Error in CONCRETE.embeddedToFile: badly formed tree\n");

(* ------------------------------------------------------------------------- *)
fun toFile( file_name, tree_name, a_tree ) =

	let
		val out_stream = TextIO.openOut(file_name)
	in
	    TextIO.output(out_stream,"<XML_FILE label=\"" ^ tree_name ^ "\">");
	    embeddedToFile out_stream a_tree; 
	    TextIO.output(out_stream,"</XML_FILE>");
																	
	    TextIO.closeOut out_stream
	end;

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)

val INDENT = "   ";

(* ------------------------------------------------------------------------- *)
(* be careful if you try to simplify this further *)

fun printTree LM (itree( inode(name, x_info), tree_list ) ) = 	let 
															val new_LM = LM      ^ INDENT
														in 
															print(LM ^   name     ); 
																		
															map (printTree new_LM) tree_list;
															()
														end
																		
  | printTree LM (itree(imatch_var (symbol_type,symbol_id, x_info), []) ) = 
					let 
					    val new_LM = LM ^ INDENT
					    val root   = "<" ^ symbol_type ^ ">" ^ symbol_id
					in 
                        print(LM ^ "imatch_var");
					    print(new_LM ^ root)
					end
																			
  | printTree LM t = (
                      print("\n\n=======================Error in CONCRETE.printTree=======================\n\n");
                      CONCRETE_REPRESENTATION.fullPrintTree LM t;

                      raise General.Fail("Error in CONCRETE.printTree: badly formed tree.\n")
                    );
													
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun leavesToString(itree( imatch_var (symbol_type,symbol_id, _), [] ) ) = "<" ^ symbol_type ^ ">" ^ symbol_id
  | leavesToString(itree( inode      (name, _)                 , [] ) ) = name
  
  | leavesToString(t as itree(inode(name,_),children) ) =
							let
                                val sep = " ";

							    fun traverse (itree( inode(name,_)                       , []       ) ) = name
							      | traverse (itree( imatch_var (symbol_type,symbol_id,_), []       ) ) = "<" ^ symbol_type ^ ">" ^ symbol_id
							      |	traverse (itree( inode(name,_)                       , children ) ) = foldr (fn (t, str) => (traverse t) ^ sep ^ str ) "" children
                                  | traverse t                                     	     			    = (
																											print("\n\n=========================================\n\n");
																											CONCRETE_REPRESENTATION.fullPrintTree " " t;
																											raise General.Fail("Error in CONCRETE.leavesToString.traverse.\n")
																										  );
							in
							    name ^ "[:]" ^  traverse t   ^ "[:]"
							end
  | leavesToString t = (
                          print("\n\n=========================================\n\n");
                          CONCRETE_REPRESENTATION.fullPrintTree " " t;
                          raise General.Fail("Error in CONCRETE.leavesToString.\n")
                       );

(* ------------------------------------------------------------------------------------------- *)
fun leavesToStringWithSep(itree( imatch_var (symbol_type,symbol_id,_), [] ), _ ) = "<" ^ symbol_type ^ ">" ^ symbol_id
  | leavesToStringWithSep(itree( inode      (name,_)                 , [] ), _ ) = name
  
  | leavesToStringWithSep(t as itree(inode(name,_),children), sep ) =
							let
							    fun traverse (itree( inode(name,_)                       , []       ) ) = name
							      | traverse (itree( imatch_var (symbol_type,symbol_id,_), []       ) ) = "<" ^ symbol_type ^ ">" ^ symbol_id
							      |	traverse (itree( inode(name,_)                       , children ) ) = foldr (fn (t, str) => (traverse t) ^ str ) sep children
                                  | traverse t                                   	     			    = (
																											print("\n\n=========================================\n\n");
																											CONCRETE_REPRESENTATION.fullPrintTree " " t;
																											raise General.Fail("Error in CONCRETE.leavesToStringWithSep.traverse.\n")
																										  );
							in
							    traverse t  
							end
  | leavesToStringWithSep (t, sep) = (
                                      print("\n\n=========================================\n\n");
                                      CONCRETE_REPRESENTATION.fullPrintTree " " t;
                                      raise General.Fail("Error in CONCRETE.leavesToStringWithSep.\n")
                                     );
                       
(* ------------------------------------------------------------------------------------------- *)
fun leavesToStringRaw someTerm = leavesToStringWithSep (someTerm, "") 
					   
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun bottom_up f_concrete a_tree =
	let
	    fun traverse ( t as itree( imatch_var _ , [] ) ) = f_concrete t
	      | traverse ( t as itree( inode root   , [] ) ) = f_concrete t

		  |	traverse (itree( some_node, tree_list ) ) = 
				let 
					val new_tree_list = map traverse tree_list
				in
					f_concrete (itree( some_node, new_tree_list ))
				end
								
	in
	    traverse a_tree
	end;
																	
(* ------------------------------------------------------------------------------------------- *)
fun size expr = let
                    val node_count = ref 0;

                    fun inc_concrete_node_count concrete_term = (node_count := !node_count + 1; concrete_term)
                in
                    bottom_up inc_concrete_node_count expr;
                    !node_count
                end;
																	
(* ------------------------------------------------------------------------------------------- *)
fun eqLinearInternalStructure( itree(node1, [] )            , itree(node2, [] )             ) = true
  | eqLinearInternalStructure( itree(inode(x1,_), [child1]) , itree(inode(x2, _), [child2]) ) = (x1 = x2) andalso eqLinearInternalStructure(child1, child2)
  | eqLinearInternalStructure _                                                               = false
																			
fun replaceLeaf( itree(inode(symbol,x_info)  , []     ) , new_symbol ) = itree(inode(new_symbol,x_info), [] )
  | replaceLeaf( itree(inode(internal,x_info), [child]) , new_symbol ) = itree(inode(internal,x_info  ), [ replaceLeaf(child, new_symbol) ] ) 
  | replaceLeaf _                                                      = raise General.Fail("Error in CONCRETE.replaceLeaf: found non-linear or non-ground tree structure.\n")
																					
fun getLeaf(  itree(inode(leaf,_), [])       ) = leaf
  | getLeaf(  itree(inode(_)     , [child])  ) = getLeaf child
  | getLeaf some_tree                               = (
														print("\n+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++ \n");
														printTree " " some_tree;
														raise General.Fail("Error in CONCRETE.getLeaf: found non-linear or non-ground tree structure.\n")
													  )

end; (* struct *)
(* ------------------------------------------------------------------------------------------- *)
(*                                   end CONCRETE_REPRESENTATION                               *)
(* ------------------------------------------------------------------------------------------- *)
 