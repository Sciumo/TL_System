

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
structure CONCRETE_REPRESENTATION =
struct

	(* ------------------------------------------------------------------------------------------- *)
	(*                           Representation Produced by Parser                                 *)
	(* ------------------------------------------------------------------------------------------- *)
	datatype NODE_INFO = info of { id : IntInf.int, line : int * int , column : int * int, label : string };
	datatype NODE = t_node of string * NODE_INFO | schema_var of string * NODE_INFO
	datatype TREE = tree of NODE * TREE list;
												
	exception AmbiguousParse of TREE * TREE			
													
	(* ------------------------------------------------------------------------------------------- *)
	val min_val			= valOf Int.minInt;
	val max_val			= valOf Int.maxInt;
	val default_label   = "";
										
	(* ranges initially reversed since we don't want to keep these values *)
	val init_info    	= info{ id = ~1, line = ( max_val, min_val ), column = (max_val, min_val), label=default_label }
	val default_info 	= info{ id = ~1, line = (0,0)               , column = (0,0)             , label=default_label }
	val dummy_node_info = info{ id = ~1, line = (0,0)               , column = (0,0)             , label=default_label };
	
	val info_ref 	= ref  default_info;
    val id_ref      = ref ~1
    
    fun getInfoId() = 
        (
            id_ref := !id_ref + 1;
            !id_ref
        )
	
	val label_ref 	= ref  default_label;
	fun setLabel( str ) = label_ref := str;
	

	
									
	(* ------------------------------------------------------------------------------------------- *)
	fun makeUniqueIdAttribute      ( info data_record ) = IntInf.toString(#id data_record)
    
	fun makeLineAttribute      ( info data_record ) = 
		let
			val (low_y,high_y) = #line data_record
		in
			Int.toString(low_y) ^ ":" ^ Int.toString(high_y)
		end
	fun makeColumnAttribute    ( info data_record ) = 
		let
			val (low_x,high_x) = #column data_record
		in
			Int.toString(low_x) ^ ":" ^ Int.toString(high_x)
		end

	fun makeLabelAttribute (info data_record ) = #label data_record
	
	(* ------------------------------------------------------------------------------------------- *)
	fun convertToInfo( { line = x, column = y } ) = 
		let
			val int_x = Word.toInt x
			val int_y = Word.toInt y
			val value = info { id = getInfoId(), line = (int_x,int_x), column= (int_y,int_y), label = !label_ref } 
		in
			info_ref := value;
			value
		end
	(* ------------------------------------------------------------------------------------------- *)
	fun getLineLow   ( info data_record ) = 
		let
			val (low_line, high_line) = #line data_record
		in
			low_line 
		end
		
	fun getLineHigh  ( info data_record ) = 
		let
			val (low_line, high_line) = #line data_record
		in
			high_line	
		end
		
	fun getColumnLow ( info data_record ) = 
		let
			val (low_column, high_column) = #column data_record
		in
			low_column
		end
		
	fun getColumnHigh( info data_record) = 
		let
			val (low_column, high_column) = #column data_record
		in
			high_column	
		end
		
	fun getLabel (info data_record ) = #label data_record
	
    fun getCurrentInfo() = !info_ref;
    fun inferCurrentInfo (info first, info last) =
        let
            val low_line = #1 (#line first)
            val low_col = #1 (#column first)
            val high_line = #2 (#line last)
            val high_col = #2 (#column last)
        in
            info { id = getInfoId(), line = (low_line, high_line), column = (low_col, high_col), label = getLabel (getCurrentInfo ()) }
        end
					
	fun getInfo( tree(t_node    (name, node_info), _ ) ) = node_info
      | getInfo( tree(schema_var(name, node_info), _ ) ) = node_info
									
	(* ------------------------------------------------------------------------------------------- *)		
	fun expandRange( tree(t_node(name,node_info), child::children) ) =
		let
			val x_lo = foldr (fn (a_tree,x2) =>  Int.min( getLineLow (getInfo a_tree), x2 )  ) (getLineLow (getInfo child))  children
			val x_hi = foldr (fn (a_tree,x2) =>  Int.max( getLineHigh(getInfo a_tree), x2 )  ) (getLineHigh(getInfo child)) children			

			val y_lo = foldr (fn (a_tree,y2) =>  Int.min( getColumnLow (getInfo a_tree), y2 )  ) (getColumnLow (getInfo child)) children
			val y_hi = foldr (fn (a_tree,y2) =>  Int.max( getColumnHigh(getInfo a_tree), y2 )  ) (getColumnHigh(getInfo child)) children			
			
		in
			tree(t_node(name, info{ id = getInfoId(), line=(x_lo,x_hi),column=(y_lo,y_hi), label= getLabel node_info}), child::children)
		end
	| expandRange t = t;

	(* ------------------------------------------------------------------------------------------- *)							
	fun special_bottom_up f a_tree =
		let
		
		    (* IMPORTANT: epsilon nodes should be ignored *)
			fun traverse (tree( t_node("", _) , []   ) ) = tree(t_node("",init_info), [])		
			  | traverse (tree( some_node, tree_list ) ) = 
				let 
					val new_tree_list = map traverse tree_list
				in
					f (tree( some_node, new_tree_list ))
				end
		in
			traverse a_tree
		end;
	
	(* ------------------------------------------------------------------------------------------- *)							
	fun bottom_up f a_tree =
		let
			fun traverse (tree( some_node, tree_list ) ) = 
				let 
					val new_tree_list = map traverse tree_list
				in
					f (tree( some_node, new_tree_list ))
				end
		in
			traverse a_tree
		end;
										
	(* ------------------------------------------------------------------------------------------- *)			 
	fun adjustInfo full_parse_tree = special_bottom_up expandRange full_parse_tree handle General.Fail( msg ) => ( print(msg); raise General.Fail(msg) )
  
	fun liftSchemaVar( tree(t_node("schema_var",_), [tree(t_node(symbol,x_info), [])] ) ) = tree(schema_var(symbol,x_info), [])
      | liftSchemaVar( tree(any, children) ) = tree( any, map liftSchemaVar children )
											
(* ------------------------------------------------------------------------------------------- *)
(*                   Internal Representation  (used by transformation system)                  *)
(* ------------------------------------------------------------------------------------------- *)
(* Internal Representation of target tree *)

	datatype INODE = inode of string * NODE_INFO
	               | imatch_var of string * string * NODE_INFO;  (* <symbol_type>symbol_id => symbol_type * symbol_id *)
															
	datatype ITREE = itree of INODE * ITREE list;

(* ------------------------------------------------------------------------------------------- *)
	fun ITREE_toDot(file_name, out_stream, itree_term ) = 
		let
			fun escape (#"\"" :: cs) = #"\\" :: #"\"" :: escape cs
			  | escape (c :: cs)     = c :: escape cs
			  | escape []            = []
			val escape = implode o escape o explode
			
			val counter 		= ref 0;
			fun nextStruct()	= (counter := !counter + 1; "struct" ^ Int.toString(!counter))
			
			val header 			= "\ndigraph \"" ^ escape file_name ^ "\"\n{"
			val footer 			= "\n}"

			fun inode_toStruct( the_struct, inode( name, _) ) = "\n" ^ the_struct ^ " [label=" ^ "\"" ^ escape name ^ "\"]"
			
			fun translateITREE "root" ( itree( the_inode, subtrees ) ) = 
					let
						val the_struct_id 	= nextStruct()
						val the_struct_def 	= inode_toStruct( the_struct_id, the_inode )
					in
						TextIO.output(out_stream, header);
						TextIO.output(out_stream, the_struct_def);
						
						map (translateITREE the_struct_id) subtrees;
						
						TextIO.output(out_stream, footer)
					end
					
			  (* epsilon *)		
			  | translateITREE ancestor_struct ( itree(  the_inode, 
			                                             [ itree( inode("", _), [] ) ] 
													  ) 
											    ) = 
					let
						val the_struct_id 	= nextStruct()
						val the_struct_def 	= inode_toStruct( the_struct_id, the_inode )
						val edge			= "\n" ^ ancestor_struct ^ "->" ^ the_struct_id
					in
						TextIO.output(out_stream, the_struct_def);
						TextIO.output(out_stream, edge)
					end
			  | translateITREE ancestor_struct ( itree( the_inode, subtrees ) ) = 
					let
						val the_struct_id 	= nextStruct()
						val the_struct_def 	= inode_toStruct( the_struct_id, the_inode )
						val edge			= "\n" ^ ancestor_struct ^ "->" ^ the_struct_id
					in
						TextIO.output(out_stream, the_struct_def);
						
						map (translateITREE the_struct_id) subtrees;
						
						TextIO.output(out_stream, edge)
					end
			
		in
			translateITREE "root" itree_term
		end
	
(* ------------------------------------------------------------------------------------------- *)
	fun convertToINODE( t_node    (name, x_info ) ) = inode(name, x_info)
	  | convertToINODE( schema_var(name, x_info ) ) = 				
				let
					fun getId( #">" :: xs ) = xs
					  | getId( x    :: xs ) = getId xs
					  | getId []            = raise General.Fail("Error in CONCRETE_REPRESENTATION.convertToINODE.getId.\n");
																
					fun getType( #">" :: xs ) = []
					  | getType( x    :: xs ) = x :: getType xs
					  | getType []            = raise General.Fail("Error in CONCRETE_REPRESENTATION.convertToINODE.getType.\n");
																	
					val symbol_list = tl( explode name ) handle Empty => raise General.Fail("Error in CONCRETE_REPRESENTATION.convertToINODE.tl.\n")
																				
				    val symbol_type = implode( getType( symbol_list ) )
                    val symbol_id   = implode( getId  ( symbol_list ) )
				in
				    imatch_var( symbol_type, symbol_id, x_info)
				end
																						
	fun convertToITREE( tree( node, children ) ) = itree( convertToINODE node, map convertToITREE children)
																	
(* ------------------------------------------------------------------------------------------- *)	
	
	fun makeNodeInfo(x_lo, x_hi, y_lo, y_hi, label_info) = info{ id = getInfoId(), line=(x_lo,x_hi), column=(y_lo,y_hi), label=label_info}

	(* assume label_info1 = label_info2 *)
	fun mergeNodeInfo( info{ id=_, line = (x1_lo, x1_hi), column=(y1_lo,y1_hi), label=label_info1},
					   info{ id=_, line = (x2_lo, x2_hi), column=(y2_lo,y2_hi), label=label_info2}
					 ) = info{ id = getInfoId(), line=(Int.min(x1_lo,x2_lo), Int.max(x1_hi,x2_hi)), column=(Int.min(y1_lo,y2_lo), Int.max(y1_hi,y2_hi)), label=label_info1 }
	
	fun extractNodeInfo ( info{ id, line=(low_x,high_x), column=(low_y, high_y), label=label_info } ) = (id, low_x, high_x, low_y, high_y, label_info)

	fun nodeInfoToString ( x_info ) = 
		let
			val (id, low_x, high_x, low_y, high_y, label_info) = extractNodeInfo( x_info )
            val id   = IntInf.toString(id)
			val x_lo = Int.toString(low_x )
			val x_hi = Int.toString(high_x)
			val y_lo = Int.toString(low_y )
			val y_hi = Int.toString(high_y)			
		in
            "id= (" ^ id ^ ") " ^
			"line= (" ^ x_lo ^ " , " ^ x_hi ^ ") " ^
			"column=(" ^ y_lo ^ " , " ^ y_hi ^ ")" ^
			"label=" ^ label_info
		end

	
	fun printNodeInfo ( x_info ) = 
		let
			val (id, low_x, high_x, low_y, high_y, label_info) = extractNodeInfo( x_info )
            val id   = IntInf.toString(id)
			val x_lo = Int.toString(low_x )
			val x_hi = Int.toString(high_x)
			val y_lo = Int.toString(low_y )
			val y_hi = Int.toString(high_y)			
		in
            print("id= (" ^ id ^ ")\n");
			print("\nline=  (" ^ x_lo ^ " , " ^ x_hi ^ ")\n");
			print("column=(" ^ y_lo ^ " , " ^ y_hi ^ ")\n");
			print("label=" ^ label_info ^ "\n\n")
		end
(* ------------------------------------------------------------------------------------------- *)
val INDENT = "   ";
																					
fun fullPrintNode LM (inode(name, x_info) ) = 
							let 
							    val new_LM = LM ^ INDENT
							in 
                		        print(LM ^ "inode");
							    print(new_LM ^ name)
							end
																	
  | fullPrintNode LM (imatch_var(symbol_type, symbol_id, x_info) ) = 
							let 
							    val new_LM = LM ^ INDENT
							in 
                		        print(LM ^ "imatch_var");
							    print(new_LM ^ "<" ^ symbol_type ^ ">" ^ symbol_id)
							end
																				
fun fullPrintTree LM (itree( name_and_info, tree_list ) ) = 
							let 
							      val new_LM = LM ^ INDENT
                                  val new_LM2 = new_LM ^ INDENT
						    in 
																	
							      fullPrintNode new_LM name_and_info;
																						
 							      map (fullPrintTree new_LM2) tree_list;
                                  ()
						    end
																
(* ------------------------------------------------------------------------------------------- *)
end;
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
