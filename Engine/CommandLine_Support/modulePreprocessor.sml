
(* =========================================================================================================================== *)
structure modulePreprocessor = struct
open CONCRETE_REPRESENTATION

(* =========================================================================================================================== *)	
datatype VISIBILITY = OPENED | CLOSED;
datatype MODULE_INFO = module_info of { moduleId : string,  visibility : VISIBILITY };


val TL_input_folder 	= ref "";
val TL_output_folder 	= ref "";

val DEBUG = true;

fun setTL_input_folder( x  ) = TL_input_folder  := x;
fun setTL_output_folder( x ) = TL_output_folder := x;
  
(* --------------------------------------------------------------------------------------------------------------------------- *)  
val importStack      = ref ([] : MODULE_INFO list);
fun pop()            = importStack := tl(!importStack)
fun initStack( mId ) = importStack := module_info { moduleId = mId, visibility = OPENED } :: []

fun pushUnique( m as module_info{moduleId = mId,...} ) = 
    if List.exists (fn (module_info({moduleId,...})) => mId = moduleId) (!importStack) then raise General.Fail("Error: cycle in imports involving " ^ mId)
    else importStack := m :: !importStack 


(* =========================================================================================================================== *)	
fun BUL_traversal f (term as tree( the_node, children ) ) = 
	let
		val new_children = map (BUL_traversal f) children
	in
		f ( tree( the_node, new_children ) )
	end
	
(* --------------------------------------------------------------------------------------------------------------------------- *)  		
fun getRawLeaf( tree( t_node(x,_), []  ) ) = x
  | getRawLeaf( tree( _          , xs ) )  = foldr (op ^) "" (map getRawLeaf xs)
  
(* --------------------------------------------------------------------------------------------------------------------------- *)  		
fun countSymbol( term, symbol) =
	let
		val counter = ref 0;
		val f = fn ( t as tree(t_node(x, y), children) ) => (
																if x = symbol then counter := !counter + 1 else (); 
																t
															)
				 | t => t
	in
	    BUL_traversal f term;
		!counter
	end
	
(* --------------------------------------------------------------------------------------------------------------------------- *)  	
fun printSymbol( term, symbol ) =
	let
		fun f( t as tree(t_node(x, y), [ value ] ) ) = (
															if x = symbol then print(getRawLeaf(value) ^ "\n") else (); 
															t
													   )
		  | f t = t
	in
		    BUL_traversal f term
	end
	
(* =========================================================================================================================== *)	
fun get_decl_list( (visibility, tree( t_node("t_program", x_node_info), [decl_list_term] )) ) = (visibility, decl_list_term)
  | get_decl_list _                                                                           = (print("Error in modulePreprocessor.get_decl_list\n"); 
                                                                                                 raise General.Fail("Error in modulePreprocessor.get_decl_list\n"))

(* --------------------------------------------------------------------------------------------------------------------------- *)
fun specialTDL mId term =
	let
		(* -------------------------------------------------------------- *)
		fun aux (tree(t_node("name", x_info1),
						[
							tree( t_node("id", x_info2),
									[
										tree(t_node(x, x_info3), [])
									]
								)
						]
					)
                ) 
				= 
				(	
					if DEBUG then print("Strategy declaration: " ^ x ^ " ==> " ^ mId ^ "." ^ x ^ "\n") else ();
 			
					tree(t_node("name", x_info1),
						[
							tree( t_node("id", x_info2),
									[
										tree(t_node(mId ^ "." ^ x, x_info3), [])
									]
								)
						]
					)
				)					

		(* -------------------------------------------------------------- *)
		(* Binding: E.g., s := expr *)
		  | aux (tree(t_node("expr", x_info1),
						[
							tree( t_node("id", x_info2),
									[
										tree(t_node(x, x_info3), [])
									]
								),
							tree( t_node(":=", x_info4), [] ),
							x_expr
						]
					)
                ) 
				= 
				let
					val new_x_expr = aux x_expr
				in
					if DEBUG then print("Binding: " ^ x ^ " ==> " ^ mId ^ "." ^ x ^ "\n") else ();
 			
					tree(t_node("expr", x_info1),
						[
							tree( t_node("id", x_info2),
									[
										tree(t_node(mId ^ "." ^ x, x_info3), [])
									]
								),
							tree( t_node(":=", x_info4), [] ),
							new_x_expr
						]
					)	
				end
		(* -------------------------------------------------------------- *)
		  | aux (tree(t_node("arg", x_info1),
						[
							tree( t_node("id", x_info2),
									[
										tree(t_node(x, x_info3), [])
									]
								)
						]
					)
                ) 
				= 
				(	
					if DEBUG then print(x ^ " ==> " ^ mId ^ "." ^ x ^ "\n") else ();
				
					tree(t_node("arg", x_info1),
						[
							tree( t_node("id", x_info2),
									[
										tree(t_node(mId ^ "." ^ x, x_info3), [])
									]
								)
						]
					)
				)
		(* -------------------------------------------------------------- *)
		  | aux (tree(t_node("qualified_id", x_info1),
						[
							tree( t_node("id", x_info2),
									[
										tree(t_node(x, x_info3), [])
									]
								)
						]
					)
                ) 
				= 
				(	
					if DEBUG then print("Base - qualified_id: "  ^ x ^ " ==> " ^ mId ^ "." ^ x ^ "\n") else ();
				
					tree(t_node("qualified_id", x_info1),
						[
							tree( t_node("id", x_info2),
									[
										tree(t_node(mId ^ "." ^ x, x_info3), [])
									]
								)
						]
					)
				)
				
		(* -------------------------------------------------------------- *)
		  | aux (tree(t_node("qualified_id", x_info1),
						[
							tree( t_node("id", x_info2),
									[
										tree(t_node(x, x_info3), [])
									]
								)
							,
							dot_term
							,
							qualified_id_term
						]
					)
                ) 
				= 
				(	
					if DEBUG then print("General - qualified_id "  ^ x ^ " ==> " ^ mId ^ "." ^ x ^ "\n") else ();
				
					tree(t_node("qualified_id", x_info1),
						[
							tree( t_node("id", x_info2),
									[
										tree(t_node(mId ^ "." ^ x, x_info3), [])
									]
								)
							,
							dot_term
							,
							qualified_id_term
						]
					)
				)
		(* -------------------------------------------------------------- *)
		(* do NOT descend into target language terms *)
		  | aux (t as tree( t_node("parse_expr", _), _ ) )  = t
					
		(* -------------------------------------------------------------- *)
		  | aux (tree( node, children )) = tree(node, map aux children)
		(* -------------------------------------------------------------- *)
	in
		aux term
	end
(* --------------------------------------------------------------------------------------------------------------------------- *)
fun merge_decl_lists(source_term, term_entry ::decl_terms_list) =
	let
		fun slashToDot str =
			let
				fun aux( #"/" ) = #"."
				  | aux( x    ) = x;
			in
				String.map aux str
			end
		fun processVisibility( module_info({moduleId = mId, visibility=OPENED}), term ) = term
		  | processVisibility( module_info({moduleId = mId, visibility=CLOSED}), term ) = specialTDL (slashToDot mId) term
		
		
		fun f( tree( t_node("decl_list", x), [tree(t_node("",_),[])] ) ) = let
																				val replacement_term = merge_decl_lists( processVisibility term_entry, decl_terms_list )
																		   in
																			    replacement_term
																		   end
																					 
		  | f( some_tree                                               ) = some_tree
	in
		BUL_traversal f source_term 
	end
  | merge_decl_lists(source_term, [] ) = source_term
  
(* --------------------------------------------------------------------------------------------------------------------------- *)
fun translateImports(term) =
	let
		val translatedImports = ref ([] : MODULE_INFO list);
				
		fun dotToSlash str =
			let
				fun aux( #"." ) = #"/"
				  | aux( x    ) = x;
			in
				String.map aux str
			end
		  
		
		fun f( t as tree( t_node("importDef", _),
							[
								tree(t_node("import_opened",_), []),
								moduleId
							]
					    )
			 ) = let
					val mId = dotToSlash( getRawLeaf moduleId )
			     in
					translatedImports := module_info( {moduleId = mId, visibility = OPENED} ) :: !translatedImports;
					t
				 end
				 
		  | f( t as tree( t_node("importDef", _),
							[
								tree(t_node("import_closed",_), []),
								moduleId
							]
					    )
			 ) = let
					val mId = dotToSlash( getRawLeaf moduleId )
			     in
					translatedImports := module_info( {moduleId = mId, visibility = CLOSED} ) :: !translatedImports;
					t
				 end
				 
		  | f t = t
	in
		BUL_traversal f term;
		!translatedImports
	end
(* =========================================================================================================================== *)	
(* The issues here is that we want to prevent cycles and duplications. 
    1. To prevent duplications we need to check the import list -- removing all duplications. We consider a duplication
       as an identity, so adding duplicates does not change the functionality, it is just an efficiency issue. We disallow,
       the case where a duplicate pair has different visibility (e.g., opened and closed).
       
    2. cycles are prevented by expanding in a depth-first fashion and keeping track of the path using a global stack.
*)
fun createModuleList(parse, importListTerm) =
	let
        (* ------------------------------------------------------------------------------- *)
        fun checkForDuplicates (module_info({moduleId = mId, visibility = flag}) :: rest, acc) = 
                if List.exists (fn x => x = mId) acc then raise General.Fail("Error: Duplicated import = " ^ mId)
                else checkForDuplicates( rest, mId :: acc )  
                
          | checkForDuplicates ( [], acc ) = false
          
        (* ------------------------------------------------------------------------------- *)  
		fun includeInDepthFirstFashion ( (m as module_info( {moduleId = mId, visibility = flag} )) :: rest ) =
			let
				val mInputFile  = OS.Path.concat (!TL_input_folder, OS.Path.joinBaseExt {base = mId, ext = SOME "tlp"})
				val mOutputFile = OS.Path.concat (!TL_output_folder, mId)
                
                val _             = pushUnique m
                val theModule     = auxProcess( parse, parse( mId, mInputFile, mOutputFile ) )
                val _             = pop()
			in
				( m, theModule ) :: includeInDepthFirstFashion rest
			end
          | includeInDepthFirstFashion [] = []
        
        (* ------------------------------------------------------------------------------- *)
        val translatedImports = translateImports importListTerm            
		val _                 = checkForDuplicates( translatedImports, [] ) 
	in
		includeInDepthFirstFashion translatedImports
	end
    
(* =========================================================================================================================== *)	
and auxProcess	( parse, tree( t_node("TL_Unit",_), 
							[
                                derivedForm_list
                                ,
								import_list as tree( t_node("importDef_list", _), [tree( t_node("",_), [])] ) 
								,
								tree( t_node("moduleDef_list", _ ),
											[
												tree(t_node("moduleDef", _),
															[
																tree(t_node("module", x_node_info),_),
																x_id,
																type_setting,
																decl_list,
																x_end
															]
													)
												,
												x_moduleDef_list
											]
									)
							]
				  )
			) 
			=
			let
                val (_,newDeclList) = DerivedForms.process derivedForm_list import_list decl_list
            in
				(* base case *)
				tree( t_node("t_program", x_node_info),
								[
									newDeclList
								]
					)
			end
            
(* --------------------------------------------------------------------------------------------------------------------------- *)
  | auxProcess	( parse, tree( t_node("TL_Unit",_), 
							[
                                derivedForm_list
                                ,
								import_list
								,
								tree( t_node("moduleDef_list", _ ),
											[
												tree(t_node("moduleDef", _),
															[
																tree(t_node("module", x_node_info),_),
																x_id,
																type_setting,
																this_decl_list,
																x_end
															]
													)
												,
												x_moduleDef_list
											]
									)
							]
				  )
			) 
			= 
			let
                val (newImportList,newDeclList) = DerivedForms.process derivedForm_list import_list this_decl_list
                
				val module_list 			    = createModuleList(parse, newImportList)
				val m_decl_list_term_list       = map get_decl_list module_list
				val merged_list   		        = merge_decl_lists( newDeclList, m_decl_list_term_list ) 
				
			in
			    tree( t_node("t_program", x_node_info),
							[
								merged_list
							]
			      )
			end

(* --------------------------------------------------------------------------------------------------------------------------- *)			
  |	auxProcess _ = (print("Error in modulePreprocessor.auxProcess\n"); 
			  	    raise General.Fail("Error in modulePreprocessor..process\n"))
  
(* =========================================================================================================================== *)
fun transmitPV( p, v ) = (
							print("(precision, verbosity) = (" ^ Int.toString p ^ "," ^ Int.toString v ^ ")\n");
							(p,v)
                         )
						 
(* --------------------------------------------------------------------------------------------------------------------------- *)									 
fun setPrecisionAndVerbosity( tree( t_node("typeSetting",_), 
									[
										lparen,
										precisionKeyword,
										x_equal1,
										precisionInt,
										comma,
										verbosityKeyword,
										x_equal2,
										verbosityInt,
										rparen
									] 
								  ) 
							) = let 
									val p = valOf( Int.fromString( getRawLeaf precisionInt ) )
									val v = valOf( Int.fromString( getRawLeaf verbosityInt ) )
								in
									transmitPV( p, v )
								end
  | setPrecisionAndVerbosity( tree( t_node("typeSetting",_), _ ) ) = transmitPV( 0, 0 )								

(* =========================================================================================================================== *)	
  
fun process	( parse, tree( t_node("TL_Unit",_), 
							[
                                derivedForm_list
                                ,
								import_list as tree( t_node("importDef_list", _), [tree( t_node("",_), [])] ) 
								,
								tree( t_node("moduleDef_list", _ ),
											[
												tree(t_node("moduleDef", _),
															[
																tree(t_node("module", x_node_info),_),
																x_id,
																type_setting,
																decl_list,
																x_end
															]
													)
												,
												x_moduleDef_list
											]
									)
							]
				  )
			) 
			=
            let
                val (_,newDeclList) = DerivedForms.process derivedForm_list import_list decl_list
            in
                (* base case *)			
                (
                    setPrecisionAndVerbosity( type_setting),
                    tree( t_node("t_program", x_node_info),
                                    [
                                        newDeclList
                                    ]
                        )
                )
			end

(* --------------------------------------------------------------------------------------------------------------------------- *)
  | process	( parse, tree( t_node("TL_Unit",_), 
						[
                                derivedForm_list
                                ,
								import_list
								,
								tree( t_node("moduleDef_list", _ ),
											[
												tree(t_node("moduleDef", _),
															[
																tree(t_node("module", x_node_info),_),
                                                                tree( t_node("id", _), [ tree(t_node(mId, _), [])	]),
																type_setting,
																this_decl_list,
																x_end
															]
													)
												,
												x_moduleDef_list
											]
									)
							]
				  )
			) 
			= 
			let
                val (newImportList,newDeclList) = DerivedForms.process derivedForm_list import_list this_decl_list
                
                val _                      = initStack( mId )         
				val module_list 		   = createModuleList(parse, newImportList)
				val m_decl_list_term_list  = map get_decl_list module_list
				val merged_list   		   = merge_decl_lists( newDeclList, m_decl_list_term_list ) 
			in
				(
					setPrecisionAndVerbosity( type_setting),
				    tree( t_node("t_program", x_node_info),
							[
								merged_list
							]
						)
				)
			end

(* --------------------------------------------------------------------------------------------------------------------------- *)			
  |	process _ = (print("Error in modulePreprocessor.process\n"); 
				 raise General.Fail("Error in modulePreprocessor..process\n"))

  
(* =========================================================================================================================== *)  
end; (* struct *)
(* =========================================================================================================================== *)
