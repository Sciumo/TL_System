
(* ------------------------------------------------------------------------------------------- *)
signature ABSTRACT_SIG =
sig
	(* Generic Traversal *)
    val bottom_up: (ABSTRACT_REPRESENTATION.EXPR -> ABSTRACT_REPRESENTATION.EXPR) -> 
                   (CONCRETE_REPRESENTATION.ITREE -> CONCRETE_REPRESENTATION.ITREE) ->
				   ABSTRACT_REPRESENTATION.EXPR  -> ABSTRACT_REPRESENTATION.EXPR
								
	(* Input and Translation *)
    val EXPR_FromXML_TREE_FORMAT  	: string -> ABSTRACT_REPRESENTATION.EXPR  
	val fromConcrete 				: CONCRETE_REPRESENTATION.TREE -> ABSTRACT_REPRESENTATION.EXPR
									
    (* Output: XML file representation only *)
    val EXPR_toXML		   			: string * string * ABSTRACT_REPRESENTATION.EXPR -> unit
 							
	(* Support *)
    val printTree    	: ABSTRACT_REPRESENTATION.EXPR -> unit
	val getExprInfo     : ABSTRACT_REPRESENTATION.EXPR -> CONCRETE_REPRESENTATION.NODE_INFO
	val leavesToString 	: ABSTRACT_REPRESENTATION.EXPR -> bool -> string
							
    (* Metrics *)
    val size: ABSTRACT_REPRESENTATION.EXPR -> int
																		
    (* Used to construct initial application *)
	val getMain                   : ABSTRACT_REPRESENTATION.EXPR  										-> ABSTRACT_REPRESENTATION.EXPR
    val makeTerm                  : CONCRETE_REPRESENTATION.ITREE * CONCRETE_REPRESENTATION.NODE_INFO	-> ABSTRACT_REPRESENTATION.EXPR
    val unmakeTerm                : ABSTRACT_REPRESENTATION.EXPR  										-> CONCRETE_REPRESENTATION.ITREE
    val makeRef                   : string * string  * int option * CONCRETE_REPRESENTATION.NODE_INFO 	-> ABSTRACT_REPRESENTATION.EXPR 
    val getRefIndex               : ABSTRACT_REPRESENTATION.EXPR  										-> int
    val isPredefinedIterator : string                        										-> bool
end;
(* ------------------------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------------------------- *)
structure ABSTRACT : ABSTRACT_SIG =
struct

open CONCRETE_REPRESENTATION;
open ABSTRACT_REPRESENTATION;

(* ------------------------------------------------------------------------------------------- *)
fun bottom_up f_abstract f_concrete expr =
    let
	fun traverse (PROG (decl_list, x_info)) = 
						let
						    val new_decl_list = map traverse decl_list
				       	in
						    f_abstract (PROG (new_decl_list, x_info))    
				       	end
						
	  | traverse (SIGNATURE     (expr, x_info) ) = 
						let
						    val new_expr = traverse expr
				       	in
						    f_abstract (SIGNATURE( new_expr, x_info ) )    
				       	end
																		
	  | traverse (RECURSIVE     (id, arg_list, expr, x_info) ) = 
						let
                            val new_id       = traverse id
						    val new_arg_list = map traverse arg_list
                            val new_expr     = traverse expr
				       	in
						    f_abstract (RECURSIVE( new_id, new_arg_list, new_expr, x_info ) )    
				       	end
															
	  | traverse (NON_RECURSIVE (id, expr, x_info) )          = 
						let
                            val new_id      = traverse id
                            val new_expr    = traverse expr
				       	in
						    f_abstract (NON_RECURSIVE( new_id, new_expr, x_info ) )    
				       	end
													
      | traverse (ANDALSO (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				       	in
						    f_abstract (ANDALSO( new_expr1, new_expr2, x_info ) )    
				       	end
																					
	  | traverse (ORELSE (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (ORELSE( new_expr1, new_expr2, x_info ) )    
				        end
																
	  | traverse (MATCH (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (MATCH( new_expr1, new_expr2, x_info ) )    
				        end
																					
	  | traverse (BIND (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				       	in
						    f_abstract (BIND( new_expr1, new_expr2, x_info ) )    
				       	end
																			
	  | traverse (CHOICE (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				       	in
						    f_abstract (CHOICE( new_expr1, new_expr2, x_info ) )    
				       	end
																				
	  | traverse (LCHOICE (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				       	in
						    f_abstract (LCHOICE( new_expr1, new_expr2, x_info ) )    
				       	end
														
	  | traverse (RCHOICE (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (RCHOICE( new_expr1, new_expr2, x_info ) )    
				        end
																		
	  | traverse (LSEQ (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (LSEQ( new_expr1, new_expr2, x_info ) )    
				        end
																		
	  | traverse (RSEQ (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (RSEQ( new_expr1, new_expr2, x_info ) )    
				        end
																			
	  | traverse (LSTAR (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (LSTAR( new_expr1, new_expr2, x_info ) )    
				        end
																	
	  | traverse (RSTAR (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (RSTAR( new_expr1, new_expr2, x_info ) )    
				        end
														
	  | traverse (RULE (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (RULE( new_expr1, new_expr2, x_info ) )    
				        end
															
	  | traverse (COND_RULE (expr1,expr2,expr3, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
						    val new_expr3 = traverse expr3
				        in
						    f_abstract (COND_RULE( new_expr1, new_expr2, new_expr3, x_info ) )    
				        end
													
	  | traverse (B_OR (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (B_OR( new_expr1, new_expr2, x_info ) )    
				        end
											
	  | traverse (B_AND (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (B_AND( new_expr1, new_expr2, x_info ) )    
				        end
																	
	  | traverse (EQ (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (EQ( new_expr1, new_expr2, x_info ) )    
				        end
															
	  | traverse (NEQ (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (NEQ( new_expr1, new_expr2, x_info ) )    
				        end
														
	  | traverse (LEQ (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (LEQ( new_expr1, new_expr2, x_info ) )    
				        end
															
	  | traverse (LT (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (LT( new_expr1, new_expr2, x_info ) )    
				        end
																		
	  | traverse (GEQ (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (GEQ( new_expr1, new_expr2, x_info ) )    
				        end
															
	  | traverse (GT (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (GT( new_expr1, new_expr2, x_info ) )    
				        end
																
	  | traverse (CONCAT (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (CONCAT( new_expr1, new_expr2, x_info ) )    
				        end
																
	  | traverse (PLUS (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (PLUS( new_expr1, new_expr2, x_info ) )    
				        end
																			
	  | traverse (MINUS (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (MINUS( new_expr1, new_expr2, x_info ) )    
				        end
										
	  | traverse (TIMES (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (TIMES( new_expr1, new_expr2, x_info ) )    
				        end
													
	  | traverse (DIVIDE (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (DIVIDE( new_expr1, new_expr2, x_info ) )    
				        end
																			
	  | traverse (DIV (expr1,expr2, x_info)) = 												
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (DIV( new_expr1, new_expr2, x_info ) )    
				        end
																
	  | traverse (MOD (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (MOD( new_expr1, new_expr2, x_info ) )    
				        end
												
	  | traverse (APP (expr1,expr2, x_info)) = 
						let
						    val new_expr1 = traverse expr1
						    val new_expr2 = traverse expr2
				        in
						    f_abstract (APP( new_expr1, new_expr2, x_info ) )    
				        end
												
	  | traverse (ITERATOR (id, arg_list, x_info) ) = 
						let
                            val new_id       = traverse id
						    val new_arg_list = map traverse arg_list
				        in
						    f_abstract (ITERATOR( new_id, new_arg_list, x_info ) )    
				        end
													
	  | traverse (BOOL       (value, x_info)  		) = f_abstract (BOOL   		(value, x_info) 		)
	  | traverse (INT        (value, x_info)  		) = f_abstract (INT    		(value, x_info) 		)
	  | traverse (REAL       (value, x_info)  		) = f_abstract (REAL   		(value, x_info)			)
	  | traverse (STRING     (value, x_info)  		) = f_abstract (STRING 		(value, x_info) 		)
	  | traverse (IDENTIFIER (x, x_info)  		  	) = f_abstract (IDENTIFIER 	(x	  , x_info) 		)
	  | traverse (REF        (x, ref_info, x_info)	) = f_abstract (REF        	(x, ref_info, x_info) 	)
                                   
	  | traverse (TERM (a_tree, x_info) )  = 
						let
						    val new_tree = CONCRETE.bottom_up f_concrete a_tree
				        in
						    f_abstract (TERM (new_tree, x_info) )    
				        end
                                      
	  | traverse (LIBRARY_CALL_0 (id, x_info)) = 
						let
						    val new_id = traverse id
				        	in
						    f_abstract (LIBRARY_CALL_0( new_id, x_info ) )    
				        	end
												
	  | traverse (LIBRARY_CALL (id,expr_list, x_info)) = 
						let
						    val new_id        = traverse id
						    val new_expr_list = map traverse expr_list
				        	in
						    f_abstract (LIBRARY_CALL( new_id, new_expr_list, x_info ) )    
				        	end
																
	  | traverse (ID(x_info))          = f_abstract (ID(x_info)) 
	  | traverse (SKIP(x_info))        = f_abstract (SKIP(x_info))
	  | traverse (FAIL(x_info))        = f_abstract (FAIL(x_info))
                                      
	  | traverse (NOT (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
				               f_abstract (NOT (new_expr, x_info))    
				        end
														
	  | traverse (BANG (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (BANG (new_expr, x_info))    
				        end
                                          
	  | traverse (TILDE (expr, x_info))        = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (TILDE (new_expr, x_info))    
				        end
                                        
	  | traverse (TRANSIENT (expr, x_info))    = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (TRANSIENT (new_expr, x_info))    
				        end
												
	  | traverse (OPAQUE (expr, x_info))       = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (OPAQUE (new_expr, x_info))    
				        end
                                              
	  | traverse (RAISE (expr, x_info))        = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (RAISE (new_expr, x_info))    
				        end
                                              
	  | traverse (HIDE (expr, x_info))         = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (HIDE (new_expr, x_info))    
				        end
																
	  | traverse (LIFT (expr, x_info))         = 
						let
					       val new_expr = traverse expr
		        	    in 
					       f_abstract (LIFT (new_expr, x_info))    
				        end
                                          
	  | traverse (MAPL (expr, x_info))         = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (MAPL (new_expr, x_info))    
				        end
															
	  | traverse (MAPR (expr, x_info))         = 
						let
					       val new_expr = traverse expr
		        	    in
   					       f_abstract (MAPR (new_expr, x_info))    
   				        end
														
	  | traverse (MAPB (expr, x_info))         = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (MAPB (new_expr, x_info))    
				        end
												
      | traverse (FOLD_CHOICE  (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLD_CHOICE (new_expr, x_info))    
				        end
														
      | traverse (FOLD_LCHOICE (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLD_LCHOICE (new_expr, x_info))    
				        end
																	
      | traverse (FOLD_RCHOICE (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLD_RCHOICE (new_expr, x_info))    
				        end
																	
      | traverse (FOLD_LSEQ    (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLD_LSEQ (new_expr, x_info))    
				        end
															
      | traverse (FOLD_RSEQ    (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLD_RSEQ (new_expr, x_info))    
				        end
																
      | traverse (FOLD_LSTAR   (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLD_LSTAR (new_expr, x_info))    
				        end
																			
      | traverse (FOLD_RSTAR   (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLD_RSTAR (new_expr, x_info))    
				        end
																
      | traverse (FOLDS_CHOICE  (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					        f_abstract (FOLDS_CHOICE (new_expr, x_info))    
				        end
																
      | traverse (FOLDS_LCHOICE (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLDS_LCHOICE (new_expr, x_info))    
				        end
															
      | traverse (FOLDS_RCHOICE (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLDS_RCHOICE (new_expr, x_info))    
				        end
																		
      | traverse (FOLDS_LSEQ    (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLDS_LSEQ (new_expr, x_info))    
				        end
																			
      | traverse (FOLDS_RSEQ    (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLDS_RSEQ (new_expr, x_info))    
				        end
														
      | traverse (FOLDS_LSTAR   (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLDS_LSTAR (new_expr, x_info))    
				        end
													
      | traverse (FOLDS_RSTAR   (expr, x_info)) = 
						let
					       val new_expr = traverse expr
		        	    in
					       f_abstract (FOLDS_RSTAR (new_expr, x_info))    
				        end
															
	  | traverse UNIT		  = raise General.Fail("Error in ABSTRACT.bottom_up.traverse: encountered UNIT value.\n")
													
    in
        traverse expr
    end;
														
(* ------------------------------------------------------------------------------------------- *)
fun isPredefinedIterator( "FIX"    ) = true
  | isPredefinedIterator( "TdlBul" ) = true
  | isPredefinedIterator( "TDL"    ) = true
  | isPredefinedIterator( "TDR"    ) = true
  | isPredefinedIterator( "TD"     ) = true
  | isPredefinedIterator( "BUL"    ) = true
  | isPredefinedIterator( "BUR"    ) = true
                                                                                
  | isPredefinedIterator( "cond_tdl" ) = true
  | isPredefinedIterator( "cond_tdr" ) = true
  | isPredefinedIterator( "cond_tdb" ) = true
  | isPredefinedIterator( "cond_bul" ) = true
  | isPredefinedIterator( "cond_bur" ) = true
                                                                                
  | isPredefinedIterator( "lcond_tdl" ) = true
  | isPredefinedIterator( "lcond_tdr" ) = true
  | isPredefinedIterator( "lcond_tdb" ) = true
  | isPredefinedIterator( "lseq_tdl"  ) = true
  | isPredefinedIterator( "lseq_tdr"  ) = true
  | isPredefinedIterator( "lseq_tdb"  ) = true
  | isPredefinedIterator( "lstar_tdl" ) = true
  | isPredefinedIterator( "lstar_tdr" ) = true
  | isPredefinedIterator( "lstar_tdb" ) = true
  | isPredefinedIterator( "lcond_bul" ) = true
  | isPredefinedIterator( "lcond_bur" ) = true
  | isPredefinedIterator( "lseq_bul"  ) = true
  | isPredefinedIterator( "lseq_bur"  ) = true
  | isPredefinedIterator( "lstar_bul" ) = true
  | isPredefinedIterator( "lstar_bur" ) = true
                                                                                                      
  | isPredefinedIterator( "rcond_tdl" ) = true
  | isPredefinedIterator( "rcond_tdr" ) = true
  | isPredefinedIterator( "rcond_tdb" ) = true
  | isPredefinedIterator( "rseq_tdl"  ) = true
  | isPredefinedIterator( "rseq_tdr"  ) = true
  | isPredefinedIterator( "rseq_tdb"  ) = true
  | isPredefinedIterator( "rstar_tdl" ) = true
  | isPredefinedIterator( "rstar_tdr" ) = true
  | isPredefinedIterator( "rstar_tdb" ) = true
  | isPredefinedIterator( "rcond_bul" ) = true
  | isPredefinedIterator( "rcond_bur" ) = true
  | isPredefinedIterator( "rseq_bul"  ) = true
  | isPredefinedIterator( "rseq_bur"  ) = true
  | isPredefinedIterator( "rstar_bul" ) = true
  | isPredefinedIterator( "rstar_bur" ) = true
                                                                                     
  | isPredefinedIterator _ = false

(* ------------------------------------------------------------------------------------------- *)
fun nameToIdentifier name x_info = 
											
	case name of
														
            "ID"        => ID( x_info )
          | "SKIP"      => SKIP( x_info )
          | "FAIL"      => FAIL( x_info )
          

          | "not"       => IDENTIFIER ("not", x_info)
          | "!"         => IDENTIFIER ("!"  , x_info)
          | "~"         => IDENTIFIER ("~"  , x_info)

          | "transient" => IDENTIFIER ("transient", x_info)
          | "opaque"    => IDENTIFIER ("opaque"   , x_info)
          | "raise"     => IDENTIFIER ("raise"    , x_info)
          | "hide"      => IDENTIFIER ("hide"     , x_info)
          | "lift"      => IDENTIFIER ("lift"     , x_info)
          | "mapL"      => IDENTIFIER ("mapL"     , x_info)
          | "mapR"      => IDENTIFIER ("mapR"     , x_info)
          | "mapB"      => IDENTIFIER ("mapB"     , x_info)

          | "FIX"       => IDENTIFIER ("FIX", x_info)

          | "TdlBul"    => IDENTIFIER ("TdlBul", x_info)
          | "TDL"       => IDENTIFIER ("TDL"   , x_info)
          | "TDR"       => IDENTIFIER ("TDR"   , x_info)
          | "BUL"       => IDENTIFIER ("BUL"   , x_info)
          | "BUR"       => IDENTIFIER ("BUR"   , x_info)
          | "TD"        => IDENTIFIER ("TD"    , x_info)

          | "lseq_tdb"  => IDENTIFIER ("lseq_tdb" , x_info)
          | "rseq_tdb"  => IDENTIFIER ("rseq_tdb" , x_info)
          | "cond_tdb"  => IDENTIFIER ("cond_tdb" , x_info)
          | "lcond_tdb" => IDENTIFIER ("lcond_tdb", x_info)
          | "rcond_tdb" => IDENTIFIER ("rcond_tdb", x_info)
          | "lstar_tdb" => IDENTIFIER ("lstar_tdb", x_info)
          | "rstar_tdb" => IDENTIFIER ("rstar_tdb", x_info)

          | "lseq_tdl"  => IDENTIFIER ("lseq_tdl" , x_info)
          | "rseq_tdl"  => IDENTIFIER ("rseq_tdl" , x_info)
          | "lseq_bul"  => IDENTIFIER ("lseq_bul" , x_info)
          | "rseq_bul"  => IDENTIFIER ("rseq_bul" , x_info)
          | "cond_tdl"  => IDENTIFIER ("cond_tdl" , x_info)
          | "lcond_tdl" => IDENTIFIER ("lcond_tdl", x_info)
          | "rcond_tdl" => IDENTIFIER ("rcond_tdl", x_info)
          | "lcond_bul" => IDENTIFIER ("lcond_bul", x_info)
          | "rcond_bul" => IDENTIFIER ("rcond_bul", x_info)
          | "lstar_tdl" => IDENTIFIER ("lstar_tdl", x_info)
          | "rstar_tdl" => IDENTIFIER ("rstar_tdl", x_info)
          | "lstar_bul" => IDENTIFIER ("lstar_bul", x_info)
          | "rstar_bul" => IDENTIFIER ("rstar_bul", x_info)

          | "lseq_tdr"  => IDENTIFIER ("lseq_tdr" , x_info)
          | "rseq_tdr"  => IDENTIFIER ("rseq_tdr" , x_info)
          | "lseq_bur"  => IDENTIFIER ("lseq_bur" , x_info)
          | "rseq_bur"  => IDENTIFIER ("rseq_bur" , x_info)
          | "cond_tdr"  => IDENTIFIER ("cond_tdr" , x_info)
          | "lcond_tdr" => IDENTIFIER ("lcond_tdr", x_info)
          | "rcond_tdr" => IDENTIFIER ("rcond_tdr", x_info)
          | "lcond_bur" => IDENTIFIER ("lcond_bur", x_info)
          | "rcond_bur" => IDENTIFIER ("rcond_bur", x_info)
          | "lstar_tdr" => IDENTIFIER ("lstar_tdr", x_info)
          | "rstar_tdr" => IDENTIFIER ("rstar_tdr", x_info)
          | "lstar_bur" => IDENTIFIER ("lstar_bur", x_info)
          | "rstar_bur" => IDENTIFIER ("rstar_bur", x_info)
 
          | _           => raise General.Fail("Error in ABSTRACT.nameToIdentifier: unknown name = " ^ name ^ "\n");


(* ------------------------------------------------------------------------------------------- *)

fun

(* ================================================== *)
(*       UserDefinedFunction Signature Declaration    *)
(* ================================================== *)
    fromConcrete( tree(t_node("decl", x_info1),        
                       [ tree(t_node("UserDefinedFunctions",x_info2),[]),
                         tree(t_node("=",x_info3),[]),
                         tree(t_node("sig",x_info4),[]),
						 x_signature_list,
                         tree(t_node("end",x_info6),[])
                       ]              
                     ) 
              ) = let
						val converted_signature_list = fromConcrete x_signature_list
                  in
                     SIGNATURE( converted_signature_list, x_info1  ) 
                  end
				  
  | fromConcrete( tree(t_node("signature_list", x_info1),        
                       [ 
							x_signature,
							x_signature_list
                       ]              
                     ) 
              ) = let
					fun auxFirst( any_expr, LIST (expr_list, _ ) ) = LIST( any_expr :: expr_list, x_info1 )
					  | auxFirst( t1, t2)                          = (
																		print("Error in ABSTRACT.fromConcrete: signature_list.auxFirst.\n");
																		raise General.Fail("Error in ABSTRACT.fromConcrete: signature_list.\n")
																	 ) 
					  
					val expr		= fromConcrete x_signature
					val expr_list	= fromConcrete x_signature_list
                  in
					auxFirst (expr, expr_list )
                  end
			
  | fromConcrete( tree(t_node("signature_list", x_info1),  [ _] ) ) = LIST ([], x_info1)
  
  | fromConcrete( tree(t_node("signature", x_info1),        
                       [ 
							x_id,
							x_colon,
							x_typeExpr
                       ]              
                     ) 
              ) = let
					fun auxFirst( any_expr, LIST (expr_list, _) ) = LIST( any_expr :: expr_list, x_info1 )
					  | auxFirst( t1, t2)                         = (
																		print("Error in ABSTRACT.fromConcrete: signature.auxFirst.\n");
																		raise General.Fail("Error in ABSTRACT.fromConcrete: signature.\n")
																	)
						
					val expr_id			= fromConcrete x_id
					val expr_typeExpr	= fromConcrete x_typeExpr
                  in
					auxFirst (expr_id, expr_typeExpr ) 
                  end
									
   | fromConcrete( tree(t_node("typeExpr", x_info1),        
                       [ 
							x_typeTerm,
							x_arrow,
							x_typeBase
                       ]              
                     ) 
              ) = let
					fun auxLast( LIST (expr_list, _) , expr ) = LIST( expr_list @ [ expr ], x_info1 )
					  | auxLast( t1, t2)                	  = (
																	 print("Error in ABSTRACT.fromConcrete: typeExpr.auxLast.\n");
					                                                 raise General.Fail("Error in ABSTRACT.fromConcrete: typeExpr.\n")
																)
					  
					val expr_typeTerm	= fromConcrete x_typeTerm
					val expr_typeBase	= fromConcrete x_typeBase
                  in
					auxLast (expr_typeTerm, expr_typeBase ) 
                  end
								
   | fromConcrete( tree(t_node("typeTerm", x_info1),        
                       [ 
							x_typeBase,
							x_star,
							x_typeTerm
                       ]              
                     ) 
              ) = let
					fun auxFirst( any_expr, LIST (expr_list, _) ) = LIST( any_expr :: expr_list, x_info1 )
					  | auxFirst( t1, t2)                         = (
																		print("Error in ABSTRACT.fromConcrete: typeTerm.auxFirst.\n");
																		raise General.Fail("Error in ABSTRACT.fromConcrete: typeTerm.\n")
																	)
								
					val expr_typeBase	= fromConcrete x_typeBase					  
					val expr_typeTerm	= fromConcrete x_typeTerm
                  in
					auxFirst (expr_typeBase, expr_typeTerm )
                  end
				  
   | fromConcrete( tree(t_node("typeTerm", x_info1),        
                       [ 
							x_typeBase
                       ]              
                     ) 
              ) = let
					val expr_typeBase	= fromConcrete x_typeBase					  
                  in
					LIST ( [expr_typeBase], x_info1) 
                  end
						
  | fromConcrete(tree(t_node("typeBase",x_info),
                           [
							tree(t_node("schemaType",_), [ tree(t_node(the_schema_type,_),[]) ] )
                           ]
                         )   
                    ) = IDENTIFIER (the_schema_type, x_info)				  
													
   | fromConcrete( tree(t_node("typeBase", x_info),        
                       [ 
							tree(t_node("unit",_),[])
                       ]              
                     ) 
              ) = IDENTIFIER( "unit", x_info )
				  
   | fromConcrete( tree(t_node("typeBase", x_info),        
                       [ 
							tree(t_node("int",_),[])
                       ]              
                     ) 
              ) = IDENTIFIER( "int", x_info )
				  
   | fromConcrete( tree(t_node("typeBase", x_info),        
                       [ 
							tree(t_node("bool",_),[])
                       ]              
                     ) 
              ) = IDENTIFIER( "bool", x_info )
				  
   | fromConcrete( tree(t_node("typeBase", x_info),        
                       [ 
							tree(t_node("string",_),[])
                       ]              
                     ) 
              ) = IDENTIFIER( "string", x_info )
				  
   | fromConcrete( tree(t_node("typeBase", x_info),        
                       [ 
							tree(t_node("real",_),[])
                       ]              
                     ) 
              ) = IDENTIFIER( "real", x_info )
						
   | fromConcrete( tree(t_node("typeBase", x_info),        
                       [ 
							tree(t_node("control",_),[])
                       ]              
                     ) 
              ) = IDENTIFIER( "control", x_info )
				  
			  

(* ================================================== *)
(*                 Regular Declarations               *)
(* ================================================== *)
  | fromConcrete( tree(t_node("decl", x_info1),        
                       [ 
                         tree(t_node("strategy", _), _),
                         label,
                         tree(t_node("parse_expr_list", x_info2), [ tree(t_node("", x_info3), []) ]),
                         tree(t_node(":",x_info4),[]),
                         expr
                       ]              
                     ) 
              ) = let
                      val label_1  = fromConcrete label
                      val expr_1   = fromConcrete expr
                          
                  in
                     NON_RECURSIVE( label_1, expr_1, x_info1 ) 
                  end
															
  | fromConcrete( tree(t_node("decl",x_info1),        
                       [ label,
                         t as tree(t_node("parse_expr_list",x_info2), parse_expr_list),
                         tree(t_node(":",x_info3),[]),
                         expr
                       ]              
                     )  
              ) = let
                      fun make_rule(lhs, expr) = RULE(lhs,expr,x_info1);
															
                      fun get_arg_list(tree(t_node("parse_expr_list", y_info), 
                                                     [ parse_expr, 
                                                       parse_expr_list 
                                                     ] 
                                           ) 
                                       ) = let
                                               val arg      = fromConcrete(parse_expr)
                                               val arg_list = get_arg_list(parse_expr_list)
                                           in
                                               arg :: arg_list
                                           end
                        | get_arg_list(tree(t_node("parse_expr_list", y_info1),[ tree(t_node("",y_info2), []) ]) ) = []
                        | get_arg_list _ = raise General.Fail("Error in ABSTRACT.fromConcrete.get_arg_list.\n");
																			
                      val label_1              = fromConcrete label
                      val parse_expr_list_1    = get_arg_list t
                      val expr_1               = fromConcrete expr
                      val expr_2               = foldr make_rule expr_1 parse_expr_list_1 
                                                          
                  in
                      NON_RECURSIVE( label_1, expr_2, x_info1 ) 
                  end
												
  | fromConcrete( tree(t_node("decl", x_info1),        
                       [ tree(t_node("def", _),[]),
                         name,
                         t as tree(t_node("arg_list",_), arg_list),
                         tree(t_node("=",_),[]),
                         expr
                       ]              
                     )  
              ) = let
							
					fun aux( tree(t_node("arg_list",_),  [ arg, arg_list ] )  ) = let
																						val arg_1      = fromConcrete(arg) 
																						val arg_list_1 = aux(arg_list)
																			  	  in
																						arg_1 :: arg_list_1
																				  end
                     
                      | aux( tree(t_node("arg_list",_),   [ tree(t_node("",_), []) ] )) = []
                      | aux _ = raise General.Fail("Error in ABSTRACT.fromConcrete.aux: badly formed arg_list.\n")
											
                      val name_1        = fromConcrete name
                      val arg_list_1    = aux t
                      val expr_1        = fromConcrete expr
                                                          
                  in
                      RECURSIVE( name_1, arg_list_1, expr_1, x_info1 ) 
                  end
									
  | fromConcrete( tree(t_node("t_program", x_info),  [ decl_list ]       )  ) = 
		let
												
			fun aux( tree(t_node("decl_list",_),  [ decl, decl_list ] )  ) = let
																				val decl_1      = fromConcrete(decl) 
																				val decl_list_1 = aux(decl_list)
																			in
																				decl_1 :: decl_list_1
																			end
																				
              | aux( tree(t_node("decl_list",_),   [ tree(t_node("",_), []) ] )) = []
																	
	          | aux some_tree = (
									raise General.Fail("Error in toAbsract.aux: Badly formed input tree.\n")
								);
														
			val the_declarations = aux decl_list
		in
			PROG (the_declarations, x_info)
		end
														
(* ================================================== *)
(*                Strategic Boolean                   *)
(* ================================================== *)
 | fromConcrete(tree(t_node("expr",x_info),
                            [expr_1a, 
                             tree(t_node("andalso",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    ANDALSO (expr_1b, expr_2b,x_info)
                                end
														
  | fromConcrete(tree(t_node("expr",x_info),
                            [expr_1a, 
                             tree(t_node("orelse",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    ORELSE (expr_1b, expr_2b,x_info)
                                end
															
(* ================================================== *)
(*                   Match                            *)
(* ================================================== *)
  | fromConcrete(tree(t_node("expr",x_info),
                            [expr_1a, 
                             tree(t_node("=",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    MATCH (expr_1b, expr_2b,x_info)
                                end
																
(* ================================================== *)
(*                   Bind                             *)
(* ================================================== *)
  | fromConcrete(tree(t_node("expr",x_info),
                            [expr_1a, 
                             tree(t_node(":=",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    BIND (expr_1b, expr_2b, x_info)
                                end
											
(* ================================================== *)
(*                Binary Combinators                  *)
(* ================================================== *)
  | fromConcrete(tree(t_node("expr",x_info),
                            [expr_1a, 
                             tree(t_node("<+>",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    CHOICE (expr_1b, expr_2b,x_info)
                                end
														
  | fromConcrete(tree(t_node("expr",x_info),
                            [expr_1a, 
                             tree(t_node("<+",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    LCHOICE (expr_1b, expr_2b, x_info)
                                end
																	
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("+>",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    RCHOICE (expr_1b, expr_2b, x_info)
                                end
												
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("<;",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    LSEQ (expr_1b, expr_2b, x_info)
                                end
															
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node(";>",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    RSEQ (expr_1b, expr_2b, x_info)
                                end
																
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("<*",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    LSTAR (expr_1b, expr_2b, x_info)
                                end
																
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("*>",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    RSTAR (expr_1b, expr_2b, x_info)
                                end
												
(* ================================================== *)
(*                Rewrite Rules                       *)
(* ================================================== *)
  | fromConcrete(tree(t_node("expr", x_info),
                            [lhs, 
                             tree(t_node("->",_),[]),
                             rhs
                            ]
                         )  ) = let
                                    val lhs_1 = fromConcrete(lhs)
                                    val rhs_1 = fromConcrete(rhs)
                                in
                                    RULE (lhs_1, rhs_1, x_info)
                                end
															
  | fromConcrete(tree(t_node("expr", x_info),
                            [lhs, 
                             tree(t_node("->",_),[]),
                             rhs,
                             tree(t_node("if",_),[]),
                             tree(t_node("{",_),[]),
                             cond,
                             tree(t_node("}",_),[])
                            ]
                         )  ) = let
                                    val lhs_1  = fromConcrete(lhs)
                                    val rhs_1  = fromConcrete(rhs)
                                    val cond_1 = fromConcrete(cond)
                                in
                                    COND_RULE (lhs_1, rhs_1, cond_1, x_info)
                                end
																
(* ================================================== *)
(*              Boolean Operators                     *)
(* ================================================== *)
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("||",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    B_OR (expr_1b, expr_2b, x_info)
                                end
											
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("&&",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    B_AND (expr_1b, expr_2b, x_info)
                                end
												
(* ================================================== *)
(*               Relational Operators                 *)
(* ================================================== *)
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("==",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    EQ (expr_1b, expr_2b, x_info)
                                end
																
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("!=",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    NEQ (expr_1b, expr_2b, x_info)
                                end
													
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("<",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    LT (expr_1b, expr_2b, x_info)
                                end
									
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("<=",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    LEQ (expr_1b, expr_2b, x_info)
                                end
												
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node(">",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    GT (expr_1b, expr_2b, x_info)
                                end
													
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node(">=",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    GEQ (expr_1b, expr_2b, x_info)
                                end
										
(* ================================================== *)
(*                    Math and String                 *)
(* ================================================== *)
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("^",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    CONCAT (expr_1b, expr_2b, x_info)
                                end
													
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("+",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    PLUS (expr_1b, expr_2b, x_info)
                                end
												
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("-",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    MINUS (expr_1b, expr_2b, x_info)
                                end
													
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("*",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    TIMES (expr_1b, expr_2b, x_info)
                                end
														
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("/",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    DIVIDE (expr_1b, expr_2b, x_info)
                                end
																
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("div",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    DIV (expr_1b, expr_2b, x_info)
                                end
															
  | fromConcrete(tree(t_node("expr", x_info),
                            [expr_1a, 
                             tree(t_node("mod",_),[]),
                             expr_2a
                            ]
                         )  ) = let
                                    val expr_1b = fromConcrete(expr_1a)
                                    val expr_2b = fromConcrete(expr_2a)
                                in
                                    MOD (expr_1b, expr_2b, x_info)
                                end
																	
  | fromConcrete(tree(t_node("expr", x_info),[application])  ) = fromConcrete application
														
(* ================================================== *)
(*                  Application                       *)
(* ================================================== *)
                        
  | fromConcrete(tree(t_node("application",x_info),
                            [application, 
                             base
                            ]
                         )  ) = let
                                    fun getString( IDENTIFIER (id,_) ) = id
                                      | getString _                    = ""

                                    fun isUnary( IDENTIFIER ("mapL",_         )) = true
									  | isUnary( IDENTIFIER ("mapR",_         )) = true
                               	      | isUnary( IDENTIFIER ("mapB",_         )) = true
                                                                                  
									  | isUnary( IDENTIFIER ("transient",_    )) = true
									  | isUnary( IDENTIFIER ("opaque"   ,_    )) = true
                                      | isUnary( IDENTIFIER ("raise"    ,_    )) = true
									  | isUnary( IDENTIFIER ("hide"     ,_    )) = true
									  | isUnary( IDENTIFIER ("lift"     ,_    )) = true
                                                                                        
                                      | isUnary( IDENTIFIER ("not"      ,_    )) = true
									  | isUnary( IDENTIFIER ("!"        ,_    )) = true
									  | isUnary( IDENTIFIER ("~"        ,_    )) = true
                                                                                     
                                      | isUnary( IDENTIFIER ("fold_choice" ,_ )) = true
									  | isUnary( IDENTIFIER ("fold_lchoice",_ )) = true
									  | isUnary( IDENTIFIER ("fold_rchoice",_ )) = true
                                      | isUnary( IDENTIFIER ("fold_lseq"   ,_ )) = true
									  | isUnary( IDENTIFIER ("fold_rseq"   ,_ )) = true
									  | isUnary( IDENTIFIER ("fold_lstar"  ,_ )) = true
                                      | isUnary( IDENTIFIER ("fold_rstar"  ,_ )) = true
                                                                                    
                                      | isUnary( IDENTIFIER ("folds_choice" ,_ )) = true
									  | isUnary( IDENTIFIER ("folds_lchoice",_ )) = true
									  | isUnary( IDENTIFIER ("folds_rchoice",_ )) = true
                                      | isUnary( IDENTIFIER ("folds_lseq"   ,_ )) = true
									  | isUnary( IDENTIFIER ("folds_rseq"   ,_ )) = true
									  | isUnary( IDENTIFIER ("folds_lstar"  ,_ )) = true
                                      | isUnary( IDENTIFIER ("folds_rstar"  ,_ )) = true
                                                                              
									  | isUnary( expr                       ) = isPredefinedIterator (getString expr);
																		
																							
                                    val expr    = fromConcrete(application)
                                    val base_0  = fromConcrete(base) 
                                    val base_1  = if isUnary( base_0 ) then raise General.Fail("Error in ABSTRACT.fromConcrete: Syntax Error...unary function (e.g., mapL, transient, etc.) in argument position.\n")
                                                                       else base_0
																						
                                in
                                    case expr of
																								
                                        IDENTIFIER ("mapL"         ,_) => MAPL          (base_1, x_info)
                                      | IDENTIFIER ("mapR"         ,_) => MAPR          (base_1, x_info)  
                                      | IDENTIFIER ("mapB"         ,_) => MAPB          (base_1, x_info)
                                                                                                        
                                      | IDENTIFIER ("transient"    ,_) => TRANSIENT     (base_1, x_info) 
                                      | IDENTIFIER ("opaque"       ,_) => OPAQUE        (base_1, x_info) 
                                      | IDENTIFIER ("raise"        ,_) => RAISE         (base_1, x_info) 
                                      | IDENTIFIER ("hide"         ,_) => HIDE          (base_1, x_info)
                                      | IDENTIFIER ("lift"         ,_) => LIFT          (base_1, x_info)  
                                                                                                         
                                      | IDENTIFIER ("not"          ,_) => NOT           (base_1, x_info)
                                      | IDENTIFIER ("!"            ,_) => BANG          (base_1, x_info)  
                                      | IDENTIFIER ("~"            ,_) => TILDE         (base_1, x_info) 
                                                                                                       
                                      | IDENTIFIER ("fold_choice"  ,_) => FOLD_CHOICE   (base_1, x_info) 
                                      | IDENTIFIER ("fold_lchoice" ,_) => FOLD_LCHOICE  (base_1, x_info) 
                                      | IDENTIFIER ("fold_rchoice" ,_) => FOLD_RCHOICE  (base_1, x_info) 
                                      | IDENTIFIER ("fold_lseq"    ,_) => FOLD_LSEQ     (base_1, x_info) 
                                      | IDENTIFIER ("fold_rseq"    ,_) => FOLD_RSEQ     (base_1, x_info) 
                                      | IDENTIFIER ("fold_lstar"   ,_) => FOLD_LSTAR    (base_1, x_info) 
                                      | IDENTIFIER ("fold_rstar"   ,_) => FOLD_RSTAR    (base_1, x_info) 
                                                                                                         
                                      | IDENTIFIER ("folds_choice" ,_) => FOLDS_CHOICE  (base_1, x_info) 
                                      | IDENTIFIER ("folds_lchoice",_) => FOLDS_LCHOICE (base_1, x_info) 
                                      | IDENTIFIER ("folds_rchoice",_) => FOLDS_RCHOICE (base_1, x_info) 
                                      | IDENTIFIER ("folds_lseq"   ,_) => FOLDS_LSEQ    (base_1, x_info) 
                                      | IDENTIFIER ("folds_rseq"   ,_) => FOLDS_RSEQ    (base_1, x_info) 
                                      | IDENTIFIER ("folds_lstar"  ,_) => FOLDS_LSTAR   (base_1, x_info) 
                                      | IDENTIFIER ("folds_rstar"  ,_) => FOLDS_RSTAR   (base_1, x_info) 
																				
                                      | IDENTIFIER (id             ,y_info)                        => if isPredefinedIterator(id) then ITERATOR( IDENTIFIER (id, y_info), [base_1], x_info )
                                                                                                      else APP(expr,base_1,x_info)
                                                                               
                                      | ITERATOR( IDENTIFIER ("TdlBul", y1_info), [sTD], y2_info ) => ITERATOR( IDENTIFIER ("TdlBul", y1_info), [sTD,base_1], x_info )                                     
                                      
                                      | otherwise                  => APP(expr,base_1,x_info)
                                end
																		
  | fromConcrete(tree(t_node("application",_),[base])  ) = fromConcrete base
																			
(* ================================================== *)
(*                  Base/Primitive                    *)
(* ================================================== *)
  | fromConcrete(tree(t_node("base",_),[child])   ) = fromConcrete(child)
																	
  | fromConcrete(tree(t_node("base",_),
                            [tree(t_node("(",_),[]), 
                             expr,
                             tree(t_node(")",_),[]) 
                            ]
                         )  ) = fromConcrete(expr)
														
  | fromConcrete(tree(t_node("library_call",x_info),
                            [	
								tree(t_node("sml",_),[]), 
								tree(t_node(".",_),[]), 
								tree(t_node("id",y_info), [tree(t_node(the_id,_),[])]),
								tree(t_node("(",_),[]), 
								tree_arg_list,
								tree(t_node(")",_),[]) 
                            ]
                         )  ) = let
                                    fun tree_list_to_expr_list(tree(t_node("expr_list",_),[expr,
                                                                                           tree(t_node(",",_),[]),
                                                                                           expr_list 
                                                                                          ]
                                                                   )
                                                              ) = let
                                                                      val expr_1      = fromConcrete expr
                                                                      val expr_list_1 = tree_list_to_expr_list expr_list
                                                                  in
                                                                      expr_1 :: expr_list_1
                                                                  end
																							
                                      | tree_list_to_expr_list(tree(t_node("expr_list",_),[expr]) 
                                                              ) = let
                                                                      val expr_1      = fromConcrete expr
                                                                  in
                                                                      expr_1::[]
                                                                  end
																				
                                      | tree_list_to_expr_list _ = raise General.Fail("Error in tree_list_to_expr_list: Unexpected tree structure.\n")
																		
                                    val expr_list = tree_list_to_expr_list(tree_arg_list)
                                in
                                    LIBRARY_CALL( IDENTIFIER (the_id, y_info), expr_list, x_info )
                                end
																			
  | fromConcrete(tree(t_node("library_call",x_info),
                            [tree(t_node("sml",_),[]), 
                             tree(t_node(".",_),[]), 
			                 tree(t_node("id",y_info), [tree(t_node(the_id,_),[])]),
                             tree(t_node("(",_),[]), 
                             tree(t_node(")",_),[]) 
                            ]
                         )  ) = LIBRARY_CALL_0( IDENTIFIER (the_id, y_info), x_info )
																
  | fromConcrete(tree(t_node("id",x_info),
                           [
                             tree(t_node(the_id,_),[])
                           ]
                         )   
                    ) = IDENTIFIER (the_id, x_info)

  | fromConcrete(t as tree(t_node("qualified_id",x_info), children)) = 
						let
							fun build( t, q_id ) = getLeaf t ^ q_id
							
							and getLeaf( tree(t_node( x, _ ), [])       ) = x
							  | getLeaf( tree(_             , children) ) = foldr build "" children
							  
							val the_id = getLeaf(t)
(* val _ = print("In fromConcrete qualified_id =[" ^ the_id ^ "]\n") *)
 							
						in
							IDENTIFIER (the_id, x_info)
						end
					
  | fromConcrete(tree(t_node("bool_value",x_info),
                           [
                             tree(t_node(value,_),[])
                           ]
                         )   
                    ) = let
                            val bool_value = case Bool.fromString(value) of
                                                SOME( a_value ) => a_value
                                              | NONE            => raise General.Fail("Error in fromConcrete: Expected boolean value.\n")
                        in
                            BOOL (bool_value, x_info)
                        end
													
  | fromConcrete(tree(t_node("int_value",x_info),
                           [
                             tree(t_node(value,_),[])
                           ]
                         )   
                    ) = let
                            val int_value = case Int.fromString(value) of
                                                SOME( a_value ) => a_value
                                              | NONE            => raise General.Fail("Error in fromConcrete: Expected integer value.\n")
                        in
                            INT (int_value, x_info)
                        end
													
  | fromConcrete(tree(t_node("real_value", x_info),
                           [
                             tree(t_node(value,_),[])
                           ]
                         )   
                    ) = REAL (value, x_info) 
															
  | fromConcrete(tree(t_node("string_value",x_info),
                           [
                             tree(t_node(the_string,_),[])
                           ]
                         )   
                    ) = STRING (the_string, x_info)
												
  | fromConcrete(tree(t_node("fold_combinator",x_info),
                          [tree(t_node("fold",_),[]),
                           tree(t_node("binary_combinator",_), [ tree(t_node(x,_),[]) ])
                          ]
                         )   
                    ) =  (case x of
                              "<+>" => IDENTIFIER   ("fold_choice"  , x_info)
                            | "<+"  => IDENTIFIER   ("fold_lchoice" , x_info)
                            | "+>"  => IDENTIFIER   ("fold_rchoice" , x_info)
                            | "<;"  => IDENTIFIER   ("fold_lseq"    , x_info)
                            | ";>"  => IDENTIFIER   ("fold_rseq"    , x_info)
                            | "<*"  => IDENTIFIER   ("fold_lstar"   , x_info)
                            | "*>"  => IDENTIFIER   ("fold_rstar"   , x_info)
                            | _     => raise General.Fail("Error: fold with unknown combinator.\n")
                          )
																	
  | fromConcrete(tree(t_node("fold_combinator", x_info),
                          [tree(t_node("foldS",_),[]),
                           tree(t_node("binary_combinator",_), [ tree(t_node(x,_),[]) ])
                          ]
                         )   
                    ) =  (case x of
                              "<+>" => IDENTIFIER   ("folds_choice"  , x_info)
                            | "<+"  => IDENTIFIER   ("folds_lchoice" , x_info)
                            | "+>"  => IDENTIFIER   ("folds_rchoice" , x_info)
                            | "<;"  => IDENTIFIER   ("folds_lseq"    , x_info)
                            | ";>"  => IDENTIFIER   ("folds_rseq"    , x_info)
                            | "<*"  => IDENTIFIER   ("folds_lstar"   , x_info)
                            | "*>"  => IDENTIFIER   ("folds_rstar"   , x_info) 
                            | _     => raise General.Fail("Error: folds with unknown combinator.\n")
                          )
															
(* ================================================== *)
(*                  Target Tree                       *)
(* ================================================== *)
  | fromConcrete(tree(t_node("target_tree_phrase", x_info)  , [t] ) )    = TERM (convertToITREE t, x_info)
																								
  | fromConcrete(t as tree(schema_var( name, x_info) , [] ) )            = TERM (convertToITREE t, x_info )
																			
(* ================================================== *)
(*                  Linear Structures                 *)
(* ================================================== *)
  | fromConcrete(tree(t_node("name", _)            ,[child] )  ) = fromConcrete child
  | fromConcrete(tree(t_node("arg", _)             ,[child] )  ) = fromConcrete child
  | fromConcrete(tree(t_node("unary", _)           ,[child] )  ) = fromConcrete child
  | fromConcrete(tree(t_node("traversal_op", _)    ,[child] )  ) = fromConcrete child
  | fromConcrete(tree(t_node("unary_combinator", _),[child] )  ) = fromConcrete child
  | fromConcrete(tree(t_node("primitive", _)       ,[child] )  ) = fromConcrete child
  | fromConcrete(tree(t_node("parse_expr", _)      ,[child] )  ) = fromConcrete child
																						
(* ================================================== *)
(*                  leaf nodes                        *)
(* ================================================== *)
  | fromConcrete(tree(t_node(name, x_info) ,[]) ) = nameToIdentifier  name  x_info
																						
(* ================================================== *)
(*                  error                             *)
(* ================================================== *)
  | fromConcrete(tree(t_node(name, x_info) ,_) ) =  (
                                   print("\n\n*************ERROR******************\n\n name = " ^ name ^ "\n\n");
                                   raise General.Fail("Error in ABSTRACT.fromConcrete: Badly formed input tree.\n")        
                             )

  | fromConcrete some_tree = (
                                   print("\n\n*************ERROR******************\n\n");
                                   raise General.Fail("Error in ABSTRACT.fromConcrete: Badly formed input tree.\n")        
                             );
																		
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
val INDENT = "   ";
val LM     = "\n";
																	
(* ------------------------------------------------------------------------------------------- *)
fun deconstruct (PROG         (expr_list, x_info))          = ("PROG"        ,expr_list, x_info)
								
  | deconstruct (SIGNATURE    (expr     , x_info))          = ("SIGNATURE"   , [expr]    , x_info )
  | deconstruct (LIST         (expr_list, x_info))          = ("LIST"        , expr_list , x_info )  
							
  | deconstruct (RECURSIVE    (id,expr_list,body, x_info))  = ("RECURSIVE"      ,[id] @ expr_list @ [body], x_info )
  | deconstruct (NON_RECURSIVE(id,body, x_info))            = ("NON_RECURSIVE"  ,[id, body], x_info)
																
  | deconstruct (ORELSE       (expr1,expr2, x_info))        = ("ORELSE"      ,[expr1,expr2], x_info)
  | deconstruct (ANDALSO      (expr1,expr2, x_info))        = ("ANDALSO"     ,[expr1,expr2], x_info)
                                                                                     
  | deconstruct (MATCH        (expr1,expr2, x_info))        = ("MATCH"       ,[expr1,expr2], x_info)
  | deconstruct (BIND         (expr1,expr2, x_info))        = ("BIND"        ,[expr1,expr2], x_info)
                                                                                     
  | deconstruct (CHOICE       (expr1,expr2, x_info))        = ("CHOICE"      ,[expr1,expr2], x_info)
  | deconstruct (LCHOICE      (expr1,expr2, x_info))        = ("LCHOICE"     ,[expr1,expr2], x_info)
  | deconstruct (RCHOICE      (expr1,expr2, x_info))        = ("RCHOICE"     ,[expr1,expr2], x_info)
  | deconstruct (LSEQ         (expr1,expr2, x_info))        = ("LSEQ"        ,[expr1,expr2], x_info)
  | deconstruct (RSEQ         (expr1,expr2, x_info))        = ("RSEQ"        ,[expr1,expr2], x_info)
  | deconstruct (LSTAR        (expr1,expr2, x_info))        = ("LSTAR"       ,[expr1,expr2], x_info)
  | deconstruct (RSTAR        (expr1,expr2, x_info))        = ("RSTAR"       ,[expr1,expr2], x_info)
                                                                                      
  | deconstruct (RULE         (expr1,expr2, x_info))        = ("RULE"        ,[expr1,expr2], x_info)
  | deconstruct (COND_RULE    (expr1,expr2,expr3, x_info))  = ("COND_RULE"   ,[expr1,expr2,expr3], x_info)
                                                                                      
  | deconstruct (B_OR         (expr1,expr2, x_info))        = ("B_OR"        ,[expr1,expr2], x_info)
  | deconstruct (B_AND        (expr1,expr2, x_info))        = ("B_AND"       ,[expr1,expr2], x_info)
                                                                                      
  | deconstruct (EQ           (expr1,expr2, x_info))        = ("EQ"          ,[expr1,expr2], x_info)
  | deconstruct (NEQ          (expr1,expr2, x_info))        = ("NEQ"         ,[expr1,expr2], x_info)
  | deconstruct (LEQ          (expr1,expr2, x_info))        = ("LEQ"         ,[expr1,expr2], x_info)
  | deconstruct (LT           (expr1,expr2, x_info))        = ("LT"          ,[expr1,expr2], x_info)
  | deconstruct (GEQ          (expr1,expr2, x_info))        = ("GEQ"         ,[expr1,expr2], x_info)
  | deconstruct (GT           (expr1,expr2, x_info))        = ("GT"          ,[expr1,expr2], x_info)
																								
  | deconstruct (CONCAT       (expr1,expr2, x_info))        = ("CONCAT"      ,[expr1,expr2], x_info)
  | deconstruct (PLUS         (expr1,expr2, x_info))        = ("PLUS"        ,[expr1,expr2], x_info)
  | deconstruct (MINUS        (expr1,expr2, x_info))        = ("MINUS"       ,[expr1,expr2], x_info)
  | deconstruct (TIMES        (expr1,expr2, x_info))        = ("TIMES"       ,[expr1,expr2], x_info)
  | deconstruct (DIVIDE       (expr1,expr2, x_info))        = ("DIVIDE"      ,[expr1,expr2], x_info)
  | deconstruct (DIV          (expr1,expr2, x_info))        = ("DIV"         ,[expr1,expr2], x_info)
  | deconstruct (MOD          (expr1,expr2, x_info))        = ("MOD"         ,[expr1,expr2], x_info)
																								
  | deconstruct (APP          (expr1,expr2, x_info))        = ("APP"         ,[expr1,expr2], x_info)
  | deconstruct (ITERATOR     (id,arg_list, x_info))        = ("ITERATOR"    ,[id] @ arg_list, x_info)
                                                                                      
  | deconstruct (BOOL         (expr, x_info))     		    = ("BOOL"        ,[BOOL       (expr, x_info)          ], x_info)
  | deconstruct (INT          (expr, x_info))           	= ("INT"         ,[INT        (expr, x_info)          ], x_info)
  | deconstruct (REAL         (expr, x_info))           	= ("REAL"        ,[REAL       (expr, x_info)          ], x_info)
  | deconstruct (STRING       (expr, x_info))           	= ("STRING"      ,[STRING     (expr, x_info)          ], x_info)    
  | deconstruct (IDENTIFIER   (str , x_info))           	= ("IDENTIFIER"  ,[IDENTIFIER (str, x_info)           ], x_info)
  | deconstruct (REF          (str,ref_info, x_info))      	= ("REF"         ,[REF        (str, ref_info, x_info) ], x_info)
																	
  | deconstruct (TERM         (parse_tree, x_info))      	= ("TERM"        ,[TERM (parse_tree, x_info)], x_info )
																	
  | deconstruct (LIBRARY_CALL_0 (id, x_info))           	= ("LIBRARY_CALL_0",[LIBRARY_CALL_0(id, x_info)], x_info )
  | deconstruct (LIBRARY_CALL   (id,expr_list, x_info)) 	= ("LIBRARY_CALL"  ,[LIBRARY_CALL(id,expr_list, x_info)], x_info )                                                                                      
																
  | deconstruct (ID x_info)                            	    = ("ID"          ,[], x_info)
  | deconstruct (SKIP x_info)                              	= ("SKIP"        ,[], x_info)
  | deconstruct (FAIL x_info)                              	= ("FAIL"        ,[], x_info)
                                                                                      
  | deconstruct (NOT   (expr, x_info))                  	= ("NOT"         ,[NOT   (expr, x_info)], x_info)
  | deconstruct (BANG  (expr, x_info))                  	= ("BANG"        ,[BANG  (expr, x_info)], x_info)
  | deconstruct (TILDE (expr, x_info))                  	= ("TILDE"       ,[TILDE (expr, x_info)], x_info)
                                                                                      
  | deconstruct (TRANSIENT (expr, x_info))              	= ("TRANSIENT"   ,[TRANSIENT (expr, x_info)], x_info)
  | deconstruct (OPAQUE    (expr, x_info))              	= ("OPAQUE"      ,[OPAQUE    (expr, x_info)], x_info)
  | deconstruct (RAISE     (expr, x_info))              	= ("RAISE"       ,[RAISE     (expr, x_info)], x_info)
  | deconstruct (HIDE      (expr, x_info))              	= ("HIDE"        ,[HIDE      (expr, x_info)], x_info)
  | deconstruct (LIFT      (expr, x_info))              	= ("LIFT"        ,[LIFT      (expr, x_info)], x_info)
                                                                                      
  | deconstruct (MAPL (expr, x_info))                   	= ("MAPL"        ,[MAPL (expr, x_info)], x_info)
  | deconstruct (MAPR (expr, x_info))                   	= ("MAPR"        ,[MAPR (expr, x_info)], x_info)
  | deconstruct (MAPB (expr, x_info))                   	= ("MAPB"        ,[MAPB (expr, x_info)], x_info)
                                                                                      
  | deconstruct (FOLD_CHOICE  (expr, x_info))           	= ("FOLD_CHOICE" ,[FOLD_CHOICE  (expr, x_info)], x_info)  
  | deconstruct (FOLD_LCHOICE (expr, x_info))           	= ("FOLD_LCHOICE",[FOLD_LCHOICE (expr, x_info)], x_info)
  | deconstruct (FOLD_RCHOICE (expr, x_info))           	= ("FOLD_RCHOICE",[FOLD_RCHOICE (expr, x_info)], x_info)
  | deconstruct (FOLD_LSEQ    (expr, x_info))           	= ("FOLD_LSEQ"   ,[FOLD_LSEQ    (expr, x_info)], x_info)
  | deconstruct (FOLD_RSEQ    (expr, x_info))           	= ("FOLD_RSEQ"   ,[FOLD_RSEQ    (expr, x_info)], x_info)
  | deconstruct (FOLD_LSTAR   (expr, x_info))           	= ("FOLD_LSTAR"  ,[FOLD_LSTAR   (expr, x_info)], x_info)
  | deconstruct (FOLD_RSTAR   (expr, x_info))           	= ("FOLD_RSTAR"  ,[FOLD_RSTAR   (expr, x_info)], x_info)
															
  | deconstruct (FOLDS_CHOICE  (expr, x_info))          	= ("FOLDS_CHOICE" ,[FOLDS_CHOICE  (expr, x_info)], x_info)  
  | deconstruct (FOLDS_LCHOICE (expr, x_info))          	= ("FOLDS_LCHOICE",[FOLDS_LCHOICE (expr, x_info)], x_info)
  | deconstruct (FOLDS_RCHOICE (expr, x_info))          	= ("FOLDS_RCHOICE",[FOLDS_RCHOICE (expr, x_info)], x_info)
  | deconstruct (FOLDS_LSEQ    (expr, x_info))          	= ("FOLDS_LSEQ"   ,[FOLDS_LSEQ    (expr, x_info)], x_info)
  | deconstruct (FOLDS_RSEQ    (expr, x_info))          	= ("FOLDS_RSEQ"   ,[FOLDS_RSEQ    (expr, x_info)], x_info)
  | deconstruct (FOLDS_LSTAR   (expr, x_info))          	= ("FOLDS_LSTAR"  ,[FOLDS_LSTAR   (expr, x_info)], x_info)
  | deconstruct (FOLDS_RSTAR   (expr, x_info))          	= ("FOLDS_RSTAR"  ,[FOLDS_RSTAR   (expr, x_info)], x_info)
																
  | deconstruct UNIT                                    	= raise General.Fail("Error in ABSTRACT.deconstruct: encountered UNIT.\n");  
                                                                                      
 
(* ------------------------------------------------------------------------------------------- *)
fun getBool( [BOOL(value, _)] ) = value
  | getBool x_list              = let
									val msg = "Error in ABSTRACT.getBool.\n"
								  in
									print(msg);
									raise RUNTIME.error(x_list, General.Fail(msg),printTree, getExprInfo, printNodeInfo)
								  end

and getInt( [INT (value, _)] ) = value
  | getInt x_list              = let
									val msg = "Error in ABSTRACT.getInt.\n"
								 in
									print(msg);
									raise RUNTIME.error(x_list, General.Fail(msg),printTree, getExprInfo, printNodeInfo)
								 end

and getReal( [REAL (value, _)] ) = value
  | getReal x_list               = 	let
										val msg = "Error in ABSTRACT.getReal.\n"
									in
										print(msg);
										raise RUNTIME.error(x_list, General.Fail(msg),printTree, getExprInfo, printNodeInfo)
									end

and getString( [STRING (value, _)] ) = value
  | getString x_list                = let
										val msg = "Error in ABSTRACT.getString.\n"
									  in
										print(msg);
										raise RUNTIME.error(x_list, General.Fail(msg),printTree, getExprInfo, printNodeInfo)
									  end

and getIdentifier( [IDENTIFIER (value, _)] ) = value
  | getIdentifier x_list                     = let
													val msg = "Error in ABSTRACT.getIdentifier.\n"
												in
													print(msg);
													raise RUNTIME.error(x_list, General.Fail(msg),printTree, getExprInfo, printNodeInfo)
												end

and getRef( [REF (str, ref_info, _) ] ) = 	let
												val strategic_context = #CONTEXT (ref_info)
												val index             = #INDEX   (ref_info)
												val absolute_address  = if isSome(index) then Int.toString(valOf index) else "undefined"
										    in
												strategic_context ^ "|" ^ str ^ "|" ^ absolute_address
											end
  | getRef x_list                  = let
										val msg = "Error in ABSTRACT.getRef.\n"
									 in
										print(msg);
										raise RUNTIME.error(x_list, General.Fail(msg),printTree, getExprInfo, printNodeInfo)
									 end

and getTree( [TERM (value, _)] ) = value
  | getTree x_list               = 	let
										val msg = "Error in ABSTRACT.getTree.\n"
									in
										print(msg);
										raise RUNTIME.error(x_list, General.Fail(msg),printTree, getExprInfo, printNodeInfo)
									end

and getArgList( [LIBRARY_CALL(id, arg_list, _)] ) = arg_list
  | getArgList x_list                             = let
														val msg = "Error in ABSTRACT.getArgList.\n"
													in
														print(msg);
														raise RUNTIME.error(x_list, General.Fail(msg),printTree, getExprInfo, printNodeInfo)
													end

and getLibraryCall_0Id( [LIBRARY_CALL_0(id, _)] ) = id
  | getLibraryCall_0Id x_list                     = let
														val msg = "Error in ABSTRACT.getLibraryCall_0Id.\n"
													in
														print(msg);
														raise RUNTIME.error(x_list, General.Fail(msg),printTree, getExprInfo, printNodeInfo)
													end

and getLibraryCallId( [LIBRARY_CALL(id, arg_list, _)] ) = id
  | getLibraryCallId x_list                             = let
															val msg = "Error in ABSTRACT.getLibraryCallId.\n"
														  in
															print(msg);
															raise RUNTIME.error(x_list, General.Fail(msg),printTree, getExprInfo, printNodeInfo)
														  end

and getIteratorArgList( id :: arg_list ) = arg_list
  | getIteratorArgList x_list            = 	let
												val msg = "Error in ABSTRACT.getIteratorArgList.\n"
											in
												print(msg);
												raise RUNTIME.error(x_list, General.Fail(msg), printTree, getExprInfo, printNodeInfo)
											end

and getIteratorId( id :: arg_list ) = id
  | getIteratorId  x_list           = let
										val msg = "Error in ABSTRACT.getIteratorId.\n"
									  in
										print(msg);
										raise RUNTIME.error(x_list, General.Fail(msg), printTree, getExprInfo, printNodeInfo)
									  end

and getUnary( [NOT        (expr, _)] ) = expr
  | getUnary( [BANG       (expr, _)] ) = expr
  | getUnary( [TILDE      (expr, _)] ) = expr
                                      
  | getUnary( [TRANSIENT     (s, _)] ) = s
  | getUnary( [OPAQUE        (s, _)] ) = s
  | getUnary( [RAISE         (s, _)] ) = s
                                       
  | getUnary( [HIDE          (s, _)] ) = s
  | getUnary( [LIFT          (s, _)] ) = s
                                      
  | getUnary( [MAPL          (s, _)] ) = s
  | getUnary( [MAPR          (s, _)] ) = s
  | getUnary( [MAPB          (s, _)] ) = s
                                      
  | getUnary( [FOLD_CHOICE   (s, _)] ) = s
  | getUnary( [FOLD_LCHOICE  (s, _)] ) = s
  | getUnary( [FOLD_RCHOICE  (s, _)] ) = s
  | getUnary( [FOLD_LSEQ     (s, _)] ) = s
  | getUnary( [FOLD_RSEQ     (s, _)] ) = s
  | getUnary( [FOLD_LSTAR    (s, _)] ) = s
  | getUnary( [FOLD_RSTAR    (s, _)] ) = s

  | getUnary( [FOLDS_CHOICE  (s, _)] ) = s
  | getUnary( [FOLDS_LCHOICE (s, _)] ) = s
  | getUnary( [FOLDS_RCHOICE (s, _)] ) = s
  | getUnary( [FOLDS_LSEQ    (s, _)] ) = s
  | getUnary( [FOLDS_RSEQ    (s, _)] ) = s
  | getUnary( [FOLDS_LSTAR   (s, _)] ) = s
  | getUnary( [FOLDS_RSTAR   (s, _)] ) = s

  | getUnary term_list            = let
										val msg = "Error in ABSTRACT.getUnary.\n"
									in
										print(msg);
										RUNTIME.error(term_list, General.Fail(msg), printTree, getExprInfo, printNodeInfo)
									end
																															
																	
and getExprInfo( x_expr ) = 
	let
		val (x_str, x_expr_list, x_info ) = deconstruct x_expr
	in
		x_info
	end
																															
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
and printTree expr = 
	let
																		
	   fun aux LM expr = 
				let
			         val new_LM = LM ^ INDENT
			         val (value,expr_list, x_info) = deconstruct expr
                        handle ex as General.Fail _ => 
                            (
                                case expr of 
                                    ABSTRACT_REPRESENTATION.TRUE  => "TRUE"
                                  | ABSTRACT_REPRESENTATION.FALSE => "FALSE"
                                  | _ => raise ex,
                                [],
                                CONCRETE_REPRESENTATION.dummy_node_info
                            )
																		
			    in
                                 print(LM ^ value);
																							
                                 case  value of
																	
                                      "BOOL"            => print(new_LM ^ Bool.toString(getBool(expr_list)) )
									| "INT"             => print(new_LM ^ Int.toString(getInt(expr_list)) )
									| "REAL"            => print(new_LM ^ getReal(expr_list) )
									| "STRING"          => print(new_LM ^ getString(expr_list) )
									| "IDENTIFIER"      => print(new_LM ^ getIdentifier(expr_list) )
									| "REF"             => print(new_LM ^ getRef(expr_list) )
										
									| "NOT"             => aux new_LM (getUnary expr_list)
									| "BANG"            => aux new_LM (getUnary expr_list)
									| "TILDE"           => aux new_LM (getUnary expr_list)              
										
									| "TRANSIENT"       => aux new_LM (getUnary expr_list)
									| "OPAQUE"          => aux new_LM (getUnary expr_list)                   
									| "RAISE"           => aux new_LM (getUnary expr_list)                 
									| "HIDE"            => aux new_LM (getUnary expr_list)                 
									| "LIFT"            => aux new_LM (getUnary expr_list)              
										
									| "MAPL"            => aux new_LM (getUnary expr_list)
									| "MAPR"            => aux new_LM (getUnary expr_list)             
									| "MAPB"            => aux new_LM (getUnary expr_list)                   
	                                        
									| "FOLD_CHOICE"     => aux new_LM (getUnary expr_list)
									| "FOLD_LCHOICE"    => aux new_LM (getUnary expr_list)
									| "FOLD_RCHOICE"    => aux new_LM (getUnary expr_list)
									| "FOLD_LSEQ"       => aux new_LM (getUnary expr_list)
									| "FOLD_RSEQ"       => aux new_LM (getUnary expr_list)
									| "FOLD_LSTAR"      => aux new_LM (getUnary expr_list)
									| "FOLD_RSTAR"      => aux new_LM (getUnary expr_list)
										
									| "FOLDS_CHOICE"    => aux new_LM (getUnary expr_list)
									| "FOLDS_LCHOICE"   => aux new_LM (getUnary expr_list)
									| "FOLDS_RCHOICE"   => aux new_LM (getUnary expr_list)
									| "FOLDS_LSEQ"      => aux new_LM (getUnary expr_list)
									| "FOLDS_RSEQ"      => aux new_LM (getUnary expr_list)
									| "FOLDS_LSTAR"     => aux new_LM (getUnary expr_list)
									| "FOLDS_RSTAR"     => aux new_LM (getUnary expr_list)
										
                                                  
									| "TERM"            => CONCRETE.printTree new_LM (getTree(expr_list))
											
									| "LIBRARY_CALL_0"  => (
                                                            aux new_LM (getLibraryCall_0Id expr_list);
                                                            ()
                                                          )

                                                          
									| "LIBRARY_CALL"    => (
                                                            aux new_LM (getLibraryCallId expr_list);
                                                            map (aux new_LM) (getArgList(expr_list));
                                                            ()
                                                          )
														
                                                          
									| "ITERATOR"        => (
                                                            aux new_LM (getIteratorId expr_list);
                                                            map (aux new_LM) (getIteratorArgList(expr_list));
                                                            ()
                                                          )
															
														  | otherwise         => (map (aux new_LM) expr_list;())
                end
	in
	    aux "\n" expr;
        print("\n\n")
	end                                   
													
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun embeddedToFile out_stream  expr = 

	let
            fun nodeToXML node_type node_value x_info = 
					TextIO.output(	out_stream,
									"<abstract node=\"" ^ node_type ^ "\" " ^
									FILE_OPERATIONS.makeXMLToken(node_value, makeLineAttribute x_info, makeColumnAttribute x_info, makeLabelAttribute x_info) ^ 
									">"
								 );

            fun extract_child [NOT           (expr, _)] = [expr]
              | extract_child [BANG          (expr, _)] = [expr]
              | extract_child [TILDE         (expr, _)] = [expr]
                                                             
              | extract_child [TRANSIENT     (expr, _)] = [expr]
              | extract_child [OPAQUE        (expr, _)] = [expr]
              | extract_child [RAISE         (expr, _)] = [expr]
                                                          
              | extract_child [HIDE          (expr, _)] = [expr]
              | extract_child [LIFT          (expr, _)] = [expr]
                                                  
              | extract_child [MAPL          (expr, _)] = [expr]                                                          
              | extract_child [MAPR          (expr, _)] = [expr]                                                          
              | extract_child [MAPB          (expr, _)] = [expr]                                                            
                                                
              | extract_child [FOLD_CHOICE   (expr, _)] = [expr]
              | extract_child [FOLD_LCHOICE  (expr, _)] = [expr]
              | extract_child [FOLD_RCHOICE  (expr, _)] = [expr]
              | extract_child [FOLD_LSEQ     (expr, _)] = [expr]
              | extract_child [FOLD_RSEQ     (expr, _)] = [expr]
              | extract_child [FOLD_LSTAR    (expr, _)] = [expr]
              | extract_child [FOLD_RSTAR    (expr, _)] = [expr]
												
              | extract_child [FOLDS_CHOICE  (expr, _)] = [expr]
              | extract_child [FOLDS_LCHOICE (expr, _)] = [expr]
              | extract_child [FOLDS_RCHOICE (expr, _)] = [expr]
              | extract_child [FOLDS_LSEQ    (expr, _)] = [expr]
              | extract_child [FOLDS_RSEQ    (expr, _)] = [expr]
              | extract_child [FOLDS_LSTAR   (expr, _)] = [expr]
              | extract_child [FOLDS_RSTAR   (expr, _)] = [expr]
					
              | extract_child _                   = raise General.Fail("Error in ABSTRACT.embeddedToFile.extract_child.\n");
						
            val EPSILON = "";
	
			val (node_type,expr_list, x_info) = deconstruct expr
	in
																
                case  node_type of
																				
                      "BOOL"            => nodeToXML "BOOL" (Bool.toString( getBool expr_list) )  x_info
					| "INT"             => nodeToXML "INT"  (Int.toString ( getInt  expr_list) )  x_info
					| "REAL"            => nodeToXML "REAL" (getReal expr_list)  x_info
																							
					| "STRING"          => nodeToXML "STRING"     (getString     expr_list)  x_info
					| "IDENTIFIER"      => nodeToXML "IDENTIFIER" (getIdentifier expr_list)  x_info
					| "REF"             => nodeToXML "REF"        (getRef        expr_list)  x_info
																									
					| "NOT"             => (
                                            nodeToXML node_type EPSILON x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                          )
														
					| "BANG"            => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                          )
									
					| "TILDE"           => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                          )
									
					| "TRANSIENT"       => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
									
					| "OPAQUE"          => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
							
					| "RAISE"           => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
								
					| "HIDE"            => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
							
					| "LIFT"            => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
							
					| "MAPL"            => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
							
					| "MAPR"            => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
							
					| "MAPB"            => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
						
					| "FOLD_CHOICE"     => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
										
					| "FOLD_LCHOICE"    => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
								
					| "FOLD_RCHOICE"    => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
							
					| "FOLD_LSEQ"       => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
						
					| "FOLD_RSEQ"       => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
						
					| "FOLD_LSTAR"      => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
						
					| "FOLD_RSTAR"      => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
						
					| "FOLDS_CHOICE"     => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
								
					| "FOLDS_LCHOICE"    => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
							
					| "FOLDS_RCHOICE"    => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
										
					| "FOLDS_LSEQ"       => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
						
					| "FOLDS_RSEQ"       => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
									
					| "FOLDS_LSTAR"      => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
						
					| "FOLDS_RSTAR"      => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) (extract_child expr_list);
                                            ()
                                            
                                          )
						
					| "TERM"            => ( 
                                            nodeToXML node_type EPSILON  x_info;
                                            CONCRETE.embeddedToFile out_stream (getTree(expr_list))
                                          )
																	
					| "LIBRARY_CALL_0"  => (
                                            nodeToXML node_type EPSILON  x_info;
                                            embeddedToFile out_stream       (getLibraryCall_0Id expr_list);
                                            ()
                                          )
                                                        
					| "LIBRARY_CALL"    => (
                                            nodeToXML node_type EPSILON  x_info;
                                            embeddedToFile out_stream       (getLibraryCallId expr_list);
                                            map (embeddedToFile out_stream) (getArgList expr_list);
                                            ()
                                          )
																								
					| "ITERATOR"        => (
                                            nodeToXML node_type EPSILON  x_info;
                                            embeddedToFile out_stream       (getIteratorId expr_list);
                                            map (embeddedToFile out_stream) (getIteratorArgList expr_list);
                                            ()
                                          )
																				
					| otherwise         => (
                                            nodeToXML node_type EPSILON  x_info;
                                            map (embeddedToFile out_stream) expr_list;
                                            ()
                                          );
											
		TextIO.output(out_stream,"</abstract>");
		TextIO.output(out_stream,"\n")
	end
																			
(* ------------------------------------------------------------------------------------------- *)
fun EXPR_toXML( file_name, term_name, a_tree ) =
															
	let
        val out_stream = TextIO.openOut(file_name)
	in
	    TextIO.output(out_stream,"<XML_FILE label=\"" ^ term_name ^ "\">");
	    embeddedToFile out_stream a_tree; 
	    TextIO.output(out_stream,"</XML_FILE>");
					
	    TextIO.closeOut out_stream
	end;
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun build_abstract_tree(node_type, node_value, children, x_info) =
	let
		fun make_unary( [expr] ) = expr
		  | make_unary _         = raise General.Fail("Error in ABSTRACT.make_unary.\n");
										
		fun make_binary( [expr1, expr2], x_info ) = (expr1,expr2, x_info)
		  | make_binary _                 		  = raise General.Fail("Error in ABSTRACT.make_binary.\n");
										
		fun make_ternary( [expr1, expr2, expr3], x_info ) = (expr1,expr2,expr3, x_info)
		  | make_ternary (expr_list, _)                   = raise General.Fail("Error in ABSTRACT.make_ternary. List length = " ^ Int.toString(length(expr_list)) ^ "\n"); 
                      
		fun refFromString( str, y_info ) = 	
									let
                                        fun leftmostSplit( x, ys) = 
												let
				                                    fun aux( y::ys, left) = if x = y then (rev left, ys) else aux( ys, y::left )
                                                      | aux _             = raise General.Fail("Error in ABSTRACT.build_abstract_tree.refFromString.leftmostSplit.aux.\n");
														
													val (left, right) = aux(ys, [])
												in
                                                    (left, right)
                                                end
													
										fun makeInfo( name, index_str ) = 
												let
													val index_opt = Int.fromString(index_str)
												in
													{ CONTEXT = name, INDEX = index_opt }
												end
												
                                        val sep                       = #"|";
																			
                                        val (strategic_context,rest)  = leftmostSplit( sep, explode str )
                                        val (id               ,index) = leftmostSplit( sep, rest        )                                         
                                    in
                                        REF( implode id, makeInfo( implode strategic_context, implode index ), y_info )  
                                    end
												
		fun make_recursive( expr_list, x_info ) = 	
									let
										val name = List.hd expr_list
										val body = List.last expr_list
										val args = List.tl( List.take( expr_list, (List.length expr_list) - 1) )
									in
										(name, args, body, x_info)
									end
														
		fun make_iterator( expr_list, x_info ) = 	
									let			
										val name = List.hd expr_list
										val args = List.tl( expr_list )
									in				
										(name, args, x_info)				
									end		
													
        (* sml library call *)		
		fun make_library_call( expr_list, x_info ) = 	
												let
													val name = List.hd expr_list
													val args = List.tl( expr_list )
												in
													(name, args, x_info)
												end
		fun make_library_call_0( expr_list, x_info ) = 	
												let
                                                    val name = List.hd expr_list
                                                in
                                                    (name, x_info)
                                                end
												
		fun make_signature( [ expr ], x_info ) = (expr,x_info) 
		  | make_signature( xs      , _      ) = raise RUNTIME.error( xs , General.Fail("Error in case of ABSTRACT.make_signature. improper structure.\n"), printTree, getExprInfo, printNodeInfo)
					
		  
	in
	    case node_type of
			  "PROG"            => PROG (children, x_info)

			| "SIGNATURE"       => SIGNATURE     	(make_signature (children, x_info))
			| "LIST"  		    => LIST		     	(children, x_info)
			
			| "RECURSIVE"       => RECURSIVE     	(make_recursive (children, x_info))
			| "NON_RECURSIVE"   => NON_RECURSIVE 	(make_binary    (children, x_info))
																						
			| "ANDALSO"         => ANDALSO       	(make_binary 	(children, x_info))
			| "ORELSE"          => ORELSE        	(make_binary 	(children, x_info))
																						
			| "MATCH"           => MATCH         	(make_binary 	(children, x_info))
			| "BIND"            => BIND          	(make_binary 	(children, x_info))
																						
			| "CHOICE"          => CHOICE        	(make_binary 	(children, x_info))
			| "LCHOICE"         => LCHOICE       	(make_binary 	(children, x_info))
			| "RCHOICE"         => RCHOICE 			(make_binary 	(children, x_info))
			| "LSEQ"            => LSEQ    			(make_binary 	(children, x_info))
			| "RSEQ"            => RSEQ    			(make_binary 	(children, x_info))
			| "LSTAR"           => LSTAR   			(make_binary 	(children, x_info))
			| "RSTAR"           => RSTAR   			(make_binary 	(children, x_info))
																			
			| "RULE"            => RULE      		(make_binary  	(children, x_info))
			| "COND_RULE"       => COND_RULE 		(make_ternary 	(children, x_info))
																					
			| "B_AND"           =>  B_AND 			(make_binary  	(children, x_info))
			| "B_OR"            =>  B_OR  			(make_binary  	(children, x_info))
																					
			| "EQ"              =>  EQ  			(make_binary  	(children, x_info))
			| "NEQ"             =>  NEQ 			(make_binary  	(children, x_info))
			| "LEQ"             =>  LEQ 			(make_binary  	(children, x_info))
			| "LT"              =>  LT  			(make_binary  	(children, x_info))
			| "GEQ"             =>  GEQ 			(make_binary  	(children, x_info))
			| "GT"              =>  GT  			(make_binary  	(children, x_info))
																					
			| "CONCAT"          =>  CONCAT 			(make_binary  	(children, x_info))
			| "PLUS"            =>  PLUS   			(make_binary  	(children, x_info))
			| "MINUS"           =>  MINUS  			(make_binary  	(children, x_info))
			| "TIMES"           =>  TIMES  			(make_binary  	(children, x_info))
			| "DIVIDE"          =>  DIVIDE 			(make_binary  	(children, x_info))
			| "DIV"             =>  DIV    			(make_binary  	(children, x_info))
			| "MOD"             =>  MOD    			(make_binary  	(children, x_info))
																				
			| "APP"             =>  APP     		(make_binary   	(children, x_info))
			| "ITERATOR"        =>  ITERATOR		(make_iterator 	(children, x_info))
																				
			| "BOOL"            => 	let
										val value = case Bool.fromString(node_value) of
														  SOME( v ) => v
														| NONE      => raise General.Fail("Error in ABSTRACT.build_abstract_tree: bool option.\n")
	                                             
									in
										BOOL (value, x_info) 
									end
																
			| "INT"             => 	let
										val value = case Int.fromString(node_value) of
														  SOME( v ) => v
														| NONE      => raise General.Fail("Error in ABSTRACT.build_abstract_tree: int option.\n")
	                                             
									in
										INT (value, x_info) 
									end
																		
			| "REAL"            => REAL 			(node_value, x_info)
			| "STRING"          => STRING 			(node_value, x_info)
			| "IDENTIFIER"      => IDENTIFIER 		(node_value, x_info)
			| "REF"             => refFromString 	(node_value, x_info)
																
			| "TERM"            => List.hd(children)   
																
			| "LIBRARY_CALL_0"  => LIBRARY_CALL_0  	(make_library_call_0( children, x_info))
			| "LIBRARY_CALL"    => LIBRARY_CALL  	(make_library_call  ( children, x_info))
														
			| "ID"              => ID  				(x_info)        
			| "SKIP"            => SKIP				(x_info)
			| "FAIL"            => FAIL				(x_info)
														
			| "NOT"             => NOT   			(make_unary children, x_info)         
			| "BANG"            => BANG  			(make_unary children, x_info)                  
			| "TILDE"           => TILDE 			(make_unary children, x_info)                 
																		
			| "TRANSIENT"       => TRANSIENT 		(make_unary children, x_info)             
			| "OPAQUE"          => OPAQUE    		(make_unary children, x_info)                   
			| "RAISE"           => RAISE     		(make_unary children, x_info)
			| "HIDE"            => HIDE      		(make_unary children, x_info)
			| "LIFT"            => LIFT      		(make_unary children, x_info)
																				
			| "MAPL"            => MAPL 	 		(make_unary children, x_info)
			| "MAPR"            => MAPR 	 		(make_unary children, x_info)
			| "MAPB"            => MAPB 	 		(make_unary children, x_info)
																				
			| "FOLD_CHOICE"     => FOLD_CHOICE  	(make_unary children, x_info)
			| "FOLD_LCHOICE"    => FOLD_LCHOICE 	(make_unary children, x_info)
			| "FOLD_RCHOICE"    => FOLD_RCHOICE 	(make_unary children, x_info)
			| "FOLD_LSEQ"       => FOLD_LSEQ    	(make_unary children, x_info)
			| "FOLD_RSEQ"       => FOLD_RSEQ    	(make_unary children, x_info)
			| "FOLD_LSTAR"      => FOLD_LSTAR   	(make_unary children, x_info)
			| "FOLD_RSTAR"      => FOLD_RSTAR   	(make_unary children, x_info)
																			
			| "FOLDS_CHOICE"     => FOLDS_CHOICE  	(make_unary children, x_info)
			| "FOLDS_LCHOICE"    => FOLDS_LCHOICE 	(make_unary children, x_info)
			| "FOLDS_RCHOICE"    => FOLDS_RCHOICE 	(make_unary children, x_info)
			| "FOLDS_LSEQ"       => FOLDS_LSEQ    	(make_unary children, x_info)
			| "FOLDS_RSEQ"       => FOLDS_RSEQ    	(make_unary children, x_info)
			| "FOLDS_LSTAR"      => FOLDS_LSTAR   	(make_unary children, x_info)
			| "FOLDS_RSTAR"      => FOLDS_RSTAR   	(make_unary children, x_info)
			
            | "TdlBul"          => IDENTIFIER 		("TdlBul", x_info)            
			| "TDL"             => IDENTIFIER 		("TDL", x_info)
			| "TDR"             => IDENTIFIER 		("TDR", x_info)
			| "BUL"             => IDENTIFIER 		("BUL", x_info)
			| "BUR"             => IDENTIFIER 		("BUR", x_info)
			| "TD"              => IDENTIFIER 		("TD" , x_info)
			| "FIX"             => IDENTIFIER 		("FIX", x_info)
																				
			| "lseq_tdl"        => IDENTIFIER 		("lseq_tdl" , x_info)
            | "rseq_tdl"        => IDENTIFIER 		("rseq_tdl" , x_info)
            | "lseq_bul"        => IDENTIFIER 		("lseq_bul" , x_info)
            | "rseq_bul"        => IDENTIFIER 		("rseq_bul" , x_info)
            | "lcond_tdl"       => IDENTIFIER 		("lcond_tdl", x_info)
            | "rcond_tdl"       => IDENTIFIER 		("rcond_tdl", x_info)
            | "lcond_bul"       => IDENTIFIER 		("lcond_bul", x_info)
            | "rcond_bul"       => IDENTIFIER 		("rcond_bul", x_info)
            | "lstar_tdl"       => IDENTIFIER 		("lstar_tdl", x_info)
            | "rstar_tdl"       => IDENTIFIER 		("rstar_tdl", x_info)    
            | "lstar_bul"       => IDENTIFIER 		("lstar_bul", x_info)
            | "rstar_bul"       => IDENTIFIER 		("rstar_bul", x_info)
																
            | "lseq_tdr"        => IDENTIFIER 		("lseq_tdr" , x_info)
            | "rseq_tdr"        => IDENTIFIER 		("rseq_tdr" , x_info)
            | "lseq_bur"        => IDENTIFIER 		("lseq_bur" , x_info)
            | "rseq_bur"        => IDENTIFIER 		("rseq_bur" , x_info)
            | "lcond_tdr"       => IDENTIFIER 		("lcond_tdr", x_info)
            | "rcond_tdr"       => IDENTIFIER 		("rcond_tdr", x_info)
            | "lcond_bur"       => IDENTIFIER 		("lcond_bur", x_info)
            | "rcond_bur"       => IDENTIFIER 		("rcond_bur", x_info)
            | "lstar_tdr"       => IDENTIFIER 		("lstar_tdr", x_info)
            | "rstar_tdr"       => IDENTIFIER 		("rstar_tdr", x_info)
            | "lstar_bur"       => IDENTIFIER 		("lstar_bur", x_info)
            | "rstar_bur"       => IDENTIFIER 		("rstar_bur", x_info)
									
			| _  => raise RUNTIME.error( children , General.Fail("Error in case of ABSTRACT.build_abstract_tree. unknown node_type = " ^ node_type ^ "\n"), printTree, getExprInfo, printNodeInfo)
	end

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun EXPR_fromEmbedded_TREE_FORMAT in_stream end_token = 
	let
		(* ----------------------------------------------------------------------- *)
		fun get_xml_tree token =
			let
				val (node_type,node_value, x_lo, x_hi, y_lo, y_hi, label_info)  = FILE_OPERATIONS.extractXML_NodeInfo(token)
				
				val result 							           		= case node_type of
																		  "TERM"     =>	let 
																							val the_token     = FILE_OPERATIONS.getXMLToken(in_stream)
																							val the_itree     = CONCRETE.ITREE_fromEmbedded the_token in_stream 
																							val next_token    = FILE_OPERATIONS.getXMLToken(in_stream)
																						in
																							if next_token = end_token 
																							then [ TERM (the_itree, makeNodeInfo(x_lo,x_hi,y_lo,y_hi,label_info)) ]
																							else raise General.Fail("Error in ABSTRACT.fromeEmbedded_internal.\n")
																						end
																		| _          => get_xml_tree_list()
																					
				(* the end tag for this tree has been consumed by get_xml_tree_list *)
			in
				build_abstract_tree(node_type,node_value,result, makeNodeInfo(x_lo, x_hi, y_lo, y_hi, label_info))
			end
													
		and get_xml_tree_list() =
				let
					(* next_token could be begin-tree or end-tree token *)
					val next_token = FILE_OPERATIONS.getXMLToken(in_stream)
				in
					if next_token = end_token then (* we have finished collecting siblings and this tag is the close tag of the parent tree *)
						[]
						
					else (* at least one more sibling to collect *) 
						let
							val next_tree  = get_xml_tree next_token
						in
							next_tree:: get_xml_tree_list()
						end
				end;
										
		(* ----------------------------------------------------------------------- *)
		(* may not have an empty tree -- i.e., at least two tokens: <abstract ...> </abstract> *)
																
		val token  = FILE_OPERATIONS.getXMLToken(in_stream)
		val a_tree = get_xml_tree token
																
	in
	     a_tree
	end;
								
(* ------------------------------------------------------------------------------------------- *)
fun EXPR_FromXML_TREE_FORMAT(infile_str) =
	let
		val _         = print("\nReading TL program: file format = (abstract,XML).......\n");
		val in_stream = TextIO.openIn(infile_str);
        val end_token = "</abstract>"
    	val header    = FILE_OPERATIONS.getXMLToken(in_stream);
		val the_tree  = EXPR_fromEmbedded_TREE_FORMAT in_stream end_token
    	val trailer   = FILE_OPERATIONS.getXMLToken(in_stream);
   in
		TextIO.closeIn(in_stream);
        the_tree
   end
				
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun leavesToString expr flag = 
	let
		val sep       = " ";
        val comma_sep = " , ";
        val equal_sep = " = ";
								
	    (* ------------------------------------------------------------------------------------------- *)
	    fun combine( f, sep, ts )         = foldr (fn (t, str) => (f t) ^ sep ^ str) "" ts
												
        fun infixOp( f, symbol, [t1,t2] ) = f t1 ^ symbol ^ f t2
          | infixOp _                     = raise General.Fail("Error in ABSTRACT.leavesToString.infixOp.\n");
									
        fun condRule( f, [lhs,rhs,cond] ) = f lhs ^ " -> " ^ f rhs ^ " if {" ^ f cond ^ "}"
          | condRule _                    = raise General.Fail("Error in ABSTRACT.leavesToString.condRule.\n");
								
        fun breakdown( expr_list ) = 	let
											val id           = hd expr_list
											val len          = List.length expr_list
											val curried_args = tl( List.take(expr_list, len - 1) )
											val body         = List.last expr_list
										in
											(id, curried_args, body)
                                        end
	   (* ------------------------------------------------------------------------------------------- *)
	   fun traverse expr = 
			let
				val (value,expr_list, x_info) = deconstruct expr
				val x_info_str = if flag then "[" ^ CONCRETE_REPRESENTATION.nodeInfoToString( x_info ) ^ "]" else ""
			in
                sep ^ 
				(
                  case  value of
							
				      "PROG"            => "prog " ^ combine(traverse, sep, expr_list) ^ x_info_str
					| "RECURSIVE"       => "def "  ^ combine(traverse, equal_sep, expr_list)^ x_info_str
					| "NON_RECURSIVE"   => 	let
												val (id,args,body) = breakdown expr_list
																	 handle Empty => raise General.Fail("Error in ABSTRACT.leavesToString.traverse. case = NON_RECURSIVE.\n")
											in
												traverse id ^ ": " ^ combine(traverse, sep, args) ^ traverse body ^ x_info_str
											end
										  
					| "ANDALSO"         => infixOp(traverse, " ANDALSO "  , expr_list) ^ x_info_str
					| "ORELSE"          => infixOp(traverse, " ORELSE "  , expr_list) ^ x_info_str
											
					| "MATCH"           => infixOp(traverse, " = "  , expr_list) ^ x_info_str
                    | "BIND"            => infixOp(traverse, " := " , expr_list) ^ x_info_str
											
					| "CHOICE"          => infixOp(traverse, " <+> " , expr_list) ^ x_info_str
                    | "LCHOICE"         => infixOp(traverse, " <+ "  , expr_list) ^ x_info_str
                    | "RCHOICE"         => infixOp(traverse, " +> "  , expr_list) ^ x_info_str
                    | "LSEQ"            => infixOp(traverse, " <; "  , expr_list) ^ x_info_str
                    | "RSEQ"            => infixOp(traverse, " ;> "  , expr_list) ^ x_info_str
                    | "LSTAR"           => infixOp(traverse, " <* "  , expr_list) ^ x_info_str
                    | "RSTAR"           => infixOp(traverse, " *> "  , expr_list) ^ x_info_str
                                                                                                 
                    | "RULE"            => infixOp(traverse, " -> ", expr_list) ^ x_info_str
                    | "COND_RULE"       => condRule(traverse, expr_list) ^ x_info_str
                                                                                            
                    | "B_OR"            => infixOp(traverse, " || " , expr_list) ^ x_info_str
                    | "B_AND"           => infixOp(traverse, " && " , expr_list) ^ x_info_str
                                                                                       
                    | "EQ"              => infixOp(traverse, " == " , expr_list) ^ x_info_str
                    | "NEQ"             => infixOp(traverse, " != " , expr_list) ^ x_info_str
                    | "LEQ"             => infixOp(traverse, " <= " , expr_list) ^ x_info_str
                    | "LT"              => infixOp(traverse, " < "  , expr_list) ^ x_info_str
                    | "GEQ"             => infixOp(traverse, " >= " , expr_list) ^ x_info_str
                    | "GT"              => infixOp(traverse, " > "  , expr_list) ^ x_info_str
							
                    | "CONCAT"          => infixOp(traverse, " ^ "  , expr_list) ^ x_info_str
                    | "PLUS"            => infixOp(traverse, " + "  , expr_list) ^ x_info_str
                    | "MINUS"           => infixOp(traverse, " - "  , expr_list) ^ x_info_str
                    | "TIMES"           => infixOp(traverse, " * "  , expr_list) ^ x_info_str
                    | "DIVIDE"          => infixOp(traverse, " / "  , expr_list) ^ x_info_str
                    | "DIV"             => infixOp(traverse, " div ", expr_list) ^ x_info_str
                    | "MOD"             => infixOp(traverse, " mod ", expr_list) ^ x_info_str
									
                    | "APP"             => "not" ^ combine(traverse, sep,  expr_list) ^ x_info_str
                    | "ITERATOR"        => (
												traverse (getIteratorId expr_list)
												^
												"(" ^ combine(traverse, sep, getIteratorArgList(expr_list)) ^ ")"
                                           ) ^ x_info_str
											
                    | "BOOL"            => Bool.toString(getBool(expr_list))  ^ x_info_str
                    | "INT"             => Int.toString(getInt(expr_list))  ^ x_info_str
                    | "REAL"            => getReal(expr_list) ^ x_info_str
                    | "STRING"          => getString(expr_list) ^ x_info_str
                    | "IDENTIFIER"      => getIdentifier(expr_list)  ^ x_info_str
                    | "REF"             => getRef(expr_list)  ^ x_info_str
                    | "TERM"            => CONCRETE.leavesToString (getTree(expr_list)) ^ x_info_str
										
                    | "LIBRARY_CALL_0"  => traverse (getLibraryCall_0Id expr_list) ^ x_info_str
                    | "LIBRARY_CALL"    => (
                                                traverse (getLibraryCallId expr_list)
                                                ^
                                                "(" ^ combine(traverse, comma_sep, getArgList(expr_list)) ^ ")"
                                           ) ^ x_info_str
								
                    | "ID"              => "ID " ^ x_info_str
                    | "SKIP"            => "SKIP " ^ x_info_str
                    | "FAIL"            => "FAIL " ^ x_info_str
								
                    | "NOT"             => "not " ^ traverse (getUnary expr_list) ^ x_info_str
				    | "BANG"            => "! "   ^ traverse (getUnary expr_list) ^ x_info_str
	                | "TILDE"           => "~ "   ^ traverse (getUnary expr_list) ^ x_info_str 
									
	                | "TRANSIENT"       => "transient " ^ traverse (getUnary expr_list) ^ x_info_str
	                | "OPAQUE"          => "opaque "    ^ traverse (getUnary expr_list) ^ x_info_str               
	                | "RAISE"           => "raise "     ^ traverse (getUnary expr_list) ^ x_info_str
	                | "HIDE"            => "hide "      ^ traverse (getUnary expr_list) ^ x_info_str    
	                | "LIFT"            => "lift "      ^ traverse (getUnary expr_list) ^ x_info_str 
	                                 
	                | "MAPL"            => "mapL "      ^ traverse (getUnary expr_list) ^ x_info_str
	                | "MAPR"            => "mapR "      ^ traverse (getUnary expr_list) ^ x_info_str
	                | "MAPB"            => "mapB "      ^ traverse (getUnary expr_list) ^ x_info_str      
	                                        
	                | "FOLD_CHOICE"     => "fold <+> "  ^ traverse (getUnary expr_list) ^ x_info_str
	                | "FOLD_LCHOICE"    => "fold <+ "   ^ traverse (getUnary expr_list) ^ x_info_str
	                | "FOLD_RCHOICE"    => "fold +> "   ^ traverse (getUnary expr_list) ^ x_info_str
	                | "FOLD_LSEQ"       => "fold <; "   ^ traverse (getUnary expr_list) ^ x_info_str
	                | "FOLD_RSEQ"       => "fold ;> "   ^ traverse (getUnary expr_list) ^ x_info_str
	                | "FOLD_LSTAR"      => "fold <* "   ^ traverse (getUnary expr_list) ^ x_info_str
	                | "FOLD_RSTAR"      => "fold *> "   ^ traverse (getUnary expr_list) ^ x_info_str
								
                    | "FOLDS_CHOICE"    => "foldS <+>" ^ traverse (getUnary expr_list) ^ x_info_str
                    | "FOLDS_LCHOICE"   => "foldS <+"  ^ traverse (getUnary expr_list) ^ x_info_str
                    | "FOLDS_RCHOICE"   => "foldS +>"  ^ traverse (getUnary expr_list) ^ x_info_str
                    | "FOLDS_LSEQ"      => "foldS <;"  ^ traverse (getUnary expr_list) ^ x_info_str
                    | "FOLDS_RSEQ"      => "foldS ;>"  ^ traverse (getUnary expr_list) ^ x_info_str
                    | "FOLDS_LSTAR"     => "foldS <*"  ^ traverse (getUnary expr_list) ^ x_info_str
                    | "FOLDS_RSTAR"     => "foldS *>"  ^ traverse (getUnary expr_list) ^ x_info_str
							
                    | otherwise         => raise General.Fail("Error in ABSTRACT.leavesToString: internal values (e.g., UNIT) may not be processed by this function.\n")
								
				)
            end
	in
	    traverse expr
	end
																											
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun size expr = let
                    val node_count = ref 0;

                    fun inc_abstract_node_count abstract_term = (node_count := !node_count + 1; abstract_term)
                    fun inc_concrete_node_count concrete_term = (node_count := !node_count + 1; concrete_term)
                in
                    bottom_up inc_abstract_node_count inc_concrete_node_count expr;
                    !node_count
                end;

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)

fun getMain( PROG (expr_list, x_info) ) = 
		let
		    fun aux( (NON_RECURSIVE(IDENTIFIER ("main",_), strategy, _) ) :: rest ) = strategy
		      | aux( _                                                    :: rest ) = aux rest
              | aux  []                                                             = raise General.Fail("Error in ABSTRACT.getMain.aux.\n");
		in
		    aux expr_list
		end
  | getMain _                 = raise General.Fail("Error in ABSTRACT.getMain.\n");


(* ------------------------------------------------------------------------------------------- *)
fun makeTerm  ( term, x_info  ) = TERM (term, x_info);

fun unmakeTerm( TERM (term, _)) = term
  | unmakeTerm _                = raise General.Fail("Error in ABSTRACT.unmakeTerm.\n");


fun makeRef( context, id, int_option, x_info ) = REF( id, { CONTEXT = context, INDEX = int_option }, x_info )

fun getRefIndex( REF( id, ref_info, x_info ) ) = (case #INDEX ref_info of
													  SOME index => index
													| NONE       => let
																		
													                    val prefix     = "Error in ABSTRACT.getRefIndex: undefined index (i.e., NONE) for " ^ id
																		val in_context = " in context " ^ (#CONTEXT ref_info) 
																		
																		val line_low   = CONCRETE_REPRESENTATION.getLineLow( x_info )
																		val line_high  = CONCRETE_REPRESENTATION.getLineHigh( x_info )
																		val line_info  = " Line = (" ^ Int.toString(line_low) ^ "," ^ Int.toString(line_high) ^ ")" ^ "\n" 
																		val msg = prefix ^ in_context ^ line_info
													                in
																	    raise RUNTIME.error([], General.Fail(msg), printTree, getExprInfo, printNodeInfo)
                                                                    end																		
												 )
															
  | getRefIndex t                  				= raise RUNTIME.error([t], General.Fail("Error in ABSTRACT.getRefIndex: expected REF\n"), printTree, getExprInfo, printNodeInfo)
	  
(* ------------------------------------------------------------------------------------------- *)
end; (* structure *)
(* ------------------------------------------------------------------------------------------- *)
