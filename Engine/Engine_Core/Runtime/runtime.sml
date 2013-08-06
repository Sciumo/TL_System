(* ------------------------------------------------------------------------------------------- *)
signature RUNTIME_SIG =
sig
 	val error	: 	ABSTRACT_REPRESENTATION.EXPR list 
					* 
					exn 
					*
					(ABSTRACT_REPRESENTATION.EXPR -> 'a) 
					*
					(ABSTRACT_REPRESENTATION.EXPR -> CONCRETE_REPRESENTATION.NODE_INFO) 
					*
					(CONCRETE_REPRESENTATION.NODE_INFO -> 'b)
					-> 
					'c
end;
(* ------------------------------------------------------------------------------------------- *)
																			
(* ------------------------------------------------------------------------------------------- *)
structure RUNTIME : RUNTIME_SIG =
struct
																						
(* ------------------------------------------------------------------------------------------- *)
fun error(term_list, ex, f_printExpr, f_getExprInfo, f_printNodeInfo) =
				let
				    fun output term = (
										print("\n\n++++++++++++++++++++++++++++++++++++++++++++++++++\n\n");
										f_printExpr term
									  )
									  
					fun range (x_info :: x_info_list) = foldr CONCRETE_REPRESENTATION.mergeNodeInfo x_info x_info_list 
					  | range ( [] )                  = CONCRETE_REPRESENTATION.dummy_node_info
					
					val the_info = range (map f_getExprInfo term_list)
				in 
					print("\n\nA runtime type error has been detected.\n");
					(* map output term_list; -- when debugging *)
output (hd term_list);											
					f_printNodeInfo the_info;
					raise ex
				end
																						
(* ------------------------------------------------------------------------------------------- *)
end;  (* struct *)
(* ------------------------------------------------------------------------------------------- *)