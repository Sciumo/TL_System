

(* ------------------------------------------------------------------------------------------- *)
signature INTERFACE_SIG =
sig
	val transform					: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR
									  -> 
									  ABSTRACT_REPRESENTATION.EXPR
									
    val toXML_FileFormat			: string * string * ABSTRACT_REPRESENTATION.EXPR -> unit
								
    val printTree    				: ABSTRACT_REPRESENTATION.EXPR -> unit
				
end;
(* ------------------------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
functor INTERFACE_FN(
  			structure UserDefinedFunctions :
			  sig
					val setTargetParser		: (string -> CONCRETE_REPRESENTATION.ITREE) -> unit;
					val setDomainFolder 	: string -> unit;
					val setTargetFileName 	: string -> unit;
					val setTargetExtension 	: string -> unit;
					
			        val functions : 	(
											string 
											* 
											(
												(ABSTRACT_REPRESENTATION.EXPR list * ABSTRACT_REPRESENTATION.EXPR list) list 
												-> 
												ABSTRACT_REPRESENTATION.EXPR
											)
										) list;
			  end
											
		 ):INTERFACE_SIG =
struct
(* ------------------------------------------------------------------------------------------- *)

structure SEMANTICS = SEMANTICS_FN(structure UserDefined = UserDefinedFunctions)


(* ------------------------------------------------------------------------------------------- *)
fun getStrategy(tl_prog_str) = ABSTRACT.getMain(
								 ABSTRACT.EXPR_FromXML_TREE_FORMAT( tl_prog_str )
                               );

fun getAbstractTerm( term_str ) = ABSTRACT.makeTerm(
									CONCRETE.ITREE_fromFile(term_str) 
									,
									CONCRETE_REPRESENTATION.dummy_node_info  (* the target program has no "position" in the tlp program *)
                                  );
																
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun toXML_FileFormat  ( file_name, term_name, a_tree ) = ABSTRACT.EXPR_toXML		    ( file_name, term_name, a_tree )
				
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun printTree term = ABSTRACT.printTree term;

(* ------------------------------------------------------------------------------------------- *)
fun metricsToFile(pathname) =
				let
					val out_stream = TextIO.openOut(pathname);
				in
   					print("\n Data being written to: " ^ pathname ^ "\n");
									
					TextIO.output(out_stream,"\n nodes_visited  = "  ^ Int.toString(0)) ; 
					TextIO.output(out_stream,"\n rule_count     = "  ^ Int.toString(0)) ; 
					TextIO.output(out_stream,"\n rule_attempts  = "  ^ Int.toString(0)) ; 
					TextIO.output(out_stream,"\n match_count    = "  ^ Int.toString(0)) ; 
					TextIO.output(out_stream,"\n match_attempts = "  ^ Int.toString(0)) ; 
					TextIO.output(out_stream,"\n cast_count     = "  ^ Int.toString(0)) ; 
					TextIO.output(out_stream,"\n cast_attempts  = "  ^ Int.toString(0)) ; 
                                        
                    TextIO.closeOut(out_stream)
				end;

(* ------------------------------------------------------------------------------------------------------ *)
(* ------------------------------------------------------------------------------------------- *)
fun transform( strategy, term ) = 
					let
						val _      = METRICS.setStartTime();
						val result = SEMANTICS.applyMain( strategy, term )
						val _      = METRICS.printMetrics();
					in
						result
					end;

(* ------------------------------------------------------------------------------------------- *)
end;  (* struct *)
(* ------------------------------------------------------------------------------------------- *)