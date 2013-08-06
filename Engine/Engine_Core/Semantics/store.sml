(* ------------------------------------------------------------------------------------------- *)
signature STORE_SIG =
sig
      val lookup		: ABSTRACT_REPRESENTATION.EXPR -> ABSTRACT_REPRESENTATION.EXPR
      val update		: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR -> unit
										
end;
(* ------------------------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------------------------- *)
structure STORE : STORE_SIG =
struct

(* ------------------------------------------------------------------------------------------- *)

val the_store = ref [] : (int * ABSTRACT_REPRESENTATION.EXPR) list ref;

fun lookup( ref_term ) = let
                             val index = ABSTRACT.getRefIndex ref_term

                             fun aux( (index1,value1)::rest ) = if index = index1 then value1 else aux(rest)
                               | aux []                       = raise RUNTIME.error([ref_term], General.Fail("Error in STORE.lookup.aux: store_ref used before assigned\n"),
							                                                        ABSTRACT.printTree, ABSTRACT.getExprInfo, CONCRETE_REPRESENTATION.printNodeInfo)
                      in
                           aux( !the_store )
                      end

fun update( ref_term, strategic_expression ) = 
						let
						    val index = ABSTRACT.getRefIndex( ref_term )
										
                            fun aux((index1, value1) :: rest ) = if index = index1 then (index1, strategic_expression) :: rest
                                                                                   else (index1, value1) :: aux rest
									
                              | aux []                         = [(index, strategic_expression)]
						in
							the_store := aux( !the_store )
						end
(* ------------------------------------------------------------------------------------------- *)
end;  (* struct *)
(* ------------------------------------------------------------------------------------------- *)