(* ---------------------------------------------------------------------------------------------------------------------------------- *)
signature PREDEFINED_SIG =
sig
      type iterator

      val tdlbul	: iterator
      val tdl		: iterator
      val tdr		: iterator
      val tdb		: iterator
      val bul       : iterator
      val bur       : iterator
      val fix		: iterator

end;
(* ---------------------------------------------------------------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------------------------------------------------------------- *)
structure PREDEFINED : PREDEFINED_SIG =
struct

open STATE_MODEL;
open CONCRETE_REPRESENTATION;
open ABSTRACT_REPRESENTATION;

type iterator = EXPR list * ITREE * (EXPR * EXPR -> STATE) * NODE_INFO * NODE_INFO * NODE_INFO -> STATE 
									
(* ---------------------------------------------------------------------------------------------------------------------------------- *)
fun combineBroadcastStates( state::state_list) =
		let
			fun combine (state1, result) = 
				{
				    application_stack   = STACK.orStack( getApplicationStack state1, getApplicationStack result ),  
				    reduction_stack     = STACK.orStack( getReductionStack   state1, getReductionStack   result ), 
									
				    strategy            = [SKIP(dummy_node_info)],  (* not well-defined at this time *)
				  				                                                                              
				    first_order_result  = (getFirstOrderResult result) @ (getFirstOrderResult state1), 
				    higher_order_result = buildHigherOrderReturned(result, state1)
				}
		in
		    foldl combine state state_list
		end
																	
  | combineBroadcastStates [] = {
				    application_stack   = STACK.FALSE_STACK,
				    reduction_stack     = STACK.FALSE_STACK,
				    strategy            = [SKIP(dummy_node_info)],
				  				                                                                              
				    first_order_result  = [],
				    higher_order_result = []
				}
													
(* ---------------------------------------------------------------------------------------------------------------------------------- *)
(*
fun combineThreadedStates(state_01, state_02) = 

			{
			    application_stack   = STACK.orStack( getApplicationStack state_01, getApplicationStack state_02 ),  
			    reduction_stack     = STACK.orStack( getReductionStack   state_01, getReductionStack   state_02 ), 
									
			    strategy            = getSingleStrategy state_02,  (* thread strategy *)
				  				                                                                              
			    first_order_result  = [], (* composing this value really does not make sense *)
			    higher_order_result = buildHigherOrderReturned(state_01, state_02)
			}
*)				
fun combineThreadedStates
   (
		{ application_stack = appStack1, reduction_stack = redStack1, strategy = strat1, first_order_result = firstOrder1, higher_order_result = higherOrder1 },
		{ application_stack = appStack2, reduction_stack = redStack2, strategy = strat2, first_order_result = firstOrder2, higher_order_result = higherOrder2 }		
	) = 
		let
			fun buildHigherOrderReturned() =
				let
					fun eqListSKIP( []                   ) 	= true
					  | eqListSKIP( (SKIP _) :: rest ) 		= eqListSKIP rest
					  | eqListSKIP _                   		= false
															
					val flag1         = eqListSKIP higherOrder1
					val flag2         = eqListSKIP higherOrder2
				in
						 if flag1 andalso flag2 then []
					else if flag1               then higherOrder2
					else if flag2               then higherOrder1
					else                             higherOrder1 @ higherOrder2
				end;
		in
			{
			    application_stack   = STACK.orStack( appStack1, appStack2 ),  
			    reduction_stack     = STACK.orStack( redStack1, redStack2 ), 
									
			    strategy            = strat2,  (* thread strategy *)
				  				                                                                              
			    first_order_result  = [], (* composing this value really does not make sense *)
			    higher_order_result = buildHigherOrderReturned()
			}
		end
			
(* ---------------------------------------------------------------------------------------------------------------------------------- *)
fun deconstruct( itree( node, children ) ) = (node, children)
																
(* ---------------------------------------------------------------------------------------------------------- *)
fun mapL f xs = let
                   fun aux (y::ys) = f y :: aux ys  
                     | aux []      = []
                in
                   aux xs
                end
												
(* ---------------------------------------------------------------------------------------------------------- *)
fun mapR f xs = let
                   fun aux (y::ys) = f y :: aux ys
                     | aux []      = []
                in
                   List.rev( aux (List.rev xs) )
                end
																				
(* ---------------------------------------------------------------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------------------------------------------------------------- *)
fun tdl_Broadcast(strategy, input_tree, apply, x_info_iterator, x_info_id, x_info_tree ) = 
		let
			(* ---------------------------------------------------------------------------------------------------------- *)
			fun identity x = x;

                        (* this will not work for references that are recursively defined *)
			fun applyLookup (REF x) = 	let
                                            val s = STORE.lookup (REF x)
                                        in
                                            reduceToValue s
                                        end
			  | applyLookup expr    = expr

			and reduceToValue s = ABSTRACT.bottom_up applyLookup identity strategy

			(* ---------------------------------------------------------------------------------------------------------- *)
			val initial_state = {

					      application_stack   = STACK.FALSE_STACK,
					      reduction_stack     = STACK.FALSE_STACK,
					      strategy            = [reduceToValue strategy], (* it does not make sense to broadcast strategies containing references *)
				  				                                                                              
					      first_order_result  = [],
					      higher_order_result = []
					   }
										
			(* ---------------------------------------------------------------------------------------------------------- *)
			fun aux s tree0 = 
					let
			   		    val state1              = apply (s , TERM (tree0, x_info_tree))
					    val (node1,children1) 	= deconstruct (ABSTRACT.unmakeTerm( getTerm state1))
			   		    val state_list      	= map (aux (getSingleStrategy state1)) children1
                        val state2    		    = combineBroadcastStates( state_list )
                        val children2           = map ABSTRACT.unmakeTerm (getFirstOrderResult state2)
			   		in
					    {
						    application_stack   = STACK.orStack( getApplicationStack state1, getApplicationStack state2 ),  
						    reduction_stack     = STACK.orStack( getReductionStack   state1, getReductionStack   state2 ), 
									
						    strategy            = [SKIP (dummy_node_info)],  (* not well-defined at this time *)
				  				                                                                              
						    first_order_result  = [ TERM ( itree(node1, children2), x_info_tree ) ],
						    higher_order_result = buildHigherOrderReturned(state1, state2)
					   }
			   		end
			(* ---------------------------------------------------------------------------------------------------------- *)
		in
			aux (reduceToValue strategy) input_tree 
		end
																	
(* ---------------------------------------------------------------------------------------------------------------------------------- *)
fun topDownBottomUp(traversal_id, strategyTD, strategyBU, input_tree, apply, mapFun, x_info_id, x_info_iterator, x_info_tree ) = 
		let
			(* ---------------------------------------------------------------------------------------------------------- *)
			val state  = ref {
								application_stack   = STACK.FALSE_STACK,
								reduction_stack     = STACK.FALSE_STACK,
								strategy            = [strategyTD,strategyBU],
				  				                                                                              
								first_order_result  = [],
								higher_order_result = []
						     } : STATE ref;

			(* ---------------------------------------------------------------------------------------------------------- *)
			fun insertBU strategyBU (state : STATE) = 
				let
                    fun insertSecond [strategyTD] = [strategyTD,strategyBU]
                      | insertSecond _            = raise General.Fail("Error in predefined.topDownBottomUp.insertBU.\n")
				in
					{
                        application_stack   = #application_stack state,
                        reduction_stack     = #reduction_stack state,
                        strategy            = insertSecond (#strategy state),
                        first_order_result  = #first_order_result state,
                        higher_order_result = #higher_order_result state
					} 
				end

			(* ---------------------------------------------------------------------------------------------------------- *)
			fun insertTD strategyTD (state : STATE) = 
				let
                    fun insertFirst [strategyBU] = [strategyTD,strategyBU]
                      | insertFirst _            = raise General.Fail("Error in predefined.topDownBottomUp.insertTD.\n")
				in
					{
					      application_stack   = #application_stack state,
                          reduction_stack     = #reduction_stack state,
                          strategy            = insertFirst (#strategy state),
                          first_order_result  = #first_order_result state,
                          higher_order_result = #higher_order_result state                          
					} 
				end
                
			(* ---------------------------------------------------------------------------------------------------------- *)
			fun applyTD t = 
				let
					val state0                  = !state
					val [strategyTD,strategyBU] = getDualStrategy state0 
																		
					val state1   = apply( strategyTD,TERM (t, x_info_tree) )
                    val state1'  = insertBU strategyBU state1
					val the_tree = ABSTRACT.unmakeTerm( getTerm state1' )
				in
					state := combineThreadedStates(state0, state1');
					the_tree 
				end

			(* ---------------------------------------------------------------------------------------------------------- *)
			fun applyBU t = 
				let
					val state0                  = !state
					val [strategyTD,strategyBU] = getDualStrategy state0 
																		
					val state1   = apply( strategyBU,TERM (t, x_info_tree) )
                    val state1'  = insertTD strategyTD state1
					val the_tree = ABSTRACT.unmakeTerm( getTerm state1' )
				in
					state := combineThreadedStates(state0, state1');
					the_tree 
				end
                
			(* ---------------------------------------------------------------------------------------------------------- *)
			fun aux t1 = 	
					let
						val (node2,children2) = deconstruct( applyTD t1 )
						
                        val children3         = mapFun aux children2
                        val t3                = itree(node2,children3)
                        
                        val (node4,children4) = deconstruct( applyBU t3 )
					in
						itree(node4, children4)
					end
                                                                          
			(* ---------------------------------------------------------------------------------------------------------- *)

			val final_tree  = aux input_tree;
			val final_state = !state
		in
			{
			   application_stack   = getApplicationStack  final_state,
			   reduction_stack     = getReductionStack    final_state,
			   strategy            = [ITERATOR(IDENTIFIER (traversal_id, x_info_id), getDualStrategy final_state, x_info_iterator)],  
				  				                                                                              
			   first_order_result  = [TERM (final_tree, x_info_tree)],
			   higher_order_result = getHigherOrderResult final_state
			} 
		end

(* ---------------------------------------------------------------------------------------------------------------------------------- *)
fun topdown(traversal_id, strategy, input_tree, apply, mapFun, x_info_id, x_info_iterator, x_info_tree ) = 
		let
			(* ---------------------------------------------------------------------------------------------------------- *)
			val state  = ref {
								application_stack   = STACK.FALSE_STACK,
								reduction_stack     = STACK.FALSE_STACK,
								strategy            = [strategy],
				  				                                                                              
								first_order_result  = [],
								higher_order_result = []
						     } : STATE ref;
																		
			(* ---------------------------------------------------------------------------------------------------------- *)
			fun applyWrapper t = 
				let
					val state0   = !state
					val s        = getSingleStrategy state0 
																		
					val state1   = apply( s,TERM (t, x_info_tree) )
					val the_tree = ABSTRACT.unmakeTerm( getTerm state1 )
				in
					state := combineThreadedStates(state0, state1);
					the_tree 
				end
																
			(* ---------------------------------------------------------------------------------------------------------- *)
			fun aux t1 = 	
					let
						val (node2,children2) = deconstruct( applyWrapper t1 )
						val children3         = mapFun aux children2
					in
						itree(node2, children3)
					end
                                                                          
			(* ---------------------------------------------------------------------------------------------------------- *)

			val final_tree  = aux input_tree;
			val final_state = !state
		in
			{
			   application_stack   = getApplicationStack  final_state,
			   reduction_stack     = getReductionStack    final_state,
			   strategy            = [ITERATOR(IDENTIFIER (traversal_id, x_info_id), [getSingleStrategy final_state], x_info_iterator)],  
				  				                                                                              
			   first_order_result  = [TERM (final_tree, x_info_tree)],
			   higher_order_result = getHigherOrderResult final_state
			} 
		end
        
(* ---------------------------------------------------------------------------------------------------------------------------------- *)
fun bottomup(traversal_id, strategy, input_tree, apply, mapFun, x_info_id, x_info_iterator, x_info_tree ) = 
		let
			(* ---------------------------------------------------------------------------------------------------------- *)
			val state  = ref {
								application_stack   = STACK.FALSE_STACK,
								reduction_stack     = STACK.FALSE_STACK,
								strategy            = [strategy],
				  				                                                                              
								first_order_result  = [],
								higher_order_result = []
							 } : STATE ref;
														
			(* ---------------------------------------------------------------------------------------------------------- *)
			fun applyWrapper t = 
				let
					val state0   = !state
					val s        = getSingleStrategy state0 
														
					val state1   = apply(s,TERM (t, x_info_tree) )
								   
					val the_tree = ABSTRACT.unmakeTerm( getTerm state1 )
					
				in
					state := combineThreadedStates(state0, state1);
					the_tree 
				end
																		
			(* ---------------------------------------------------------------------------------------------------------- *)
			fun aux (t1 as itree( node1, children1 )) = 	
				let
			   	    val children2	= 	mapFun aux children1
			   	in
					applyWrapper (itree(node1, children2))
			   	end
									
			(* ---------------------------------------------------------------------------------------------------------- *)
			val final_tree  = aux input_tree;
			val final_state = !state
		in
			{
				application_stack   = getApplicationStack  final_state,
				reduction_stack     = getReductionStack    final_state,
				strategy            = [ITERATOR(IDENTIFIER (traversal_id, x_info_iterator), [getSingleStrategy final_state], x_info_iterator)],  
				  				                                                                              
				first_order_result  = [TERM (final_tree, x_info_tree)],
				higher_order_result = getHigherOrderResult final_state
			} 
		end
															
(* ---------------------------------------------------------------------------------------------------------------------------------- *)
(* ---------------------------------------------------------------------------------------------------------------------------------- *)
fun tdlbul([strategyTD, strategyBU], input_tree, apply, x_info_id, x_info_iterator, x_info_tree ) = topDownBottomUp("TdlBul", strategyTD, strategyBU, input_tree, apply, mapL, x_info_id, x_info_iterator, x_info_tree )
fun tdl([strategy], input_tree, apply, x_info_id, x_info_iterator, x_info_tree ) = topdown("TDL", strategy, input_tree, apply, mapL, x_info_id, x_info_iterator, x_info_tree )
fun tdr([strategy], input_tree, apply, x_info_id, x_info_iterator, x_info_tree ) = topdown("TDR", strategy, input_tree, apply, mapR, x_info_id, x_info_iterator, x_info_tree )
fun tdb([strategy], input_tree, apply, x_info_id, x_info_iterator, x_info_tree ) = tdl_Broadcast( strategy, input_tree, apply,       x_info_id, x_info_iterator, x_info_tree )
																								
fun bul([strategy], input_tree, apply, x_info_id, x_info_iterator, x_info_tree ) = bottomup("BUL", strategy, input_tree, apply, mapL, x_info_id, x_info_iterator, x_info_tree )
fun bur([strategy], input_tree, apply, x_info_id, x_info_iterator, x_info_tree ) = bottomup("BUR", strategy, input_tree, apply, mapR, x_info_id, x_info_iterator, x_info_tree )
																				
(* ---------------------------------------------------------------------------------------------------------------------------------- *)
fun fix([strategy], input_tree, apply, x_info_iterator, x_info_id, x_info_tree) =
			let
				(* ---------------------------------------------------------------------------------------------------------- *)
				val state  =  {
								application_stack   = STACK.FALSE_STACK,
								reduction_stack     = STACK.FALSE_STACK,
								strategy            = [strategy],
				  				                                                                              
								first_order_result  = [TERM (input_tree, x_info_tree)],
								higher_order_result = []
							  };
						
				(* ---------------------------------------------------------------------------------------------------------- *)
				fun auxFIX state0 = 
					let
						val state1   = apply(getSingleStrategy state0,getTerm state0)
					in
						if state0 = state1 then state1
						else auxFIX state1
					end
				(* ---------------------------------------------------------------------------------------------------------- *)
				val final_state = auxFIX state
			in
				{
				   application_stack   = getApplicationStack  final_state,
				   reduction_stack     = getReductionStack    final_state,
				   strategy            = [ITERATOR(IDENTIFIER ("FIX", x_info_id), [getSingleStrategy final_state], x_info_iterator)],  (* ? or original s ? *)
				  				                                                                              
				   first_order_result  = getFirstOrderResult  final_state,
				   higher_order_result = getHigherOrderResult final_state
				} 
			end
(* ------------------------------------------------------------------------------------------- *)
end;  (* struct *)
(* ------------------------------------------------------------------------------------------- *)