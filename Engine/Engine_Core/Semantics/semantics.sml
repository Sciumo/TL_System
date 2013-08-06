

(* ------------------------------------------------------------------------------------------- *)
signature SEMANTICS_SIG =
sig
 	val applyMain	: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR -> ABSTRACT_REPRESENTATION.EXPR

end;
(* ------------------------------------------------------------------------------------------- *)
(*

  This is the tuple that is being manipulated.

   ( 
      application stack -- controls strategic application  { <+, +>, <;, ;>, <*, *>, hide, lift }
      reduction stack   -- controls strategic reduction    { transient, opaque, raise }
      strategy          -- this is the current form of the *object strategy*. The *object strategy* is
                           the strategy that is being applied (e.g., lhs of application operator).

      first_order_result  -- In a first-order application this position in the tuple contains the
                             computed answer (and the higher-order position should be empty).
 
      higher_order_result -- In a higher-order application this position in the tuple contains
                             the computed answer (and the first-order position should be empty).

   )


The primary behavior here is *strategy application*. Application can occur within two distinct contexts:
first-order and higher-order. In a first-order context, the result of application is a term. In a 
higher-order context, the result of application is a strategy list. 

It can be statically determined whether a given application is first-order or higher-order. Let s 
denote a strategy, let t, t1, t2 denote terms, let X denote a schema variable and let f denote 
an identifier.

Initial Application Contexts

        main( parse_tree )  this is required to be first-order
                             
	<X>_1 = s t         is a first-order application of s to t.    
                                 
	f = s t             is a higher-order application of s to t.    


Decompostion of Application Contexts

        (s1 t1)(s2 t2)      The application of s1 to t1 is higher-order and the application 
                            of s2 to t2 is first-order.
                           


A heterogeneous application can arise when a higher-order strategy is applied to
a term in a first-order context. In a heterogeneous application, the result of 
application may be a term and/or a strategy. The strategic result (if present) 
should be folded into the *object strategy*. This fold needs to be eplicit in the
source program.



*)

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
functor SEMANTICS_FN (
    structure UserDefined :
        sig
            val functions : (
                                string
                                *
                                (
                                    (ABSTRACT_REPRESENTATION.EXPR list * ABSTRACT_REPRESENTATION.EXPR list) list
                                    ->
                                    ABSTRACT_REPRESENTATION.EXPR
                                )
                            ) list;
        end
) : SEMANTICS_SIG =
struct

open CONCRETE_REPRESENTATION;
open ABSTRACT_REPRESENTATION;
open STATE_MODEL;

(* ------------------------------------------------------------------------------------------- *)
fun filter_rev( (TERM (term, _) ):: rest, acc ) = filter_rev(rest, term::acc)
  | filter_rev( []                      , acc ) = acc
  | filter_rev _                                = raise General.Fail("Error in SEMANTICS.filter_rev.\n");
																						
(* ------------------------------------------------------------------------------------------- *)
fun filter( (TERM (term, _)):: rest ) = term :: filter rest
  | filter( []                      ) = []
  | filter _                          = raise General.Fail("Error in SEMANTICS.filter.\n");
																	
(* ------------------------------------------------------------------------------------------- *)
fun composeThreadedState( []      , state  ) = [ state ]
  | composeThreadedState( [ acc ] , state  ) = [
													{
														application_stack   = STACK.orStack( getApplicationStack acc, getApplicationStack state ),  
														reduction_stack     = STACK.orStack( getReductionStack   acc, getReductionStack   state ), 
														strategy            = [getSingleStrategy state],  (* threaded *)
					  				                                                                              
														first_order_result  = (getTerm state) :: (getFirstOrderResult acc),  (* this more efficient composition produces a reversed list *)
														higher_order_result = buildHigherOrderReturned(acc, state)
													}	
												] 
																						
   | composeThreadedState _ = raise General.Fail("Error in SEMANTICS.composeThreadedState\n");
																						
(* ------------------------------------------------------------------------------------------- *)
fun lookupSML(f_id, function_list, x_info ) = 	
					let
					    fun aux(  (g_id, body)::rest ) = if f_id = g_id then body else aux rest
                          | aux []                     = let
															val msg = "Error in SEMANTICS.lookupSML.aux.\nCannot find: " ^ f_id
														 in
															print(msg ^ "\n");
															RUNTIME.error([ IDENTIFIER (f_id, x_info) ], General.Fail(msg), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
														 end
					in
					    aux function_list
					end
																		
(* ------------------------------------------------------------------------------------------- *)
fun unsuccessfulApp (t, x_info) =
			{
			   application_stack   = STACK.FALSE_STACK,
			   reduction_stack     = STACK.FALSE_STACK,
			   strategy            = [SKIP (x_info)],
				  				                                                                              
			   first_order_result  = [t],
			   higher_order_result = []
			}
																
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(* the objective of apply is to apply a strategy to a term and return a state record           *)
(* ------------------------------------------------------------------------------------------- *)
fun apply( rule as RULE( lhs, rhs, x_info ), term ) = 

						let
							val _            = METRICS.ruleApplicationAttempt() 
                            val sigma        = MATCHING.match(lhs,term, SOME [] )
                        in
                            if isSome(sigma) andalso METRICS.ruleApplicationSuccess()  
						    then   
							   let
                                    (* recall that the application of a heterogeneous strategy to a term may yield either
                                       a strategy as a result, a term as a result, or both as a result.
                                    *)
                                    val (possible_result,strategy_result) = reduce(MATCHING.subst(sigma, rhs))
                                    val term_result                       = if null possible_result then [ term ] else possible_result
							   in
                                                                         { 
                                                                            application_stack   = STACK.TRUE_STACK , 
                                                                            reduction_stack     = STACK.TRUE_STACK , 
                                                                            strategy            = [rule]           ,
                                                                               
                                                                            first_order_result  = term_result      , 
                                                                            higher_order_result = strategy_result              
                                                                          } 
							   end
                                                                             
                            else (* identity-based semantics *)
                                                                         { 
                                                                            application_stack   = STACK.FALSE_STACK , 
                                                                            reduction_stack     = STACK.FALSE_STACK ,  
                                                                            strategy            = [rule]            , 
                                                                                                         
                                                                            first_order_result  = [term]            ,
                                                                            higher_order_result = []    
                                                                          } 
                        end
																						
  | apply( rule as COND_RULE( lhs, rhs, cond, x_info ), term ) = 

						let
							val _      = METRICS.ruleApplicationAttempt() 
                            val sigma0 = MATCHING.match(lhs,term, SOME [])
                            val sigma  = eval(cond, sigma0)
                        in
                            if isSome(sigma) andalso METRICS.ruleApplicationSuccess() 
						    then 
							let
                                val (possible_result,strategy_result) = reduce(MATCHING.subst(sigma, rhs))
                                val term_result                       = if null possible_result then [ term ] else possible_result
							in
                                                                         { 
                                                                            application_stack   = STACK.TRUE_STACK , 
                                                                            reduction_stack     = STACK.TRUE_STACK , 
                                                                            strategy            = [rule]           ,
                                                                               
                                                                            first_order_result  = term_result      ,
                                                                            higher_order_result = strategy_result              
                                                                          } 
							end
                                                                             
                                                    else (* identity-based semantics *)
                                                                          { 
                                                                            application_stack   = STACK.FALSE_STACK , 
                                                                            reduction_stack     = STACK.FALSE_STACK ,  
                                                                            strategy            = [rule]            , 
                                                                                                         
                                                                            first_order_result  = [ term ]          ,
                                                                            higher_order_result = []
                                                                          } 
                                                end
																									
(* ------------------------------------------------------------------------------------------- *)
  | apply( ITERATOR(IDENTIFIER (any, _), [SKIP(_)], x_info ), t ) = unsuccessfulApp(t, x_info)
																								
(* ------------------------------------------------------------------------------------------- *)
  | apply( ITERATOR(IDENTIFIER ("FIX", x_info_id), [s], x_info_iterator ), TERM (input_tree, x_info_tree)  ) = PREDEFINED.fix([s], input_tree, apply, x_info_id, x_info_iterator, x_info_tree)
	
  | apply( ITERATOR(IDENTIFIER ("TdlBul", x_info_id), [sTD,sBU], x_info_iterator ), TERM (input_tree, x_info_tree)  ) = PREDEFINED.tdlbul([sTD, sBU], input_tree, apply, x_info_id, x_info_iterator, x_info_tree)    
  | apply( ITERATOR(IDENTIFIER ("TDL", x_info_id), [s], x_info_iterator ), TERM (input_tree, x_info_tree)  ) = 
  
  					let
						val (_, s_reduced_list) = reduce(s)
						val s_reduced = hd s_reduced_list 
										handle Empty => RUNTIME.error([s], General.Fail("Error in SEMANTICS.apply. Case: TDL\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					in
						PREDEFINED.tdl([s_reduced], input_tree, apply, x_info_id, x_info_iterator, x_info_tree)
					end

  | apply( ITERATOR(IDENTIFIER ("TDR", x_info_id), [s], x_info_iterator ), TERM (input_tree, x_info_tree)  ) = PREDEFINED.tdr([s], input_tree, apply, x_info_id, x_info_iterator, x_info_tree)
  | apply( ITERATOR(IDENTIFIER ("TD" , x_info_id), [s], x_info_iterator ), TERM (input_tree, x_info_tree)  ) = PREDEFINED.tdb([s], input_tree, apply, x_info_id, x_info_iterator, x_info_tree)
																								
  | apply( ITERATOR(IDENTIFIER ("BUL", x_info_id), [s], x_info_iterator ), TERM (input_tree, x_info_tree)  ) = PREDEFINED.bul([s], input_tree, apply, x_info_id, x_info_iterator, x_info_tree)      
  | apply( ITERATOR(IDENTIFIER ("BUR", x_info_id), [s], x_info_iterator ), TERM (input_tree, x_info_tree)  ) = PREDEFINED.bur([s], input_tree, apply, x_info_id, x_info_iterator, x_info_tree)
																						
(* ------------------------------------------------------------------------------------------- *)
  | apply( ITERATOR(IDENTIFIER ( "cond_tdl", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_CHOICE ( ITERATOR(IDENTIFIER ("TDL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("lcond_tdl", x_info_id), [s], x_info_iterator), term ) = 
					let
						val (_, s_reduced_list) = reduce(s)
						val s_reduced = hd s_reduced_list 
										handle Empty => RUNTIME.error([s], General.Fail("Error in SEMANTICS.apply. Case: lcond_tdl\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					in
						apply( FOLD_LCHOICE( ITERATOR(IDENTIFIER ("TDL", x_info_id), [s_reduced], x_info_iterator), x_info_iterator ), term ) 
					end
  | apply( ITERATOR(IDENTIFIER ("rcond_tdl", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RCHOICE( ITERATOR(IDENTIFIER ("TDL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ( "lseq_tdl", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LSEQ   ( ITERATOR(IDENTIFIER ("TDL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ( "rseq_tdl", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RSEQ   ( ITERATOR(IDENTIFIER ("TDL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("lstar_tdl", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LSTAR  ( ITERATOR(IDENTIFIER ("TDL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("rstar_tdl", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RSTAR  ( ITERATOR(IDENTIFIER ("TDL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
																																											
  | apply( ITERATOR(IDENTIFIER ( "cond_tdr", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_CHOICE ( ITERATOR(IDENTIFIER ("TDR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("lcond_tdr", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LCHOICE( ITERATOR(IDENTIFIER ("TDR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("rcond_tdr", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RCHOICE( ITERATOR(IDENTIFIER ("TDR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ( "lseq_tdr", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LSEQ   ( ITERATOR(IDENTIFIER ("TDR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ( "rseq_tdr", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RSEQ   ( ITERATOR(IDENTIFIER ("TDR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("lstar_tdr", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LSTAR  ( ITERATOR(IDENTIFIER ("TDR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("rstar_tdr", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RSTAR  ( ITERATOR(IDENTIFIER ("TDR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
																																													
  | apply( ITERATOR(IDENTIFIER ( "cond_bul", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_CHOICE ( ITERATOR(IDENTIFIER ("BUL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("lcond_bul", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LCHOICE( ITERATOR(IDENTIFIER ("BUL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("rcond_bul", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RCHOICE( ITERATOR(IDENTIFIER ("BUL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ( "lseq_bul", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LSEQ   ( ITERATOR(IDENTIFIER ("BUL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ( "rseq_bul", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RSEQ   ( ITERATOR(IDENTIFIER ("BUL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("lstar_bul", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LSTAR  ( ITERATOR(IDENTIFIER ("BUL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("rstar_bul", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RSTAR  ( ITERATOR(IDENTIFIER ("BUL", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
																																							
  | apply( ITERATOR(IDENTIFIER ( "cond_bur", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_CHOICE ( ITERATOR(IDENTIFIER ("BUR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("lcond_bur", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LCHOICE( ITERATOR(IDENTIFIER ("BUR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("rcond_bur", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RCHOICE( ITERATOR(IDENTIFIER ("BUR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ( "lseq_bur", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LSEQ   ( ITERATOR(IDENTIFIER ("BUR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ( "rseq_bur", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RSEQ   ( ITERATOR(IDENTIFIER ("BUR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("lstar_bur", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_LSTAR  ( ITERATOR(IDENTIFIER ("BUR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
  | apply( ITERATOR(IDENTIFIER ("rstar_bur", x_info_id), [s], x_info_iterator), term ) = apply( FOLD_RSTAR  ( ITERATOR(IDENTIFIER ("BUR", x_info_id), [s], x_info_iterator), x_info_iterator ), term ) 
																									
(* ------------------------------------------------------------------------------------------- *)
  | apply( FOLDS_CHOICE  (s, x_info), term ) =
						let
							(* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLDS_CHOICE( heteroFoldFromLeft("CHOICE", state, x_info), x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = []
						    }
						end
											
  | apply( FOLD_CHOICE  (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLD_CHOICE( getSingleStrategy state, x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = foldStrategyList("CHOICE", state, x_info)
						    }
						end
																		
  | apply( FOLDS_LCHOICE  (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term) 
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLDS_LCHOICE( heteroFoldFromLeft("LCHOICE", state, x_info), x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = []
						    }
						end
																					
  | apply( FOLD_LCHOICE (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
							val x_info_s = ABSTRACT.getExprInfo s
						    val state = apply(s,term) 
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLD_LCHOICE( getSingleStrategy state, x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = foldStrategyList("LCHOICE", state, x_info_s)
						    }
						end
																		
  | apply( FOLDS_RCHOICE  (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLDS_RCHOICE( heteroFoldFromLeft("RCHOICE", state, x_info), x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = []
						    }
						
						end
																								
  | apply( FOLD_RCHOICE (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
								strategy            = [FOLD_RCHOICE( getSingleStrategy state, x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = foldStrategyList("RCHOICE", state, x_info)
						    }
						end
																				
  | apply( FOLDS_LSEQ  (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state          = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLDS_LSEQ( heteroFoldFromLeft("LSEQ", state, x_info), x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = []
						    }
						end
																
  | apply( FOLD_LSEQ    (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLD_LSEQ( getSingleStrategy state, x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = foldStrategyList("LSEQ", state, x_info)
						    }
						end
																
  | apply( FOLDS_RSEQ  (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLDS_RSEQ( heteroFoldFromLeft("RSEQ", state, x_info), x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = []
						    }
						end
																		
  | apply( FOLD_RSEQ    (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLD_RSEQ( getSingleStrategy state, x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = foldStrategyList("RSEQ", state, x_info)
						    }
						end
																	
  | apply( FOLDS_LSTAR  (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLDS_LSTAR( heteroFoldFromLeft("LSTAR", state, x_info), x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = []
						    }
						end
																				
  | apply( FOLD_LSTAR   (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLD_LSTAR( getSingleStrategy state, x_info )],
                                                                                 
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = foldStrategyList("LSTAR", state, x_info)
						    }
						end
																				
  | apply( FOLDS_RSTAR  (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLDS_RSTAR( heteroFoldFromLeft("RSTAR", state, x_info), x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = []
						    }
						end
																		
  | apply( FOLD_RSTAR   (s, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state = apply(s,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
                                application_stack   = getApplicationStack state,
                                reduction_stack     = getReductionStack state,
                                strategy            = [FOLD_RSTAR( getSingleStrategy state, x_info )],
                                                                                  
                                first_order_result  = getFirstOrderResult  state,
                                higher_order_result = foldStrategyList("RSTAR", state, x_info)
						    }
						end
																							
  | apply( MAPL (s, x_info), term ) =			apply_mapL(s, term, x_info) 
  | apply( MAPR (s, x_info), term ) =			apply_mapR(s, term, x_info) 
  | apply( MAPB (s, x_info), term ) =			apply_mapB(s, term, x_info) 
																				
  | apply( TRANSIENT (s, x_info), term ) =
						let
							(* ---------------------------------------------------------------------------------------------------------- *)
							val state             = apply(s,term) 
							val strategy_returned = if STACK.reductionObserved(state) then SKIP(x_info) else TRANSIENT( getSingleStrategy state, x_info )
							(* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
								application_stack   = getApplicationStack state,
								reduction_stack     = STACK.popStack(getReductionStack state),
								strategy            = [strategy_returned],
                                                                                  
								first_order_result  = getFirstOrderResult  state,
								higher_order_result = getHigherOrderResult state
						    }
						end
																					
  | apply( OPAQUE    (s, x_info), term ) =
						let
							(* ---------------------------------------------------------------------------------------------------------- *)
							val state = apply(s,term)
							(* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
								application_stack   = getApplicationStack state,
								reduction_stack     = STACK.popStack(getReductionStack state),
								strategy            = [OPAQUE( getSingleStrategy state, x_info )],
                                                                                  
								first_order_result  = getFirstOrderResult  state,
								higher_order_result = getHigherOrderResult state
						    }
						end
																									
  | apply( HIDE      (s, x_info), term ) =
						let
							(* ---------------------------------------------------------------------------------------------------------- *)
							val state = apply(s,term)
							(* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
								application_stack   = STACK.popStack(getApplicationStack state),
								reduction_stack     = getReductionStack state,
								strategy            = [HIDE( getSingleStrategy state, x_info )],
                                                                                  
								first_order_result  = getFirstOrderResult  state,
								higher_order_result = getHigherOrderResult state
						    }
						end
											
  | apply( RAISE     (s, x_info), term ) =
						let
							(* ---------------------------------------------------------------------------------------------------------- *)
							val state = apply(s,term)
							(* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
								application_stack   = getApplicationStack state,
								reduction_stack     = STACK.dupStackTop(getReductionStack state),
								strategy            = [RAISE( getSingleStrategy state, x_info )],
                                                                                  
								first_order_result  = getFirstOrderResult  state,
								higher_order_result = getHigherOrderResult state
						    }
						end
											
  | apply( LIFT      (s, x_info), term ) =
						let
							(* ---------------------------------------------------------------------------------------------------------- *)
							val state = apply(s,term)
							(* ---------------------------------------------------------------------------------------------------------- *)
						in
						    {
								application_stack   = STACK.dupStackTop(getApplicationStack state),
								reduction_stack     = getReductionStack state,
								strategy            = [LIFT( getSingleStrategy state, x_info )],
                                                                                  
								first_order_result  = getFirstOrderResult  state,
								higher_order_result = getHigherOrderResult state
						    }
						end
								
  | apply( CHOICE(s1,s2, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state1 = apply(s1,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    if STACK.applicationObserved(state1) 
						    then
										{
                                    		application_stack   = getApplicationStack state1, 
					                        reduction_stack     = getReductionStack   state1,
                                        	strategy            = [buildStrategyReturned("CHOICE", getSingleStrategy state1, s2, x_info)],
				  				                                                                              
					                        first_order_result  = getFirstOrderResult  state1,
                                        	higher_order_result = getHigherOrderResult state1
										}
																	
						    else 	let
										val state2 = apply(s2,getTerm state1)
									in
										{
                                       		application_stack   = getApplicationStack state2,
					                        reduction_stack     = STACK.orStack(getReductionStack   state1, getReductionStack   state2),
                                    		strategy            = [buildStrategyReturned("CHOICE", getSingleStrategy state1, getSingleStrategy state2, x_info)],
				  						                                                                             
					                        first_order_result  = getFirstOrderResult  state2,
                                    		higher_order_result = buildHigherOrderReturned(state1, state2)
										}
									end
						end
														
  | apply( LCHOICE(s1,s2, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state1 = apply(s1,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    if STACK.applicationObserved(state1) 
						    then
										{
                                        	application_stack   = getApplicationStack state1, 
					                        reduction_stack     = getReductionStack   state1,
                                        	strategy            = [buildStrategyReturned("LCHOICE", getSingleStrategy state1, s2, x_info)],
				  				                                                                              
					                        first_order_result  = getFirstOrderResult  state1,
                                        	higher_order_result = getHigherOrderResult state1
										}		
																	
						    else 	let
										val state2 = apply(s2,getTerm state1)
									in
										{
                                        	application_stack   = getApplicationStack state2,
					                        reduction_stack     = STACK.orStack(getReductionStack   state1, getReductionStack   state2),
                                        	strategy            = [buildStrategyReturned("LCHOICE", getSingleStrategy state1, getSingleStrategy state2, x_info)],
				  						                                                                             
					                        first_order_result  = getFirstOrderResult  state2,
                                        	higher_order_result = buildHigherOrderReturned(state1, state2)
										}
									end
						end
															
  | apply( RCHOICE(s2,s1, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state1 = apply(s1,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    if STACK.applicationObserved(state1) 
						    then
										{
                                        	application_stack   = getApplicationStack state1, 
					                        reduction_stack     = getReductionStack   state1,
                                        	strategy            = [buildStrategyReturned("RCHOICE", s2, getSingleStrategy state1, x_info)],
				  				                                                                              
					                        first_order_result  = getFirstOrderResult  state1,
                                        	higher_order_result = getHigherOrderResult state1
										}
																								
						    else 	let
										val state2 = apply(s2,getTerm state1)
									in
										{
                                        	application_stack   = getApplicationStack state2,
					                        reduction_stack     = STACK.orStack(getReductionStack   state1, getReductionStack   state2),
                                        	strategy            = [buildStrategyReturned("RCHOICE", getSingleStrategy state2, getSingleStrategy state1, x_info)],
				  						                                                                             
					                        first_order_result  = getFirstOrderResult  state2,
                                        	higher_order_result = buildHigherOrderReturned(state1, state2)
										}
									end
						end
																			
  | apply( LSEQ(s1,s2, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state1 = apply(s1,term)
						    val state2 = apply(s2,getTerm state1)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
										{
                                            application_stack   = STACK.orStack( getApplicationStack state1, getApplicationStack state2 ),  
											reduction_stack     = STACK.orStack( getReductionStack   state1, getReductionStack   state2 ), 
                                        	strategy            = [buildStrategyReturned("LSEQ", getSingleStrategy state1, getSingleStrategy state2, x_info)],
				  				                                                                              
											first_order_result  = getFirstOrderResult  state2,
                                        	higher_order_result = buildHigherOrderReturned(state1, state2)
										}
						end
																											
  | apply( RSEQ(s2,s1, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state1 = apply(s1,term)
						    val state2 = apply(s2,getTerm state1)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
										{
                                            application_stack   = STACK.orStack( getApplicationStack state1, getApplicationStack state2 ),  
											reduction_stack     = STACK.orStack( getReductionStack   state1, getReductionStack   state2 ), 
                                        	strategy            = [buildStrategyReturned("RSEQ", getSingleStrategy state2, getSingleStrategy state1, x_info)],
				  				                                                                              
											first_order_result  = getFirstOrderResult  state2,
                                            higher_order_result = buildHigherOrderReturned(state1, state2)
										}
						end
																													
  | apply( LSTAR(s1,s2, x_info), term ) =
						let
						    (* ---------------------------------------------------------------------------------------------------------- *)
						    val unsuccessful_application_state =
								{
				               		application_stack   = STACK.FALSE_STACK,
									reduction_stack     = STACK.FALSE_STACK,
									strategy            = [LSTAR(s1,s2, x_info)],
				  				                                                                              
									first_order_result  = [term],
									higher_order_result = []
								}
                                                    
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state1 = apply(s1,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    if STACK.applicationObserved(state1) 
						    then 
								let
						            val state2 = apply(s2,getTerm state1)
								in
									if STACK.applicationObserved(state2) 
									then
										{
											application_stack   = STACK.andStack(getApplicationStack state1, getApplicationStack state2),
					                        reduction_stack     = STACK.andStack(getReductionStack   state1, getReductionStack   state2),
                                        	strategy            = [buildStrategyReturned("LSTAR", getSingleStrategy state1, getSingleStrategy state2, x_info)],
				  					  	                                                                             
					                        first_order_result  = getFirstOrderResult  state2,
                                        	higher_order_result = buildHigherOrderReturned(state1, state2)
							           }
																					
									else  unsuccessful_application_state 
							 end
																					
						    else unsuccessful_application_state
						end
																									
  | apply( RSTAR(s2,s1, x_info), term ) =
						let
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val unsuccessful_application_state =
								{
									application_stack   = STACK.FALSE_STACK,
									reduction_stack     = STACK.FALSE_STACK,
									strategy            = [RSTAR(s1,s2, x_info)],
				  				                                                                              
									first_order_result  = [term],
									higher_order_result = []
							    }
                            (* ---------------------------------------------------------------------------------------------------------- *)
						    val state1 = apply(s1,term)
                            (* ---------------------------------------------------------------------------------------------------------- *)
						in
						    if STACK.applicationObserved(state1) 
						    then 
								let
						            val state2 = apply(s2,getTerm state1)
								in
									if STACK.applicationObserved(state2) 
									then
										{
                                            application_stack   = STACK.andStack(getApplicationStack state1, getApplicationStack state2),
					                        reduction_stack     = STACK.andStack(getReductionStack   state1, getReductionStack   state2),
                                            strategy            = [buildStrategyReturned("RSTAR", getSingleStrategy state2, getSingleStrategy state1, x_info)],
				  					  	                                                                             
					                        first_order_result  = getFirstOrderResult  state2,
                                            higher_order_result = buildHigherOrderReturned(state1, state2)
										}
																				
									else  unsuccessful_application_state 
								end
						    else unsuccessful_application_state
						end
																								
  | apply( ref_term as REF tuple, term )  = 
						let
							val s            = STORE.lookup(ref_term)
							val state        = apply(s,term)
						in
							STORE.update(ref_term , getSingleStrategy state );
									
						    {
								application_stack   = getApplicationStack state,
								reduction_stack     = getReductionStack   state,
								strategy            = [ref_term],
				  				                                                                              
								first_order_result  = getFirstOrderResult  state,
								higher_order_result = getHigherOrderResult state
						    }
						end
																											
  | apply( SKIP(x_info), term)  =   
					{
							application_stack   = STACK.FALSE_STACK,
				       		reduction_stack     = STACK.FALSE_STACK,
							strategy            = [SKIP(x_info)],
				  				                                                                              
							first_order_result  = [term],
							higher_order_result = []
					}
																					
  | apply( ID(x_info), term)    =   
					{
							application_stack   = STACK.TRUE_STACK,
							reduction_stack     = STACK.TRUE_STACK,
							strategy            = [ID(x_info)],
				  				                                                                              
							first_order_result  = [term],
							higher_order_result = []       (* ID should not return a higher-order result *)
					}
                        
  | apply( FAIL(x_info), term) =
                    {
                        application_stack   = STACK.FALSE_STACK,
                        reduction_stack     = STACK.TRUE_STACK,
                        strategy            = [FAIL(x_info)],
                        
                        first_order_result  = [term],
                        higher_order_result = []
                    }
													
  | apply(t1, t2)       =  		RUNTIME.error([t1, t2], General.Fail("Error in SEMANTICS.apply.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
																				
(* ------------------------------------------------------------------------------------------- *)
and apply_mapL( s, t as TERM( itree(inode(root),[]), _), x_info_mapL ) =
						{
							application_stack   = STACK.FALSE_STACK,
							reduction_stack     = STACK.FALSE_STACK,
							strategy            = [MAPL (s, x_info_mapL)],
				  				                                                                              
							first_order_result  = [t],
							higher_order_result = []   
						}
										
  | apply_mapL( s_reduced, t as TERM( itree(inode(root),subterms), x_info_tree), x_info_mapL )  =
						let
						    fun aux( term, (s, state_acc) ) = 
											let
												val state         = apply(s, TERM (term, x_info_tree) )
												val new_s         = getSingleStrategy state                      (* strategy is threaded *)
												val new_state_acc = composeThreadedState(state_acc, state)
											in
												(new_s, new_state_acc)
											end					    
																								
						    val (final_strategy, final_state_list) = foldl aux (s_reduced, []) subterms 
						    val final_state                        = hd final_state_list
																	 handle Empty => raise RUNTIME.error([s_reduced, t], General.Fail("Error in SEMANTICS.apply_mapL.final_state.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
						    val new_subterms                       = filter_rev (getFirstOrderResult final_state, [])
																														
						in
						    {
								application_stack   = getApplicationStack final_state,
								reduction_stack     = getReductionStack   final_state,
								strategy            = [MAPL (final_strategy, x_info_mapL)],
				  				                                                                              
								first_order_result  = [TERM (itree(inode(root), new_subterms), x_info_tree) ],
								higher_order_result = getHigherOrderResult final_state
						    }
						end
													
  | apply_mapL (s, t, _) = RUNTIME.error([s,t], General.Fail("Error in SEMANTICS.apply_mapL.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
																					
(* ------------------------------------------------------------------------------------------- *)
and apply_mapR( s, t as TERM(itree(inode(root),[]), x_info_tree), x_info_mapR ) =
						{
							application_stack   = STACK.FALSE_STACK,
							reduction_stack     = STACK.FALSE_STACK,
							strategy            = [MAPR (s, x_info_mapR)],
				  				                                                                              
							first_order_result  = [t],
							higher_order_result = []   
						}
										
  | apply_mapR( s_reduced, t as TERM(itree(inode(root),subterms), x_info_tree), x_info_mapR ) =
						let
						    fun aux( term, (s, state_acc) ) = 
											let
												val state         = apply(s, TERM (term, x_info_tree) )
												val new_s         = getSingleStrategy state                      (* strategy is threaded *)
												val new_state_acc = composeThreadedState(state_acc, state)
											in
												(new_s, new_state_acc)
											end					    

						    val (final_strategy, final_state_list) = foldr aux (s_reduced, []) subterms 
							val final_state                        = hd( final_state_list ) 
																	 handle Empty => raise RUNTIME.error([s_reduced, t], General.Fail("Error in SEMANTICS.apply_mapR.final_state.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
							val new_subterms                       = filter (getFirstOrderResult final_state)
						in
						    {
								application_stack   = getApplicationStack final_state,
								reduction_stack     = getReductionStack   final_state,
								strategy            = [MAPR( final_strategy, x_info_mapR )],
				  				                                                                              
								first_order_result  = [TERM (itree(inode(root), new_subterms), x_info_tree)],
								higher_order_result = getHigherOrderResult final_state
						    }
						end
															
  | apply_mapR (s, t, _) = RUNTIME.error([s,t], General.Fail("Error in SEMANTICS.apply_mapR.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
																					
(* ------------------------------------------------------------------------------------------- *)
(* currently only well-defined for top-down *)
																						
and apply_mapB( s, t as TERM(itree(inode(root),[]), x_info_tree), x_info_mapB ) =
						{
							application_stack   = STACK.FALSE_STACK,
							reduction_stack     = STACK.FALSE_STACK,
							strategy            = [MAPB (s, x_info_mapB)],
				  				                                                                              
							first_order_result  = [t],
							higher_order_result = []   
						}
									
  | apply_mapB( s_reduced, t as TERM(itree(inode(root),subterms), x_info_tree), x_info_mapB ) =
						let
						    fun aux( term, state_acc ) = 
											let
												val state         = apply(s_reduced, TERM (term, x_info_tree) )
												val new_state_acc = composeThreadedState(state_acc, state) (* don't care since strategy is ignored *)
											in
												new_state_acc
											end					    
						    val final_state   = hd (foldl aux [] subterms)
												handle Empty => raise RUNTIME.error([s_reduced, t], General.Fail("Error in SEMANTICS.apply_mapB.final_state.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
						    val new_subterms  = filter_rev (getFirstOrderResult final_state, [])
						in
						    {
								application_stack   = getApplicationStack final_state,
								reduction_stack     = getReductionStack   final_state,
								strategy            = [MAPB( getSingleStrategy final_state, x_info_mapB )],   (* don't care since this is only for top-down *)
				  				                                                                              
								first_order_result  = [TERM (itree(inode(root), new_subterms), x_info_tree) ],
								higher_order_result = getHigherOrderResult final_state
						    }
						end
																			
  | apply_mapB (s, t, _) = RUNTIME.error([s,t], General.Fail("Error in SEMANTICS.apply_mapB.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
																					
(* ------------------------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------------------------- *)
(* the objective of reduce is to produce a value                                               *)
(* ------------------------------------------------------------------------------------------- *)
and reduce( APP(expr1, expr2, x_info) ) = 
							let
                                val (_           , strategy_reduced) = reduce expr1
                                val (term_reduced, _               ) = reduce expr2
								val new_strategy_reduced = STATE_MODEL.build1StrategyReturned(strategy_reduced, x_info)
								
                       	        val state_record  = apply( new_strategy_reduced, hd term_reduced )
                                                    handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = APP.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
                                in
                                   (* strategic expressions can be in lazy form *)
							       createResult state_record 
                             	end
								
  (* -------------------------------------------------------------------- *)
  | reduce( ITERATOR (id, args, x_info)     ) = 
							let
                                fun filter( term_list, []  ) = SKIP x_info
                                  | filter( term_list, [s] ) = s
                                  | filter( term_list, xs  ) = raise RUNTIME.error([ITERATOR(id, args, x_info)], General.Fail("Error in SEMANTICS.reduce.filter: case = ITERATOR. Missing fold?\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
											
                                val reduced_args = map filter (map reduce args)
							in
								( [], [ITERATOR( id, reduced_args, x_info ) ]) 
							end
									
(* -------------------------------------------------------------------- *)
  | reduce( B_OR (expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _) = reduce expr1
							    val (expr2_reduced, _) = reduce expr2
							in
							    (
									[ OPERATIONS.booleanOr( hd expr1_reduced, hd expr2_reduced, x_info ) ],   (* first-order  result *)
									[]                                                                        (* higher-order result *)
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = B_OR.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
																									
  | reduce( B_AND(expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _) = reduce expr1
							    val (expr2_reduced, _) = reduce expr2
							in
								(
									[OPERATIONS.booleanAnd( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = B_AND.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
																			
  | reduce( EQ (expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _) = reduce expr1
							    val (expr2_reduced, _) = reduce expr2
							in
							    (
									[OPERATIONS.eq( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = EQ.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
																					
  | reduce( NEQ(expr1, expr2, x_info) ) = 
							let
								val (expr1_reduced, _) = reduce expr1
								val (expr2_reduced, _) = reduce expr2
							in
							    (
									[OPERATIONS.neq( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = NEQ.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
													
  | reduce( GEQ(expr1, expr2, x_info) ) = 
							let
								val (expr1_reduced, _) = reduce expr1
								val (expr2_reduced, _) = reduce expr2
							in
							    (
									[OPERATIONS.geq( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = GEQ.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
									
  | reduce( GT (expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _) = reduce expr1
							    val (expr2_reduced, _) = reduce expr2
							in
							    (
									[OPERATIONS.gt( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = GT.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
															
  | reduce( LEQ(expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced,_) = reduce expr1
							    val (expr2_reduced,_) = reduce expr2
							in
							    (
									[OPERATIONS.leq( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = LEQ.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
											
  | reduce( LT (expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _) = reduce expr1
							    val (expr2_reduced, _) = reduce expr2
							in
								(
									[OPERATIONS.lt( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = LT.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
																		
  | reduce( CONCAT(expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _) = reduce expr1
							    val (expr2_reduced, _) = reduce expr2
							in
							    (
									[OPERATIONS.stringConcat( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = CONCAT.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
																		
  | reduce( PLUS(expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _) = reduce expr1
							    val (expr2_reduced, _) = reduce expr2
							in
								(
									[OPERATIONS.add( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = PLUS.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
													
  | reduce( MINUS (expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _) = reduce expr1
							    val (expr2_reduced, _) = reduce expr2
							in
							    (
									[OPERATIONS.subtract( hd expr1_reduced, hd expr2_reduced, x_info)],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = MINUS.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
								
  | reduce( TIMES (expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _) = reduce expr1
							    val (expr2_reduced, _) = reduce expr2
							in
							    (
									[OPERATIONS.multiply( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = TIMES.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
																
  | reduce( DIVIDE(expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _) = reduce expr1
							    val (expr2_reduced, _) = reduce expr2
							in
							    (
									[OPERATIONS.divide( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = DIVIDE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
											
  | reduce( DIV   (expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _ ) = reduce expr1
							    val (expr2_reduced, _ ) = reduce expr2
							in
							    (
									[OPERATIONS.intDiv( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = DIV.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
																	
  | reduce( MOD   (expr1, expr2, x_info) ) = 
							let
							    val (expr1_reduced, _ ) = reduce expr1
							    val (expr2_reduced, _ ) = reduce expr2
							in
							    (
									[OPERATIONS.modulus( hd expr1_reduced, hd expr2_reduced, x_info )],
									[]
								)
                                handle Empty => RUNTIME.error([expr1,expr2], General.Fail("Error in SEMANTICS.reduce. case = MOD.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
														
  | reduce( TILDE   (expr, x_info)  ) = 
							let
							    val (expr_reduced, _ ) = reduce expr
							in
							    (
									[OPERATIONS.tilde( hd expr_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr], General.Fail("Error in SEMANTICS.reduce. case = TILDE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
																	
  | reduce( BANG   (expr, x_info)  ) = 
							let
							    val (expr_reduced , _ ) = reduce expr
							in
                                (
									[OPERATIONS.bang( hd expr_reduced, x_info )],
									[]
								)
								handle Empty => RUNTIME.error([expr], General.Fail("Error in SEMANTICS.reduce. case = BANG.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							end
												
  (* -------------------------------------------------------------------- *)
  | reduce(expr as LIBRARY_CALL_0 (IDENTIFIER (f_id, _), x_info) ) = 
							let
							    val the_function = lookupSML(f_id, UserDefined.functions, x_info)
								val result = the_function([]) 
                                             handle ex => RUNTIME.error([expr], ex, ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
							in
							    (
									[result],
									[]
								)
								handle General.Fail( msg ) => let
																val msg2 = " Error in SEMANTICS.reduce. case = LIBRARY_CALL_0.\n"
															  in
																print(msg);
																RUNTIME.error([expr], General.Fail(msg ^ msg2), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
															  end
							end
																	
  | reduce(expr as LIBRARY_CALL (IDENTIFIER (f_id,_), arg_list, x_info) ) = 
							let
							    val the_function     = lookupSML(f_id, UserDefined.functions, x_info)
							    val arg_list_reduced = map reduce arg_list   (* only first-order arguments at this time *)
								val result           = the_function arg_list_reduced
                                                       handle ex => RUNTIME.error([expr], ex, ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
							in
								(
									[result],
									[]
								)
								handle General.Fail( msg ) => let
																val msg2 = " Error in SEMANTICS.reduce. case = LIBRARY_CALL.\n"
															  in
																print msg;
																RUNTIME.error([expr], General.Fail(msg ^ msg2), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
															  end
							end
																
  (* -------------------------------------------------------------------- *)
  | reduce( RULE(lhs,rhs,x_info)           ) = ( [], [RULE(lhs,rhs,x_info)]            ) 
  | reduce( COND_RULE(lhs,rhs,cond,x_info) ) = ( [], [COND_RULE(lhs,rhs,cond,x_info)]  )
																				
  (* -------------------------------------------------------------------- *)                                                                                             
  | reduce( TRANSIENT (s, x_info)             ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy_list = STATE_MODEL.build1StrategyListReturned("TRANSIENT", strategy_list, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([TRANSIENT (s,x_info) ], General.Fail("Error in SEMANTICS.reduce. case = TRANSIENT.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																		
  | reduce( OPAQUE    (s, x_info)             ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy_list = STATE_MODEL.build1StrategyListReturned("OPAQUE", strategy_list, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([OPAQUE (s,x_info)], General.Fail("Error in SEMANTICS.reduce. case = OPAQUE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																		
  | reduce( RAISE     (s, x_info)             ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy_list = STATE_MODEL.build1StrategyListReturned("RAISE", strategy_list, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([RAISE (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = RAISE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																				
  | reduce( HIDE      (s, x_info)             ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy_list = STATE_MODEL.build1StrategyListReturned("HIDE", strategy_list, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([HIDE (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = HIDE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																			
  | reduce( LIFT      (s, x_info)             ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy_list = STATE_MODEL.build1StrategyListReturned("LIFT", strategy_list, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([LIFT (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = LIFT.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
														
  (* -------------------------------------------------------------------- *)                                                                                                                                                                
  | reduce( MAPL (s, x_info) ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
					in
						( [], [MAPL (hd strategy_list, x_info)] ) 
					    handle Empty => RUNTIME.error([MAPL (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = MAPL.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																
  | reduce( MAPR (s, x_info) ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
					in
						( [], [MAPR (hd strategy_list, x_info)] ) 
					    handle Empty => RUNTIME.error([MAPR (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = MAPR.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																	
  | reduce( MAPB (s, x_info) ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
					in
						( [], [MAPB (hd strategy_list, x_info)] ) 
					    handle Empty => RUNTIME.error([MAPB (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = MAPB.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																				
  (* -------------------------------------------------------------------- *)                                                                                             
  | reduce( FOLD_CHOICE  (s, x_info)          ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)
					in
                        ( [], [FOLD_CHOICE (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLD_CHOICE (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLD_CHOICE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end 
																		
  | reduce( FOLD_LCHOICE (s, x_info)          ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)
					in
                        ( [], [FOLD_LCHOICE (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLD_LCHOICE (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLD_LCHOICE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																				
  | reduce( FOLD_RCHOICE (s, x_info)          ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)
					in
                        ( [], [FOLD_RCHOICE (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLD_RCHOICE (s,x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLD_RCHOICE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																				
  | reduce( FOLD_LSEQ    (s, x_info)          ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLD_LSEQ (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLD_LSEQ (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLD_LSEQ.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																	
  | reduce( FOLD_RSEQ    (s, x_info)          ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLD_RSEQ (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLD_RSEQ (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLD_RSEQ.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																			
  | reduce( FOLD_LSTAR   (s, x_info)          ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLD_LSTAR (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLD_LSTAR (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLD_LSTAR.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																			
  | reduce( FOLD_RSTAR   (s, x_info)          ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLD_RSTAR (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLD_RSTAR (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLD_RSTAR.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
														
  (* -------------------------------------------------------------------- *)
  | reduce( FOLDS_CHOICE  (s, x_info)         ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLDS_CHOICE (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLDS_CHOICE (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLDS_CHOICE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																			
  | reduce( FOLDS_LCHOICE (s, x_info)         ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLDS_LCHOICE (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLDS_LCHOICE (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLDS_LCHOICE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																					
  | reduce( FOLDS_RCHOICE (s, x_info)         ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLDS_RCHOICE (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLDS_RCHOICE (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLDS_RCHOICE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																		
  | reduce( FOLDS_LSEQ    (s, x_info)         ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLDS_LSEQ (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLDS_LSEQ (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLDS_LSEQ.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																			
  | reduce( FOLDS_RSEQ    (s, x_info)         ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLDS_RSEQ (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLDS_RSEQ (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLDS_RSEQ.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																				
  | reduce( FOLDS_LSTAR   (s, x_info)         ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLDS_LSTAR (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLDS_LSTAR (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLDS_LSTAR.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																					
  | reduce( FOLDS_RSTAR   (s, x_info)         ) = 
					let
					    val (term_list, strategy_list) = reduce s   (* term list should be null, otherwise it is a type error *)
						val new_strategy               = STATE_MODEL.build1StrategyReturned(strategy_list, x_info)	
					in
                        ( [], [FOLDS_RSTAR (new_strategy, x_info)] ) 
					    handle Empty => RUNTIME.error([FOLDS_RSTAR (s, x_info)], General.Fail("Error in SEMANTICS.reduce. case = FOLDS_RSTAR.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																		
  (* -------------------------------------------------------------------- *)                                                                                       
  | reduce( CHOICE (s1,s2, x_info)          ) = 
					let
					    val (term_list1, strategy_list1) = reduce s1   (* term list should be null, otherwise it is a type error *)
					    val (term_list2, strategy_list2) = reduce s2   (* term list should be null, otherwise it is a type error *)
												
						val new_strategy_list = STATE_MODEL.build2StrategyListReturned("CHOICE", strategy_list1, strategy_list2, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([CHOICE (s1,s2, x_info) ], General.Fail("Error in SEMANTICS.reduce. case = CHOICE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																				
  | reduce( LCHOICE (s1,s2, x_info)         ) = 
					let
					    val (term_list1, strategy_list1) = reduce s1   (* term list should be null, otherwise it is a type error *)
					    val (term_list2, strategy_list2) = reduce s2   (* term list should be null, otherwise it is a type error *)
												
						val new_strategy_list = STATE_MODEL.build2StrategyListReturned("LCHOICE", strategy_list1, strategy_list2, x_info)
					in
						( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([LCHOICE (s1,s2, x_info) ], General.Fail("Error in SEMANTICS.reduce. case = LCHOICE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
											
  | reduce( RCHOICE (s1,s2, x_info)         ) = 
					let
					    val (term_list1, strategy_list1) = reduce s1   (* term list should be null, otherwise it is a type error *)
					    val (term_list2, strategy_list2) = reduce s2   (* term list should be null, otherwise it is a type error *)
										
						val new_strategy_list = STATE_MODEL.build2StrategyListReturned("RCHOICE", strategy_list1, strategy_list2, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([RCHOICE (s1,s2, x_info) ], General.Fail("Error in SEMANTICS.reduce. case = RCHOICE.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																				
  | reduce( LSEQ (s1,s2, x_info)            ) = 
					let
					    val (term_list1, strategy_list1) = reduce s1   (* term list should be null, otherwise it is a type error *)
					    val (term_list2, strategy_list2) = reduce s2   (* term list should be null, otherwise it is a type error *)
																															
						val new_strategy_list = STATE_MODEL.build2StrategyListReturned("LSEQ", strategy_list1, strategy_list2, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([LSEQ (s1,s2, x_info) ], General.Fail("Error in SEMANTICS.reduce. case = LSEQ.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																						
  | reduce( RSEQ (s1,s2, x_info)            ) = 
					let
					    val (term_list1, strategy_list1) = reduce s1   (* term list should be null, otherwise it is a type error *)
					    val (term_list2, strategy_list2) = reduce s2   (* term list should be null, otherwise it is a type error *)
						
						val new_strategy_list = STATE_MODEL.build2StrategyListReturned("RSEQ", strategy_list1, strategy_list2, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([RSEQ (s1,s2, x_info) ], General.Fail("Error in SEMANTICS.reduce. case = RSEQ.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																	
  | reduce( LSTAR (s1,s2, x_info)           ) = 
					let
					    val (term_list1, strategy_list1) = reduce s1   (* term list should be null, otherwise it is a type error *)
					    val (term_list2, strategy_list2) = reduce s2   (* term list should be null, otherwise it is a type error *)
						
						val new_strategy_list = STATE_MODEL.buildStar2StrategyListReturned("LSTAR", strategy_list1, strategy_list2, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([LSTAR (s1,s2, x_info) ], General.Fail("Error in SEMANTICS.reduce. case = LSTAR.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																
  | reduce( RSTAR (s1,s2, x_info)           ) = 
					let
					    val (term_list1, strategy_list1) = reduce s1   (* term list should be null, otherwise it is a type error *)
					    val (term_list2, strategy_list2) = reduce s2   (* term list should be null, otherwise it is a type error *)
						
						val new_strategy_list = STATE_MODEL.buildStar2StrategyListReturned("RSTAR", strategy_list1, strategy_list2, x_info)
					in
                        ( [], new_strategy_list ) 
					    handle Empty => RUNTIME.error([RSTAR (s1,s2, x_info) ], General.Fail("Error in SEMANTICS.reduce. case = RSTAR.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
					end
																		
  (* -------------------------------------------------------------------- *)
  | reduce( REF( id, ref_info, x_info )         ) = ( []            , [REF(id, ref_info, x_info)] )                                                                                                              
  | reduce( IDENTIFIER (id, x_info)             ) = ( []            , [IDENTIFIER (id, x_info)  ] )
  | reduce( ID( x_info )                        ) = ( [ID(x_info)]  , [ID(x_info)]                )
  | reduce( SKIP( x_info )                      ) = ( [SKIP(x_info)], [SKIP(x_info)]              )
  | reduce( FAIL( x_info )                      ) = ( [FAIL(x_info)], [FAIL(x_info)]              )
                                                                 
  | reduce( TERM parse_expr_tuple               ) = ( [TERM parse_expr_tuple], [] )  
                                                    
  | reduce( BOOL   v                            ) = ( [BOOL   v], [] )
  | reduce( INT    v                            ) = ( [INT    v], [] )
  | reduce( REAL   v                            ) = ( [REAL   v], [] )
  | reduce( STRING v                            ) = ( [STRING v], [] )
																					
  | reduce (t) = let
					val msg = "Error in SEMANTICS.reduce.\n"
				 in
					print msg;
					RUNTIME.error([t], General.Fail(msg), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
				 end
																			
(* ------------------------------------------------------------------------------------------- *)
(* the objective of eval is to produce a sigma                                                 *)
(* ------------------------------------------------------------------------------------------- *)
and eval(_, NONE ) = NONE

  | eval(ANDALSO(expr1,expr2, _), sigma0 ) = 
						let
						    val sigma1 = eval(expr1, sigma0)
						in
                            if isSome(sigma1) then eval(expr2, sigma1)
                                              else NONE  
						end
													
  | eval(ORELSE (expr1,expr2, _), sigma0 ) = 
						let
						    val sigma1        = eval(expr1, sigma0)
						in
						    if isSome(sigma1) then sigma1
						    		          else eval(expr2, sigma0)  
						end
												
  | eval(NOT(expr, _), sigma0 ) = 
						let
						    val sigma1        = eval(expr, sigma0)
						in
						    if isSome(sigma1) then NONE
						    		          else sigma0  
						end
													
  | eval(LEQ (expr1,expr2, _), sigma ) = 
						let
						    val v1 = MATCHING.subst(sigma,expr1)
							val v2 = MATCHING.subst(sigma,expr2)
						in
						    if OPERATIONS.control_leq(v1,v2) then sigma  
						    		                         else NONE
						end

  | eval(LT (expr1,expr2, _), sigma ) = 
						let
						    val v1 = MATCHING.subst(sigma,expr1)
							val v2 = MATCHING.subst(sigma,expr2)
						in
						    if OPERATIONS.control_lt(v1,v2) then sigma  
						    		                         else NONE
						end

  | eval(GEQ (expr1,expr2, _), sigma ) = 
						let
						    val v1 = MATCHING.subst(sigma,expr1)
							val v2 = MATCHING.subst(sigma,expr2)
						in
						    if OPERATIONS.control_geq(v1,v2) then sigma  
						    		                         else NONE
						end
						
  | eval(GT (expr1,expr2, _), sigma ) = 
						let
						    val v1 = MATCHING.subst(sigma,expr1)
							val v2 = MATCHING.subst(sigma,expr2)
						in
						    if OPERATIONS.control_gt(v1,v2) then sigma  
						    		                         else NONE
						end
						
  | eval(MATCH(left,right, x_info), sigma ) =
						let
						    val (left_first_order_result , _) = reduce( MATCHING.subst( sigma, left ) )
						    val (right_first_order_result, _) = reduce( MATCHING.subst( sigma, right) )   (* can be optimized!! delay this but consider operations *)
						in								
						    MATCHING.match( hd left_first_order_result, hd right_first_order_result, sigma)
							handle Empty => RUNTIME.error([MATCH(left,right, x_info)], General.Fail("Error in SEMANTICS.eval. case = MATCH.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
						end
																						
  | eval(BIND(ref_term,strategic_expression, x_info), sigma ) =
						let
						    val (_, reduced_strategic_expression) = reduce( MATCHING.subst( sigma, strategic_expression) )  
						in
						    if null reduced_strategic_expression then STORE.update(ref_term, SKIP(x_info))
																 else STORE.update(ref_term, hd reduced_strategic_expression);
							sigma
						end
																		
  | eval(APP( strategy, term, x_info), sigma ) =
						let
						    val (_                 , higher_order_result) = reduce (MATCHING.subst(sigma, strategy)) 
						    val (first_order_result, _                  ) = reduce (MATCHING.subst(sigma, term    ))
							val h_strategy                                = if null(higher_order_result) then SKIP(x_info) else hd(higher_order_result)
						    val state      							      = apply( h_strategy, hd first_order_result )  
																			handle Empty => RUNTIME.error([APP(strategy, term, x_info)], General.Fail("Error in SEMANTICS.eval. case = APP.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo ) 
						in
						    if STACK.applicationObserved(state) then sigma
																else NONE
						end
																			
  | eval(expr as LIBRARY_CALL_0( IDENTIFIER (f_id, _), x_info ), sigma ) = 
						let
						    val the_function = lookupSML(f_id, UserDefined.functions, x_info)
							val result = the_function( [] ) 
										 handle ex => RUNTIME.error([expr], ex, ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
							            
						in
							case result of
								  TRUE 		=> sigma
								| FALSE 	=> NONE
								| _         => RUNTIME.error([expr], General.Fail("Improper return time for SML library function in this context\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo)
						end
													
  | eval(expr as LIBRARY_CALL( IDENTIFIER (f_id,_), expr_list, x_info ), sigma ) = 
						let
						    val the_function       = lookupSML(f_id, UserDefined.functions, x_info)
							val expr_list_instance = map (fn expr => reduce ( MATCHING.subst(sigma,expr) )) expr_list
							val result             = the_function expr_list_instance
										             handle ex => RUNTIME.error([expr], ex, ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo )
						in
							case result of
								  TRUE 		=> sigma
								| FALSE 	=> NONE
								| _         => RUNTIME.error([expr], General.Fail("Improper return time for SML library function in this context\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo)
						end
												
  | eval (t, _) = RUNTIME.error([t], General.Fail("Error in SEMANTICS.eval.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo );
																
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun applyMain( strategy, term ) = getTerm( apply( strategy, term ) )
																											
(* ------------------------------------------------------------------------------------------- *)
end;  (* struct *)
(* ------------------------------------------------------------------------------------------- *)