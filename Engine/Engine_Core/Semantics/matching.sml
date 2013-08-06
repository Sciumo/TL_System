(* ------------------------------------------------------------------------------------------- *)
signature MATCHING_SIG =
sig
	val match : ABSTRACT_REPRESENTATION.EXPR *                                    (* term         *)
                ABSTRACT_REPRESENTATION.EXPR *                                    (* ground term  *)
                (string * string * CONCRETE_REPRESENTATION.ITREE) list option     (* sigma_in     *)
				->                                                                                                   
                (string * string * CONCRETE_REPRESENTATION.ITREE) list option     (* sigma_out    *)
                                                                                           
	val subst : (string * string * CONCRETE_REPRESENTATION.ITREE) list option *   (* sigma: (symbol_type,symbol_id,ground_term) list option *)
                ABSTRACT_REPRESENTATION.EXPR                                      (* term         *)
		    	->                                                                                       
                ABSTRACT_REPRESENTATION.EXPR                                      (* sigma(term)  *) 
																											
end;
(* ------------------------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------------------------- *)
structure MATCHING : MATCHING_SIG =
struct

open ABSTRACT_REPRESENTATION;

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*                                    MATCHING                                                 *)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)

exception MatchFail;

(* ------------------------------------------------------------------------------------------- *)
fun zip (x::xs) (y::ys) = (x,y) :: (zip xs ys)
  | zip []      []      = []
  | zip _ _             = raise MatchFail;

(* ------------------------------------------------------------------------------------------- *)  
fun eq_GroundTerm( itree( inode(x1, _ ), children1), itree(inode(x2, _), children2 )) = (x1 = x2) andalso eq_GroundTerm_list (children1, children2)
  | eq_GroundTerm _     = raise General.Fail("Error in MATCHING.eq_GroundTerm: encountered non-ground term (system error).\n")

and eq_GroundTerm_list( t1 :: rest1, t2 :: rest2 ) 	= eq_GroundTerm(t1,t2) andalso eq_GroundTerm_list(rest1, rest2)
  | eq_GroundTerm_list( [], [] ) 					= true
  | eq_GroundTerm_list _ 							= false

(* ------------------------------------------------------------------------------------------- *)
fun CompareOrelseInsert( symbol_type, symbol_id, ground_tree, subst ) = 
																												
	let
	    fun aux [] = [(symbol_type,symbol_id,ground_tree)]
                                                                              
	      | aux (subst_list as (s_type,s_id,ground_t) :: rest) = 
					if (s_type,s_id) = (symbol_type,symbol_id) then (* previous binding exists, so we now must do an equality comparison  *)
																	if eq_GroundTerm(ground_tree, ground_t) then subst_list
																	else raise MatchFail
                    else (s_type,s_id,ground_t) :: aux rest
	in
	    aux subst
	end
																															
(* ------------------------------------------------------------------------------------------- *)
(* Note that a match_var (e.g., <foo>_1) cannot/should not match successfully with a ground 
   leaf node. The reason being that match vars only exist for nonterminal symbols NOT terminal 
   symbols. A leaf node in a ground tree is, by definition, a terminal.
*)
fun auxMatch( itree(imatch_var(symbol_type, symbol_id,_), []), ground_tree as itree(inode(x,_),child::children) , subst_list ) = 

								    if symbol_type = x then CompareOrelseInsert(symbol_type, symbol_id, ground_tree, subst_list)
                                                       else raise MatchFail
																										
  | auxMatch( itree(inode(root1,_), children1), itree(inode(root2,_), children2), subst_list ) = 
							(
								case root1 = root2 of
								     true  => foldr (fn ((t1, t2), s) => auxMatch(t1,t2,s)) subst_list (zip children1 children2) 
								   | false => raise MatchFail
							)
																										
  | auxMatch _ = raise MatchFail
																																
(* ------------------------------------------------------------------------------------------- *)

fun match( TERM (term, x1_info) , TERM (ground_tree, x2_info), NONE                        ) = NONE
  | match( TERM (term, x1_info) , TERM (ground_tree, x2_info), sigma as SOME( subst_list ) ) = 
											
										let
					(* 						val _ = METRICS.matchCall(); *)
					(*						val _ = METRICS.startMatchIntervalClock(); *)
												
											(*use standard matching algorithm *)
        	                                val new_sigma = SOME( auxMatch(term, ground_tree, subst_list) )
															handle MatchFail => 	let
																				val (wildcard_match, t1, t2) = WILDCARD.isWild(term,ground_tree)
																			in
																				if wildcard_match andalso WILDCARD.associativeMatch(t1,t2) 
																				then sigma
																				else (
																						(* METRICS.matchFail(); *)
																						NONE
																					)
															end
										in
					(*						METRICS.pauseMatchIntervalClock(); *)
											new_sigma
										end
																										
  | match (t1, t2, _) = let
							val msg = "Error in MATCHING.match.\n"
						in
							print msg;
							raise RUNTIME.error([t1,t2], General.Fail(msg), ABSTRACT.printTree, ABSTRACT.getExprInfo, CONCRETE_REPRESENTATION.printNodeInfo)
						end
																								
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*                                    SUBSTITUTION                                             *)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
																										
(* ------------------------------------------------------------------------------------------- *)							
(* ------------------------------------------------------------------------------------------- *)
(* the presence of free-variables in the rhs of a rewrite should be statically detected        *)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *) 
fun concreteTraversal subst_list term =
					let
					    (* --------------------------------------------------------------------------------- *)
					    fun applySubst(  t as (symbol_type, symbol_id, _), children, (s_type,s_id,ground_t)::rest ) = 
								if (symbol_type, symbol_id) = (s_type,s_id) then ground_t else applySubst(t, children, rest)
								
					      | applySubst( (symbol_type, symbol_id, x_info) , children, []   ) = itree( imatch_var(symbol_type, symbol_id, x_info), children ); 
																										
					    (* --------------------------------------------------------------------------------- *)
					    fun traverse( itree(imatch_var(symbol_type, symbol_id, x_info), children)	)  = 	applySubst( (symbol_type, symbol_id, x_info), children, subst_list )
					      | traverse( itree(node,children)                      	   		       	)  = 	let
																												val new_children = map traverse children
																											in
																												itree(node,new_children)
																											end
					    (* --------------------------------------------------------------------------------- *)
					in
						traverse term
					end 

																						
(* ------------------------------------------------------------------------------------------- *)
fun subst(SOME( subst_list ) , expr ) =
    let

        (* --------------------------------------------------------------------------------- *)

	fun   traverse (PROG            (decl_list, x_info)          ) = PROG           ( map traverse decl_list, x_info )
		| traverse (RECURSIVE       (id, arg_list, expr, x_info) ) = RECURSIVE      ( id, map traverse arg_list, traverse expr, x_info )     
		| traverse (NON_RECURSIVE   (id, expr, x_info)           ) = NON_RECURSIVE  ( id, traverse expr, x_info ) 
																														
        | traverse (ANDALSO         (expr1,expr2, x_info)        ) = ANDALSO        ( traverse expr1, traverse expr2, x_info )     
		| traverse (ORELSE          (expr1,expr2, x_info)        ) = ORELSE         ( traverse expr1, traverse expr2, x_info )   
		| traverse (NOT             (expr, x_info)               ) = NOT            ( traverse expr, x_info )
																													
		| traverse (MATCH           (expr1,expr2, x_info)        ) = MATCH          ( traverse expr1, traverse expr2, x_info )     
		| traverse (BIND            (s_ref,expr2, x_info)        ) = BIND           ( s_ref         , traverse expr2, x_info )                                                                                       
																																	
		| traverse (CHOICE          (expr1,expr2, x_info)        ) = CHOICE         ( traverse expr1, traverse expr2, x_info )     
		| traverse (LCHOICE         (expr1,expr2, x_info)        ) = LCHOICE        ( traverse expr1, traverse expr2, x_info )     
		| traverse (RCHOICE         (expr1,expr2, x_info)        ) = RCHOICE        ( traverse expr1, traverse expr2, x_info )     
		| traverse (LSEQ            (expr1,expr2, x_info)        ) = LSEQ           ( traverse expr1, traverse expr2, x_info )     
		| traverse (RSEQ            (expr1,expr2, x_info)        ) = RSEQ           ( traverse expr1, traverse expr2, x_info )     
		| traverse (LSTAR           (expr1,expr2, x_info)        ) = LSTAR          ( traverse expr1, traverse expr2, x_info )     
		| traverse (RSTAR           (expr1,expr2, x_info)        ) = RSTAR          ( traverse expr1, traverse expr2, x_info )     
																												
        (* --------------------------------------------------------------------------------- *)
        (* 
            The scoping rules of TL are based on the principle of "single declaration". 
            A scope boundary is delineated by a label and NOT by a rewrite rule. This
            means that the strategic expression associated with a label defines a single
            scope! This prohibits/disallows the concept of nested scopes.

            In TL, the inlining of label with its body requires the renaming of all 
            schema variables in the body prior to the inlining operation. 
        *)
       (* --------------------------------------------------------------------------------- *)
		| traverse (RULE      (lhs,rhs, x_info)      ) = 	let
																val new_lhs = traverse lhs 
																val new_rhs = traverse rhs
															in
																RULE( new_lhs, new_rhs, x_info ) 
															end
																					
		| traverse (COND_RULE (lhs,rhs,cond, x_info) ) = 	let
																val new_lhs  = traverse lhs
																val new_rhs  = traverse rhs
																val new_cond = traverse cond 
															in
																COND_RULE( new_lhs, new_rhs, new_cond, x_info ) 
															end   
        (* --------------------------------------------------------------------------------- *)
																						
		| traverse (B_OR            (expr1,expr2, x_info)        ) = B_OR           ( traverse expr1, traverse expr2, x_info )     
		| traverse (B_AND           (expr1,expr2, x_info)        ) = B_AND          ( traverse expr1, traverse expr2, x_info )     
																																
		| traverse (EQ              (expr1,expr2, x_info)        ) = EQ             ( traverse expr1, traverse expr2, x_info )     
		| traverse (NEQ             (expr1,expr2, x_info)        ) = NEQ            ( traverse expr1, traverse expr2, x_info )     
		| traverse (LEQ             (expr1,expr2, x_info)        ) = LEQ            ( traverse expr1, traverse expr2, x_info )     
		| traverse (LT              (expr1,expr2, x_info)        ) = LT             ( traverse expr1, traverse expr2, x_info )      
		| traverse (GEQ             (expr1,expr2, x_info)        ) = GEQ            ( traverse expr1, traverse expr2, x_info )      
		| traverse (GT              (expr1,expr2, x_info)        ) = GT             ( traverse expr1, traverse expr2, x_info )      
																																
		| traverse (CONCAT          (expr1,expr2, x_info)        ) = CONCAT         ( traverse expr1, traverse expr2, x_info )     
																															
		| traverse (PLUS            (expr1,expr2, x_info)        ) = PLUS           ( traverse expr1, traverse expr2, x_info )     
		| traverse (MINUS           (expr1,expr2, x_info)        ) = MINUS          ( traverse expr1, traverse expr2, x_info )     
		| traverse (TIMES           (expr1,expr2, x_info)        ) = TIMES          ( traverse expr1, traverse expr2, x_info )     
		| traverse (DIVIDE          (expr1,expr2, x_info)        ) = DIVIDE         ( traverse expr1, traverse expr2, x_info )     
		| traverse (DIV             (expr1,expr2, x_info)        ) = DIV            ( traverse expr1, traverse expr2, x_info )      
		| traverse (MOD             (expr1,expr2, x_info)        ) = MOD            ( traverse expr1, traverse expr2, x_info )     
																																
		| traverse (APP             (expr1,expr2, x_info)        ) = APP            ( traverse expr1, traverse expr2       , x_info )     
		| traverse (ITERATOR        (id, arg_list, x_info)       ) = ITERATOR       ( id            , map traverse arg_list, x_info )     
                                                                                      
		| traverse (BOOL            (value, x_info)              ) = BOOL           ( value, x_info ) 
		| traverse (INT             (value, x_info)              ) = INT            ( value, x_info ) 
		| traverse (REAL            (value, x_info)              ) = REAL           ( value, x_info ) 
		| traverse (STRING          (value, x_info)              ) = STRING         ( value, x_info ) 
		| traverse (IDENTIFIER      (value, x_info)              ) = IDENTIFIER     ( value, x_info )
		| traverse (REF             tuple         		         ) = REF            tuple
																						
		| traverse (TERM            (a_tree, x_info)             ) = TERM           ( concreteTraversal subst_list a_tree, x_info )
                                      
		| traverse ( LIBRARY_CALL_0 (id, x_info)                 ) = LIBRARY_CALL_0 ( id, x_info )
		| traverse ( LIBRARY_CALL   (id,expr_list, x_info)       ) = LIBRARY_CALL   ( id, map traverse expr_list, x_info )     
                                                                                
		| traverse (ID   x_info                                  ) = ID  ( x_info )
		| traverse (SKIP x_info                                  ) = SKIP( x_info )
		| traverse (FAIL x_info                                  ) = FAIL( x_info )
                                                                               
		| traverse (BANG            (expr, x_info)               ) = BANG           ( traverse expr, x_info )
		| traverse (TILDE           (expr, x_info)               ) = TILDE          ( traverse expr, x_info )
																														
		| traverse (TRANSIENT       (expr, x_info)               ) = TRANSIENT      ( traverse expr, x_info )
		| traverse (OPAQUE          (expr, x_info)               ) = OPAQUE         ( traverse expr, x_info )
		| traverse (RAISE           (expr, x_info)               ) = RAISE          ( traverse expr, x_info )
		| traverse (HIDE            (expr, x_info)               ) = HIDE           ( traverse expr, x_info )
		| traverse (LIFT            (expr, x_info)               ) = LIFT           ( traverse expr, x_info )
                                                                                                               
		| traverse (MAPL            (expr, x_info)               ) = MAPL           ( traverse expr, x_info )
		| traverse (MAPR            (expr, x_info)               ) = MAPR           ( traverse expr, x_info )
		| traverse (MAPB            (expr, x_info)               ) = MAPB           ( traverse expr, x_info )
																												
        | traverse (FOLD_CHOICE     (expr, x_info)               ) = FOLD_CHOICE    ( traverse expr, x_info )
        | traverse (FOLD_LCHOICE    (expr, x_info)               ) = FOLD_LCHOICE   ( traverse expr, x_info )
        | traverse (FOLD_RCHOICE    (expr, x_info)               ) = FOLD_RCHOICE   ( traverse expr, x_info )
        | traverse (FOLD_LSEQ       (expr, x_info)               ) = FOLD_LSEQ      ( traverse expr, x_info )
        | traverse (FOLD_RSEQ       (expr, x_info)               ) = FOLD_RSEQ      ( traverse expr, x_info )
        | traverse (FOLD_LSTAR      (expr, x_info)               ) = FOLD_LSTAR     ( traverse expr, x_info )
        | traverse (FOLD_RSTAR      (expr, x_info)               ) = FOLD_RSTAR     ( traverse expr, x_info )
																										
        | traverse (FOLDS_CHOICE     (expr, x_info)              ) = FOLDS_CHOICE   ( traverse expr, x_info )
        | traverse (FOLDS_LCHOICE    (expr, x_info)              ) = FOLDS_LCHOICE  ( traverse expr, x_info )
        | traverse (FOLDS_RCHOICE    (expr, x_info)              ) = FOLDS_RCHOICE  ( traverse expr, x_info )
        | traverse (FOLDS_LSEQ       (expr, x_info)              ) = FOLDS_LSEQ     ( traverse expr, x_info )
        | traverse (FOLDS_RSEQ       (expr, x_info)              ) = FOLDS_RSEQ     ( traverse expr, x_info )
        | traverse (FOLDS_LSTAR      (expr, x_info)              ) = FOLDS_LSTAR    ( traverse expr, x_info )
        | traverse (FOLDS_RSTAR      (expr, x_info)              ) = FOLDS_RSTAR    ( traverse expr, x_info )
																										
		| traverse TRUE	 				                            = raise General.Fail("Error in MATCHING.innerSubst.traverse: encountered the internal control value TRUE.\n")																										
		| traverse FALSE	            			 				= raise General.Fail("Error in MATCHING.innerSubst.traverse: encountered the internal control value FALSE.\n")
		| traverse (SIGNATURE _)           			 				= raise General.Fail("Error in MATCHING.innerSubst.traverse: encountered SIGNATURE.\n")		
		| traverse (LIST _)    		       			 				= raise General.Fail("Error in MATCHING.innerSubst.traverse: encountered LIST.\n")				
    in
        traverse expr
    end
										
  | subst (_, t)  =  let
						val msg = "Error in MATCHING.innerSubst: match has failed.\n"
					 in
						print msg;
						raise RUNTIME.error([t], General.Fail(msg), ABSTRACT.printTree, ABSTRACT.getExprInfo, CONCRETE_REPRESENTATION.printNodeInfo)
					 end
										
(* ------------------------------------------------------------------------------------------- *)
end; (* struct *)
(* ------------------------------------------------------------------------------------------- *)