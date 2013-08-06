
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

*)


(* ------------------------------------------------------------------------------------------- *)
structure STATE_MODEL =
struct

open ABSTRACT_REPRESENTATION;


datatype CONTEXT = FIRST_ORDER | HIGHER_ORDER;

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
type STATE = { 
               application_stack   : int, 
               reduction_stack     : int,
               strategy            : EXPR list, 
               first_order_result  : EXPR list,     (* a term -- this is modelled as a list to permit accumulation (e.g., mapL) *)
               higher_order_result : EXPR list      (* a strategies list *)
             }


(* ------------------------------------------------------------------------------------------- *)
fun getTerm             ( state:STATE ) = hd( #first_order_result(state) ) handle Empty => raise General.Fail("Error in STATE_MODEL.getTerm.\n");

fun getApplicationStack ( state:STATE ) = #application_stack  ( state )
fun getReductionStack   ( state:STATE ) = #reduction_stack    ( state )

fun getFirstOrderResult ( state:STATE ) = #first_order_result ( state ) 
fun getHigherOrderResult( state:STATE ) = #higher_order_result( state )

fun getSingleStrategy   ( state:STATE ) = 
    let
        fun aux [ s ] = s
          | aux _     = raise General.Fail("Error in state_model.getSingleStrategy: compiler error.\n")
          
        val sList = #strategy ( state )
    in
        aux sList
    end
    
fun getDualStrategy   ( state:STATE ) = 
    let
        fun aux (dual as [ s1, s2 ]) = dual
          | aux _     = raise General.Fail("Error in state_model.getDualStrategy: compiler error.\n")
          
        val sList = #strategy ( state )
    in
        aux sList
    end

(* ------------------------------------------------------------------------------------------- *)
fun printState (state:STATE) =
			let
				val v1 = #application_stack  ( state )
				val v2 = #reduction_stack    ( state )
				val v3 = #strategy           ( state )
				val v4 = #first_order_result ( state ) 
				val v5 = #higher_order_result( state )
			in
				print("\n\n@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n\n{\n");
				print("\n application_stack = " ^ Int.toString(v1));
				print("\n reduction_stack   = " ^ Int.toString(v2));
				print("\n strategy          = "); map ABSTRACT.printTree v3;
				print("\n first_order_result = \n"); map (fn term => ( print("\n=========================BEGIN===========================================\n"); 
                                                                       ABSTRACT.printTree term; 
                                                                       print("\n=========================END=============================================\n")
                                                                     )
                                                          ) v4;		
																				
				print("\n higher_order_result = \n"); map (fn term => ( print("\n=========================BEGIN===========================================\n"); 
                                                                        ABSTRACT.printTree term; 
                                                                        print("\n=========================END=============================================\n")
                                                                      )
                                                          ) v5;		
																													
				print("\n}\n@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@@\n\n")
			end
																				
(* ------------------------------------------------------------------------------------------- *)
(* assume that TL's type system will catch errors associated with inappropriate list length         *)
fun createResult( state_record:STATE ) = (
											#first_order_result (state_record)  ,
											#higher_order_result(state_record) 
                                         )
						         
(* ------------------------------------------------------------------------------------------- *)
fun makeBinaryCombiningFunction( combinator_str, x_info ) =

		case combinator_str of	
			  "CHOICE"    => (fn (s1,s2) => CHOICE (s1,s2, x_info) ) 
			| "LCHOICE"   => (fn (s1,s2) => LCHOICE(s1,s2, x_info) ) 
			| "RCHOICE"   => (fn (s1,s2) => RCHOICE(s1,s2, x_info) ) 
			| "LSEQ"      => (fn (s1,s2) => LSEQ   (s1,s2, x_info) ) 
			| "RSEQ"      => (fn (s1,s2) => RSEQ   (s1,s2, x_info) ) 
			| "LSTAR"     => (fn (s1,s2) => LSTAR  (s1,s2, x_info) ) 
			| "RSTAR"     => (fn (s1,s2) => RSTAR  (s1,s2, x_info) ) 
														
			| _         => raise General.Fail("Error in SEMANTICS.makeCombiningFunction.\n")

(* ------------------------------------------------------------------------------------------- *)
fun makeUnaryCombiningFunction( combinator_str, x_info ) =

		case combinator_str of	
			  "TRANSIENT" => (fn s1    => TRANSIENT(s1, x_info) ) 
			| "OPAQUE"    => (fn s1    => OPAQUE   (s1, x_info) ) 
			| "RAISE"     => (fn s1    => RAISE    (s1, x_info) ) 
			| "HIDE"      => (fn s1    => HIDE     (s1, x_info) ) 
			| "LIFT"      => (fn s1    => LIFT     (s1, x_info) ) 
			| _           => raise General.Fail("Error in SEMANTICS.makeUnaryCombiningFunction.\n")

(* ------------------------------------------------------------------------------------------- *)
fun eqSKIP( SKIP _ ) = true
  | eqSKIP _         = false
  
fun buildStrategyReturned(combinator_str, s1, s2, x_info) = 

 	         if eqSKIP s1 andalso eqSKIP s2 then SKIP x_info
	    else if eqSKIP s1                   then s2
 	    else if eqSKIP s2                   then s1
															
	    else makeBinaryCombiningFunction (combinator_str, x_info)(s1,s2);
																
(* ------------------------------------------------------------------------------------------- *)
fun build2StrategyListReturned(combinator_str, [s1], [s2], x_info) = [ makeBinaryCombiningFunction (combinator_str, x_info)(s1,s2) ]
  | build2StrategyListReturned(combinator_str, []  , [s2], _     ) = [s2]
  | build2StrategyListReturned(combinator_str, [s1], []  , _     ) = [s1]
  | build2StrategyListReturned(combinator_str, []  , []  , _     ) = [] 
  | build2StrategyListReturned(combinator_str, s1_list  , s2_list  , _  ) =  
         RUNTIME.error(s1_list @ s2_list, General.Fail("Error in STATE_MODEL.build2StrategyListReturned. Combinator = " ^ combinator_str ^ "\n"), 
		               ABSTRACT.printTree, ABSTRACT.getExprInfo, CONCRETE_REPRESENTATION.printNodeInfo );  
											
(* ------------------------------------------------------------------------------------------- *)
fun buildStar2StrategyListReturned(combinator_str, [s1], [s2], x_info) = [ makeBinaryCombiningFunction (combinator_str, x_info)(s1,s2) ]
  | buildStar2StrategyListReturned(combinator_str, []  , [s2], _     ) = []
  | buildStar2StrategyListReturned(combinator_str, [s1], []  , _     ) = []
  | buildStar2StrategyListReturned(combinator_str, []  , []  , _     ) = [] 
  | buildStar2StrategyListReturned(combinator_str, s1_list  , s2_list  , _  ) =  
         RUNTIME.error(s1_list @ s2_list, General.Fail("Error in STATE_MODEL.build2StrategyListReturned. Combinator = " ^ combinator_str ^ "\n"), 
		               ABSTRACT.printTree, ABSTRACT.getExprInfo, CONCRETE_REPRESENTATION.printNodeInfo );  
					   
  (* ------------------------------------------------------------------------------------------- *)
fun build1StrategyReturned( [s1], x_info ) = s1
  | build1StrategyReturned( []  , x_info ) = SKIP x_info 
  | build1StrategyReturned( s_list, _    ) = 
			RUNTIME.error(s_list, General.Fail("Error in STATE_MODEL.build1StrategyReturned.\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, CONCRETE_REPRESENTATION.printNodeInfo);    
											
  (* ------------------------------------------------------------------------------------------- *)
fun build1StrategyListReturned(combinator_str, [], x_info)      = []  
  | build1StrategyListReturned(combinator_str, [s1], x_info)    = [makeUnaryCombiningFunction (combinator_str, x_info) s1  ]
  | build1StrategyListReturned(combinator_str, s_list, x_info)  = 
       RUNTIME.error(s_list, General.Fail("Error in STATE_MODEL.build1StrategyListReturned. Combinator = " ^ combinator_str ^ "\n"), ABSTRACT.printTree, ABSTRACT.getExprInfo, CONCRETE_REPRESENTATION.printNodeInfo);  
																
(* ------------------------------------------------------------------------------------------- *)
fun buildHigherOrderReturned(state1, state2) =
	let
	    fun eqListSKIP( []                   ) = true
              | eqListSKIP( (SKIP _) :: rest ) = eqListSKIP rest
              | eqListSKIP _                   = false
															
	    val higher_order1 = getHigherOrderResult state1
        val higher_order2 = getHigherOrderResult state2
	    val flag1         = eqListSKIP higher_order1
        val flag2         = eqListSKIP higher_order2
	in
 	         if flag1 andalso flag2 then []
	    else if flag1               then higher_order2
 	    else if flag2               then higher_order1
	    else                             higher_order1 @ higher_order2
	end;
													
(* ------------------------------------------------------------------------------------------- *)
fun associateRight(combining_function, s_list, s_list_length) = 
	[ foldr	combining_function 
			(List.last s_list) 
			(List.take(s_list, s_list_length - 1)) 
	]
												  
fun associateLeft(combining_function, s_list, s_list_length) =
	let
		fun aux( s :: [] ) = s
		  | aux( s::rest ) = 
			let
				val s_result = aux(rest)
			in
				combining_function( s_result, s)
			end
		  | aux _          = raise General.Fail("Error in SEMANTICS.associateLef.aux.\n")
					
		val s_list_rev = List.rev s_list
	in
		[ aux s_list_rev ]
	end
						
fun foldStrategyList( combinator_str, state, x_info ) =
	let
	    val s_list             = getHigherOrderResult state
	    val s_list_length      = length(s_list)
 	    val combining_function = makeBinaryCombiningFunction (combinator_str, x_info)
	in
		if s_list_length = 0 
		then []
		else case combinator_str of	
			  "CHOICE"    => associateLeft (combining_function, s_list, s_list_length)
			| "LCHOICE"   => associateRight(combining_function, s_list, s_list_length)
			| "RCHOICE"   => associateLeft (combining_function, s_list, s_list_length)
			| "LSEQ"      => associateRight(combining_function, s_list, s_list_length)
			| "RSEQ"      => associateLeft (combining_function, s_list, s_list_length)
			| "LSTAR"     => associateRight(combining_function, s_list, s_list_length)
			| "RSTAR"     => associateLeft (combining_function, s_list, s_list_length)
														
			| _           => raise General.Fail("Error in SEMANTICS.foldStrategyList.\n")
															
	end;
																					
(* ------------------------------------------------------------------------------------------- *)
fun heteroFoldFromLeft( combinator_str, state, x_info ) =
	let          
	    val s_list             = getHigherOrderResult  state
	    val s                  = getSingleStrategy           state
  	    val combining_function = makeBinaryCombiningFunction (combinator_str, x_info)
 	in
        foldr combining_function s s_list
	end;

(* ------------------------------------------------------------------------------------------- *)
end;  (* struct *)
(* ------------------------------------------------------------------------------------------- *)