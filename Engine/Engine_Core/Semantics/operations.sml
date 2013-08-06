
(* ------------------------------------------------------------------------------------------- *)
signature OPERATIONS_SIG =
sig

	val booleanOr		: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val booleanAnd		: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR

	val control_leq		: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR -> bool
	val control_lt		: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR -> bool
	val control_geq		: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR -> bool
	val control_gt		: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR -> bool	
	
	val eq				: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val neq				: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val geq				: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val gt				: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val leq				: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val lt				: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR

	val stringConcat	: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR

	val add				: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val subtract		: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val multiply 		: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val divide			: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val intDiv			: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val modulus 		: ABSTRACT_REPRESENTATION.EXPR * ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR

	val tilde			: ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
	val bang			: ABSTRACT_REPRESENTATION.EXPR * CONCRETE_REPRESENTATION.NODE_INFO -> ABSTRACT_REPRESENTATION.EXPR
end;
(* ------------------------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------------------------- *)
structure OPERATIONS : OPERATIONS_SIG =
struct

open ABSTRACT_REPRESENTATION;



(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun getNumericValue( TERM (term, x_info) ) = 
				let
                    val v_str = CONCRETE.getLeaf term
				    val v1    = Int.fromString(v_str)
				in
				         if isSome(v1)                    then INT  ( valOf v1, x_info )
				    else if isSome(Real.fromString v_str) then REAL ( v_str   , x_info )
		                                                                   
				    else raise General.Fail("Error in OPERATIONS.getNumericValue.\n")
				end
																
  | getNumericValue( INT    x ) = INT    x
  | getNumericValue( REAL   x ) = REAL   x
  | getNumericValue _           = raise General.Fail("Error in OPERATIONS.getNumericValue.\n");

(* ------------------------------------------------------------------------------------------- *)
fun getIntegerValue( TERM (term, x_info ) ) = 
				let
		            val v_str = CONCRETE.getLeaf term
				    val v     = Int.fromString(v_str)
				in
				    if isSome(v) then INT ( valOf v, x_info )
				                 else raise General.Fail("Error in OPERATIONS.getIntegerValue.\n")
				end
																		
  | getIntegerValue( INT x )     = INT x
  | getIntegerValue _            = raise General.Fail("Error in OPERATIONS.getIntegerValue.\n");
																
(* ------------------------------------------------------------------------------------------- *)
fun getRealValue( TERM (term, x_info) ) = 
				let
                    val v_str = CONCRETE.getLeaf term
				    val v     = Real.fromString(v_str)
				in
				    if isSome(v) then REAL( v_str, x_info )
				                 else raise General.Fail("Error in OPERATIONS.getRealValue.\n")                            
				end
											
  | getRealValue( REAL x )    = REAL x
  | getRealValue _            = raise General.Fail("Error in OPERATIONS.getRealValue.\n");
																	
(* ------------------------------------------------------------------------------------------- *)
fun getStringValue( TERM (term, x_info) ) = STRING ( CONCRETE.getLeaf term, x_info )
  | getStringValue( STRING x )            = STRING x
  | getStringValue _                      = raise General.Fail("Error in OPERATIONS.getStringValue.\n");
																			
(* ------------------------------------------------------------------------------------------- *)
fun getBooleanValue( TERM (term, x_info ) ) = 
					let
						val v_str = CONCRETE.getLeaf term
						val v     = Bool.fromString(v_str)
					in
				       if isSome(v) then BOOL ( valOf v, x_info )
				       else raise General.Fail("Error in OPERATIONS.getBooleanValue.\n")
				   end
													
  | getBooleanValue( BOOL x )    = BOOL x
  | getBooleanValue _            = raise General.Fail("Error in OPERATIONS.getBooleanValue.\n");
																	
(* ------------------------------------------------------------------------------------------- *)
fun convertToString( INT    (v   , _) )  = Int.toString  v
  | convertToString( BOOL   (v   , _) )  = Bool.toString v
  | convertToString( TERM   (term, _) )  = CONCRETE.getLeaf term
  | convertToString( REAL   (v   , _) )  = v
  | convertToString( STRING (v   , _) )  = v
  | convertToString _                    = raise General.Fail("Error in OPERATIONS.convertToString.\n");
																										
(* ------------------------------------------------------------------------------------------- *)
fun valueToString( INT    (v    , _) ) = Int.toString v
  | valueToString( REAL   (v_str, _) ) = v_str
  | valueToString( STRING (v_str, _) ) = v_str
  | valueToString( BOOL   (v    , _) ) = Bool.toString v
  | valueToString _                    = raise General.Fail("Error in OPERATIONS.valueToString.\n");
																					
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun orBooleanValues( [BOOL (v1, x1_info) , BOOL (v2, x2_info)], _ )  = BOOL ( (v1 orelse v2), mergeNodeInfo(x1_info, x2_info) )
  | orBooleanValues _                                                = raise General.Fail("Error in OPERATIONS.orBooleanValues: inappropriate types. \n");
																										
(* ------------------------------------------------------------------------------------------- *)
fun andBooleanValues( [BOOL (v1, x1_info) , BOOL (v2, x2_info)], _ ) = BOOL ((v1 andalso v2), mergeNodeInfo(x1_info, x2_info))
  | andBooleanValues _                                               = raise General.Fail("Error in OPERATIONS.orBooleanValues: inappropriate types. \n");
																												
(* ------------------------------------------------------------------------------------------- *)
fun booleanNot( [BOOL  (v, x_info)], _ ) = BOOL ((not v), x_info)
  | booleanNot _                         = raise General.Fail("Error in OPERATIONS.booleanNot: applying ! on incompatible type.\n");
																										
(* ------------------------------------------------------------------------------------------- *)
fun eqOp ( [expr1, expr2], x_info ) = BOOL( expr1 =  expr2, x_info )
  | eqOp _                          = raise General.Fail("Error in OPERATIONS.eqOp.\n");
																			
fun neqOp( [expr1, expr2], x_info ) = BOOL( expr1 <> expr2, x_info )
  | neqOp _                         = raise General.Fail("Error in OPERATIONS.neqOp.\n");
																							
fun geqOp( [expr1, expr2] : string list, x_info ) = BOOL( expr1 >= expr2, x_info )
  | geqOp _                                       = raise General.Fail("Error in OPERATIONS.geqOp.\n");
																									
fun gtOp ( [expr1, expr2] : string list, x_info ) = BOOL( expr1 >  expr2, x_info )
  | gtOp _                                        = raise General.Fail("Error in OPERATIONS.gtOp.\n");         
																					
fun leqOp( [expr1, expr2] : string list, x_info ) = BOOL( expr1 <= expr2, x_info )
  | leqOp _                                       = raise General.Fail("Error in OPERATIONS.leqOp.\n");         
																						
fun ltOp ( [expr1, expr2] : string list, x_info ) = BOOL( expr1 <  expr2, x_info )
  | ltOp _                                        = raise General.Fail("Error in OPERATIONS.ltqOp.\n");         
																							
(* ------------------------------------------------------------------------------------------- *)
fun concatenateStrings( [STRING (v1, x1_info) , STRING (v2, x2_info) ], _ ) = STRING (v1 ^ v2, mergeNodeInfo(x1_info, x2_info) )
  | concatenateStrings _                                                    = raise General.Fail("Error in OPERATIONS.concatenateStrings: attempting string concatenation on non-string types.\n");
																													
(* ------------------------------------------------------------------------------------------- *)
fun addNumericValues( [INT  (v1, x1_info)    , INT  (v2, x2_info)     ], _ ) = INT (v1 + v2, mergeNodeInfo(x1_info, x2_info) )
  | addNumericValues( [REAL (v1_str, x1_info), REAL (v2_str, x2_info) ], _ ) = 
								let
									val v1 = valOf(Real.fromString v1_str)
									val v2 = valOf(Real.fromString v2_str)
								in
									REAL( Real.toString(v1 + v2), mergeNodeInfo(x1_info, x2_info) )
								end
										
  | addNumericValues _				    = raise General.Fail("Error in OPERATIONS.addNumericValues: attempting add on incompatible types.\n");
																	
(* ------------------------------------------------------------------------------------------- *)
fun subtractNumericValues ( [INT  (v1, x1_info)    , INT  (v2, x2_info)    ], _ ) = INT (v1 - v2, mergeNodeInfo(x1_info, x2_info))
  | subtractNumericValues ( [REAL (v1_str, x1_info), REAL (v2_str, x2_info)], _ ) = 
								let
									val v1 = valOf(Real.fromString v1_str)
									val v2 = valOf(Real.fromString v2_str)
								in
									REAL( Real.toString(v1 - v2), mergeNodeInfo(x1_info, x2_info) )
								end
                                                               
  | subtractNumericValues _                              = raise General.Fail("Error in OPERATIONS.subtractNumericValues: attempting subtraction on incompatible types.\n");
															
(* ------------------------------------------------------------------------------------------- *)
fun multiplyNumericValues( [INT  (v1, x1_info)    , INT  (v2, x2_info)    ], _ ) = INT (v1 * v2, mergeNodeInfo(x1_info,x2_info))
  | multiplyNumericValues( [REAL (v1_str, x1_info), REAL (v2_str, x2_info)], _ ) = 
								let
									val v1 = valOf(Real.fromString v1_str)
									val v2 = valOf(Real.fromString v2_str)
						        in
						            REAL( Real.toString(v1 * v2), mergeNodeInfo(x1_info, x2_info) )
						        end
                                                              
  | multiplyNumericValues _                             = raise General.Fail("Error in OPERATIONS.multiplyNumericValues: attempting multiplication on incompatible types.\n");
																					
(* ------------------------------------------------------------------------------------------- *)
fun divideNumericValues( [REAL (v1_str, x1_info), REAL (v2_str, x2_info)], _ ) =
							let
								val v1 = valOf(Real.fromString v1_str)
								val v2 = valOf(Real.fromString v2_str)
					 		in
								REAL( Real.toString(v1 / v2), mergeNodeInfo(x1_info, x2_info) )
							end
																							
  | divideNumericValues _                         =  	raise General.Fail("Error in OPERATIONS.divideNumericValues: attempting division on non-real types.\n");
																				
(* ------------------------------------------------------------------------------------------- *)
fun intDivNumericValues( [INT (v1,x1_info), INT (v2, x2_info)], _ ) = INT (v1 div v2, mergeNodeInfo(x1_info, x2_info))
  | intDivNumericValues _                                           = raise General.Fail("Error in OPERATIONS.intDivNumericValues: attempting integer divide on non-integer types.\n");
																			
(* ------------------------------------------------------------------------------------------- *)
fun modulusNumericValues( [INT (v1, x1_info), INT (v2, x2_info)], _ ) = INT (v1 mod v2, mergeNodeInfo(x1_info,x2_info) )
  | modulusNumericValues _		                                      = raise General.Fail("Error in OPERATIONS.modulusNumericValues: attempting mod on non-integer types.\n");
																					
(* ------------------------------------------------------------------------------------------- *)
fun unaryMinus( [INT  (v, x_info)    ], _ ) = INT (~v, x_info)
  | unaryMinus( [REAL (v_str, x_info)], _ ) = 
						let
							val v = valOf(Real.fromString v_str)
		                in
		                    REAL( Real.toString(~v), x_info )
                        end
													
  | unaryMinus _               = raise General.Fail("Error in OPERATIONS.unaryMinus: applying unary minus on incompatible type.\n");
																		
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun makeStructure( [TERM (term1, _), TERM (term2, _)] , expr, x_info ) = 
							if CONCRETE.eqLinearInternalStructure( term1, term2 ) 
							then TERM (CONCRETE.replaceLeaf( term1, valueToString ( expr ) ), x_info )
																	
							else raise General.Fail("Error in OPERATIONS.makeStructure: attempting to perform an operation on trees having different structures.\n")
																						
  | makeStructure( [TERM (term, _) , _              ] , expr, x_info ) = TERM (CONCRETE.replaceLeaf( term, valueToString ( expr ) ), x_info )
  | makeStructure( [_              , TERM (term, _) ] , expr, x_info ) = TERM (CONCRETE.replaceLeaf( term, valueToString ( expr ) ), x_info )
  | makeStructure( [_         , _                   ] , expr, x_info ) = expr
  | makeStructure( [TERM (term, _)                  ] , expr, x_info ) = TERM (CONCRETE.replaceLeaf( term, valueToString ( expr ) ), x_info )
  | makeStructure( [_                               ] , expr, x_info ) = expr
  | makeStructure _                                                    = raise General.Fail("Error in OPERATIONS.makeStructure.\n");
																							
(* ------------------------------------------------------------------------------------------- *)
fun performOperation( expr_list, operation, getValue, x_info ) = 
							let
							    val result = operation(map getValue expr_list, x_info)
							in
							    makeStructure( expr_list, result, x_info )
							end
 
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)

fun booleanOr   ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , orBooleanValues        , getBooleanValue, x_info);
fun booleanAnd  ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , andBooleanValues       , getBooleanValue, x_info);
																																	
fun eq          ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , eqOp                   , convertToString, x_info); 
fun neq         ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , neqOp                  , convertToString, x_info);
fun geq         ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , geqOp                  , convertToString, x_info);
fun gt          ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , gtOp                   , convertToString, x_info);
fun leq         ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , leqOp                  , convertToString, x_info);
fun lt          ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , ltOp                   , convertToString, x_info);
                                                                                                    
fun stringConcat( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , concatenateStrings     , getStringValue , x_info);
                                                                                                      
fun add         ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , addNumericValues       , getNumericValue, x_info);
fun subtract    ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , subtractNumericValues  , getNumericValue, x_info);
fun multiply    ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , multiplyNumericValues  , getNumericValue, x_info);
fun divide      ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , divideNumericValues    , getRealValue   , x_info);
fun intDiv      ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , intDivNumericValues    , getIntegerValue, x_info);
fun modulus     ( expr1, expr2, x_info ) = performOperation( [expr1,expr2] , modulusNumericValues   , getIntegerValue, x_info);
																							
fun tilde       ( expr, x_info )         = performOperation( [expr]        , unaryMinus             , getNumericValue, x_info);
fun bang        ( expr, x_info )         = performOperation( [expr]        , booleanNot             , getBooleanValue, x_info);
																																							
(* ------------------------------------------------------------------------------------------- *)
(* control-level expressions. E.g., lhs -> rhs if { <number>_1 < <number>_2 }                  *)
(* ------------------------------------------------------------------------------------------- *)
fun control_leq ( expr1, expr2 ) = 
	let
		val v1 = convertToString expr1
		val v2 = convertToString expr2
	in
		v1 <= v2
	end
																				
fun control_lt ( expr1, expr2 ) = 
	let
		val v1 = convertToString expr1
		val v2 = convertToString expr2
	in
		v1 < v2
	end
															
fun control_geq ( expr1, expr2 ) = 
	let
		val v1 = convertToString expr1
		val v2 = convertToString expr2
	in
		v1 >= v2
	end
														
fun control_gt ( expr1, expr2 ) = 
	let
		val v1 = convertToString expr1
		val v2 = convertToString expr2
	in
		v1 > v2
	end
											
(* ------------------------------------------------------------------------------------------- *)
end;  (* struct *)
(* ------------------------------------------------------------------------------------------- *)