(*

  This enhanced prettyprinter may run significantly slower than the original. However, it supports
  a matching function that enables a leftmost derivation of any depth to be matched. 
  
   Example Grammar:
   
		A ::= B C
		B ::= E F
		
   Original Stub Match corresponds to grammar productions (i.e., derivation length 1):
   
		match stub:   	A ::= B C
		
	Enhanced:
	
		match stub:		A => E F C
		
		
*)


(* ==================================================================================== *)
signature PRETTYPRINT_ENGINE_SIG =
sig
    val prettyprint: TextIO.outstream * CONCRETE_REPRESENTATION.ITREE -> unit
	val prettyprintString: CONCRETE_REPRESENTATION.ITREE -> string
end;
(* ==================================================================================== *)

(* ------------------------------------------------------------------------------------ *)
functor PRETTYPRINT_ENGINE_FN(
								structure UserStyles :
								sig
									type PP = PRETTYPRINT_DATATYPES.PP
									val format_list : (string * (string -> PP list)) list
								end
							) : PRETTYPRINT_ENGINE_SIG =
(* ------------------------------------------------------------------------------------ *)
struct

open CONCRETE_REPRESENTATION;
open PRETTYPRINT_DATATYPES;

val SEP       = " ";

datatype MATCH_TYPE = DEEP_MATCH | SHALLOW_MATCH

(* ------------------------------------------------------------------------------------ *)
fun skipBlanks( #" " :: xs ) = skipBlanks xs
  | skipBlanks xs            = xs;
  
(* ------------------------------------------------------------------------------------ *)  
(* precondition: leading blanks have been skipped *)
(* remark: the blank after the symbol is thrown away *)
fun getNextSymbol (#" "::xs)  = ("", xs) 
  | getNextSymbol ( [] )      = ("", [])
  | getNextSymbol (x::xs)     =
		let
			val (symbol_tail,rest) = getNextSymbol(xs)
		in
			( (Char.toString x) ^ symbol_tail, rest )
		end
		
(* ------------------------------------------------------------------------------------ *)		
fun getSymbols( [] ) = []
  | getSymbols( sym_list as x::xs ) = 
		let
			val (symbol,rest) = getNextSymbol(skipBlanks sym_list)
		in
			symbol::(getSymbols rest)
		end
						
(* ------------------------------------------------------------------------------------ *)		
fun makeChildrenStubs ( symbol :: nil )  = [ itree(inode(symbol,CONCRETE_REPRESENTATION.default_info),[]) ]
  | makeChildrenStubs ( symbol :: rest ) = itree(inode(symbol,CONCRETE_REPRESENTATION.default_info),[]) :: makeChildrenStubs(rest)
  | makeChildrenStubs ( [] )             = [ itree(inode("", CONCRETE_REPRESENTATION.default_info), []) ]		
  
(* ------------------------------------------------------------------------------------ *)  
fun makeTreeStub( lhs :: "::=" :: rhs ) =
	let
		val children = makeChildrenStubs rhs
	in
		(
			itree(inode(lhs, CONCRETE_REPRESENTATION.default_info), children)
			,
			SHALLOW_MATCH
		)
	end
  | makeTreeStub( lhs :: "=>*" :: rhs ) =
	let
		val children = makeChildrenStubs rhs
	in
		(
			itree(inode(lhs,CONCRETE_REPRESENTATION.default_info), children)
			,
			DEEP_MATCH
		)
	end	
  | makeTreeStub _ = raise General.Fail("Error: In prettyprint_engine.makeTreeStub.\n")
		
(* ------------------------------------------------------------------------------------ *)		
fun convert( (format_str, format_fun) ) =
	let
		val symbol_list               = getSymbols( explode format_str )
		val (tree_stub, match_type)   = makeTreeStub( symbol_list )
	in
		(tree_stub, match_type, format_fun)
	end
	
(* ------------------------------------------------------------------------------------ *)		
(* ------------------------------------------------------------------------------------ *)	
(*                             Begin Enhanced Matching                                  *)
(* ------------------------------------------------------------------------------------ *)	
(* ------------------------------------------------------------------------------------ *)	
(*
	Given: A derivation of the form:
	
		A =>* T1 T2 T3
		
	If deepMatch succeeds, it returns a tuple of the form: 
   
				(flag, t_list) 
				
    where t_list is a list of concrete trees [t1, t2, t3] where
	t1 has T1 as its root symbol, etc.   
   
 *)
 
 (* ------------------------------------------------------------------------------------ *)
datatype MATCH_STATUS = MATCH_SUCCESS of ITREE 
                      | MATCH_FAIL 
					  | EXPANDING of ITREE list;

(* ------------------------------------------------------------------------------------ *)
(* recall that the stub tree has depth 1 *) 
 fun deepMatch( itree(inode(x1,_), []) , t as itree(inode(x2,_), []      )  ) 	    = 
			if x1 = x2 then MATCH_SUCCESS(t)
			           else MATCH_FAIL

   | deepMatch( itree(inode(x1,_), []) , t as itree(inode(x2,_), children)  ) 	    = 
			if x1 = x2 then MATCH_SUCCESS(t) 
					   else EXPANDING(children)		
   | deepMatch( _, itree(imatch_var(symbol_type,symbol_id,_), children)  ) 	= raise General.Fail("Runtime Type Error: In prettyprint_engine.deepMatch: imatch(" ^ symbol_type ^ "," ^ symbol_id ^ ")\n") 
   | deepMatch _                                                            = raise General.Fail("Error: In prettyprint_engine.deepMatch\n")

(* ------------------------------------------------------------------------------------ *)	 
fun deepMatchList( x::xs, y::ys ) = 
		(case deepMatch(x,y) of
			  MATCH_SUCCESS(t) 		=> 	let
											val (flag, t_list) = deepMatchList( xs, ys )
										in
											(flag, y :: t_list )
										end
			| MATCH_FAIL 			=> (false, [])
			| EXPANDING( t_list ) 	=> deepMatchList( x :: xs, t_list @ ys )
		)	
  | deepMatchList( []   , []    ) = (true , [])
  | deepMatchList _               = (false, [])

 	
(* ------------------------------------------------------------------------------------ *)	
fun deepMatchStub( itree(inode(x1,_), [])           , t2 as itree(inode(x2,_) , children)  ) 	                = (x1 = x2, [t2])
  (* non-empty childrenStubs can only exist for initial stub tree *)
  | deepMatchStub( itree(inode(x1,_), childrenStubs),       itree(inode(x2,_) , children)  ) 	                = if (x1 = x2) then deepMatchList(childrenStubs, children) else (false, [])
  
  | deepMatchStub( itree(inode(x1,_), childrenStubs), itree(imatch_var(symbol_type,symbol_id,_), children)  ) 	= raise General.Fail("Runtime Type Error: In prettyprint_engine.deepMatchStub: imatch(" ^ symbol_type ^ "," ^ symbol_id ^ ")\n") 
  | deepMatchStub _                                                                                             = raise General.Fail("Error: In prettyprint_engine.deepMatchStub\n")

  
(* ------------------------------------------------------------------------------------ *)	  
(* ------------------------------------------------------------------------------------ *)	
(* recall that the stub tree has depth 1 *) 
fun shallowMatch( itree(inode(x1,_), []) , t as itree(inode(x2,_), children)  )   = 
			if x1 = x2 then MATCH_SUCCESS(t)
			           else MATCH_FAIL 
  | shallowMatch( _ , itree(imatch_var(symbol_type,symbol_id,_), children) )      = raise General.Fail("Error: In prettyprint_engine.shallowMatch. imatch found in concrete tree.\n")			   				   
  | shallowMatch _                                                                = raise General.Fail("Error: In prettyprint_engine.shallowMatch.\n")			   

(* ------------------------------------------------------------------------------------ *)	
fun shallowMatchStubList( x::xs, y::ys ) = 
		(case shallowMatch(x,y) of
			  MATCH_SUCCESS(t)	=> 	let
										val (flag, t_list) = shallowMatchStubList(xs,ys)
								    in
										(flag, y :: t_list)
									end
			| MATCH_FAIL		=> (false, [])
			| _                 => raise General.Fail("Error: In prettyprint_engine.shallowMatchStubList.\n")
		)	
  | shallowMatchStubList( []   , []    ) = (true,  [] ) 
  | shallowMatchStubList _               = (false, [] )
	
(* ------------------------------------------------------------------------------------ *)	
fun shallowMatchStub( itree(inode(x1,_), [])           , t2 as itree(inode(x2,_)                        , children)  ) 	= (x1 = x2, [t2])
(* non-empty childrenStubs can only exist for initial stub tree *)
  | shallowMatchStub( itree(inode(x1,_), childrenStubs),       itree(inode(x2,_)                        , children)  ) 	=  if (x1 = x2) then shallowMatchStubList( childrenStubs, children ) else (false, [])

  | shallowMatchStub( itree(inode(x1,_), childrenStubs),       itree(imatch_var(symbol_type,symbol_id,_), children)  ) 	= raise General.Fail("Runtime Type Error: In prettyprint_engine.shallowMatchStub: imatch(" ^ symbol_type ^ "," ^ symbol_id ^ ")\n") 
  | shallowMatchStub _                                                                                                  = raise General.Fail("Error: In prettyprint_engine.shallowMatchStub\n")
					
(* ------------------------------------------------------------------------------------ *)	
fun matchStub( DEEP_MATCH, 		t1, t2 )  = deepMatchStub(t1, t2)
  | matchStub( SHALLOW_MATCH,	t1, t2 )  = shallowMatchStub(t1, t2);
  
  
(* ------------------------------------------------------------------------------------ *)	  
(* ------------------------------------------------------------------------------------ *)
(*                             End Enhanced Matching                                    *)	
(* ------------------------------------------------------------------------------------ *)	
(* ------------------------------------------------------------------------------------ *)	

  
(* ------------------------------------------------------------------------------------ *)
fun getChildren( itree(inode(_), children) ) = children
  | getChildren _                            = raise General.Fail("Error: In prettyprint_engine.getChildren\n")
 
(* ------------------------------------------------------------------------------------ *) 
fun defaultPPtoIPP (LM , atree1 :: atree2 :: rest ) = i_process(atree1, LM)::i_insert(SEP)::defaultPPtoIPP(LM,atree2::rest)
  | defaultPPtoIPP (LM , atree::[]                ) = i_process(atree, LM)::[]
  | defaultPPtoIPP _                                = raise General.Fail("Error: In prettyprint_engine.defaultPPtoIPP\n")

(* ------------------------------------------------------------------------------------ *)  
fun convertPPtoIPP( pp_list, tree_list) =
	let
		fun getNth(1, atree::rest) = atree
		  | getNth(n, atree::rest) = getNth(n-1, rest)
		  | getNth _               = raise General.Fail("Error: In prettyprint_engine.getNth. Process counter exceeds subtrees.\n")
		  
		fun aux( insert(str)           ::rest ) = i_insert(str)                        :: aux(rest)
	      | aux( processTerm(term,str) ::rest ) = i_process(term,str)                  :: aux(rest)        
	      | aux( process(pos,str)      ::rest ) = i_process(getNth(pos,tree_list),str) :: aux(rest)
		  | aux( thunk(some_fun)       ::rest ) = i_thunk(some_fun)                    :: aux(rest)
		  | aux( thunkStr(some_fun)    ::rest ) = i_thunkStr(some_fun)                 :: aux(rest)
          
		  | aux( Nothing               ::rest ) = aux(rest)          
		  | aux( []                           ) = []
	in
		aux pp_list
	end
			
(* ------------------------------------------------------------------------------------ *)		
fun prettyprint(output_file, atree) = 
	let
		val internal_format_list = map convert (UserStyles.format_list)
		val LM = "";
							
		fun auxPP( (format_stub, match_type, format_fun) :: other_formats, task_list as i_process(atree,LM)::rest ) = 
				let
					val (flag, t_list) = matchStub(match_type, format_stub, atree)
				in
					if flag 
					then 	
						let
							val _               = setTreeListRef t_list
							val prefix_tasks 	= convertPPtoIPP( format_fun LM, t_list )
						in
							auxPP( internal_format_list, prefix_tasks @ rest )
						end
						
					else auxPP( other_formats, task_list )
				end
											
		  | auxPP( _ , i_insert( str        )  :: rest ) = ( TextIO.output(output_file, str); auxPP( internal_format_list, rest ) )
		  
		  | auxPP( _ , i_thunkStr( some_fun )  :: rest ) = ( TextIO.output( output_file, some_fun() ); auxPP( internal_format_list, rest ) )
		  
		  | auxPP( _ , i_thunk( some_fun    )  :: rest ) = ( some_fun(); auxPP( internal_format_list, rest ) )
									
		  | auxPP( [], i_process(itree(inode(x,_),[]),_)::rest ) = ( if x <> "" then TextIO.output(output_file, x) else ();  auxPP(internal_format_list, rest))
		  
		  | auxPP( [], i_process(atree,LM)::rest ) =
				let
					val children = getChildren atree
					val prefix_tasks = defaultPPtoIPP (LM, children)
				in
					auxPP( internal_format_list, prefix_tasks @ rest )
				end
		  | auxPP( _, [] ) = (* epsilon *) ()
		  
	in
		auxPP( internal_format_list, [ i_process (atree, LM) ] ) 
	end;
	
(* ------------------------------------------------------------------------------------ *)		
fun prettyprintString(atree) = 
	let
		val internal_format_list = map convert (UserStyles.format_list)
		val LM = ""
		val retStr = ref ""
							
		fun auxPP( (format_stub, match_type, format_fun) :: other_formats, task_list as i_process(atree,LM)::rest ) = 
				let
					val (flag, t_list) = matchStub(match_type, format_stub, atree)
				in
					if flag 
					then 	
						let
							val _               = setTreeListRef t_list
							val prefix_tasks 	= convertPPtoIPP( format_fun LM, t_list )
						in
							auxPP( internal_format_list, prefix_tasks @ rest )
						end
						
					else auxPP( other_formats, task_list )
				end
											
		  | auxPP( _ , i_insert( str        )  :: rest ) = ( retStr := !retStr ^ str; auxPP( internal_format_list, rest ) )
		  
		  | auxPP( _ , i_thunkStr( some_fun )  :: rest ) = (  retStr := !retStr ^ some_fun(); auxPP( internal_format_list, rest ) )
		  
		  | auxPP( _ , i_thunk( some_fun    )  :: rest ) = ( some_fun(); auxPP( internal_format_list, rest ) )
									
		  | auxPP( [], i_process(itree(inode(x,_),[]),_)::rest ) = ( if x <> "" then  retStr := !retStr ^ x else ();  auxPP(internal_format_list, rest))
		  
		  | auxPP( [], i_process(atree,LM)::rest ) =
				let
					val children = getChildren atree
					val prefix_tasks = defaultPPtoIPP (LM, children)
				in
					auxPP( internal_format_list, prefix_tasks @ rest )
				end
		  | auxPP( _, [] ) = (* epsilon *) ()
		  
	in
		auxPP( internal_format_list, [ i_process (atree, LM) ] );
		!retStr
	end;

end; (* struct *)
(* ==================================================================================== *)