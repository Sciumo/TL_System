(* =========================================================================================== *)
(* ------------------------------------------------------------------------------------------- *)
(*                       Functions for Inspecting Strategic Values                             *)
(* ------------------------------------------------------------------------------------------- *)
(* =========================================================================================== *)

structure Strategic_Values = struct
open ABSTRACT_REPRESENTATION;

(* ------------------------------------------------------------------------------------------- *)

fun getFirstOrder( [first_order], _ ) 		= first_order
  | getFirstOrder _                   		= raise General.Fail("Error in Strategic_Values.getFirstOrder\n");

fun getHigherOrder( _ , higher_order_list )	= higher_order_list

fun getNumInfo( INT (_ , x_info) ) 	= x_info
  | getNumInfo( REAL(_ , x_info) ) 	= x_info
  | getNumInfo( TERM(_ , x_info) ) 	= x_info 
  | getNumInfo( expr             )  = raise RUNTIME.error([expr], General.Fail("Error in Strategic_Values.getNumInfo\n"),
                                                              ABSTRACT.printTree, ABSTRACT.getExprInfo, CONCRETE_REPRESENTATION.printNodeInfo);

fun getInt( [INT (v, _)], _ ) 			= v
  | getInt _             			= raise General.Fail("Error in Strategic_Values.getInt\n");

fun getString( [STRING (v, _)], _ ) 		= v
  | getString _                			= raise General.Fail("Error in Strategic_Values.getString\n");

fun getStringInfo( [STRING (_, x_info)], _ )	= x_info
  | getStringInfo _                				= raise General.Fail("Error in Strategic_Values.getStringInfo\n");

fun getTerm( [TERM (v,_)], _ ) 				= v
  | getTerm _              					= raise General.Fail("Error in Strategic_Values.getTerm\n");

fun getSubTermList( [TERM ( 
							itree(_,v_list),
							_
						  )
					], 
					_ 
				 ) 							= v_list
  | getSubTermList _              			= raise General.Fail("Error in Strategic_Values.getSubTermList\n");
   
fun getSubTerm( [TERM ( 
						itree(_,[v]),
						_
					  )
				], 
				_ 
			  ) 							= v
  | getSubTerm _              				= raise General.Fail("Error in Strategic_Values.getSubTerm\n");
  
fun getTermInfo( [TERM (_,x_info)], _ )		= x_info
  | getTermInfo _              				= raise General.Fail("Error in Strategic_Values.getTermInfo\n");

fun getStrategy( _ , [s] )					= s
  | getStrategy( _ , []  ) 					= SKIP (CONCRETE_REPRESENTATION.dummy_node_info)
  | getStrategy _             				= raise General.Fail("Error in Strategic_Values.getStrategy\n");

  
(* ------------------------------------------------------------------------------------------- *)  
fun getITREE_info( itree(inode(v,x_info),_) ) = x_info
  | getITREE_info _              			  = raise General.Fail("Error in Strategic_Values.getITREE_info\n");
  
(* ------------------------------------------------------------------------------------------- *)    
fun getNthSubTerm expr n = 
	let
		val v_list = getSubTermList expr
	in
		if List.length v_list >= n-1 then List.nth(v_list, n-1)
		else raise General.Fail("Error in Strategic_Values.getNthSubterm\n")
	end

fun getUniqueIdFromInfo( info( data ) ) = #id( data )
fun getLineFromInfo    ( info( data ) ) = #line( data )
fun getColumnFromInfo  ( info( data ) ) = #column( data )
fun getLabelFromInfo   ( info( data ) ) = #label( data )

fun getNodeInfo( [TERM(
                          itree(inode(_,inode_info), children), 
						  term_info
					   )
				  ], _ ) = inode_info 
				  
  | getNodeInfo _  = raise General.Fail("Error in Strategic_Values.getNodeInfo\n");  
  

fun showNodeInfo( someTerm ) =
    let
        val inode_info = getNodeInfo someTerm
    in
        print("\n\n==================================================================\n");
        print("Node Info: uniqueId = " ^ makeUniqueIdAttribute inode_info ^ "\n");
        print("           line     = " ^ makeLineAttribute inode_info ^ "\n");
        print("           column   = " ^ makeColumnAttribute inode_info ^ "\n");
        print("           label    = " ^ makeLabelAttribute inode_info ^ "\n");
        print("==================================================================\n\n")
    end
  
fun getLine  ( x_node ) = getLineFromInfo  ( getNodeInfo x_node ) 
fun getColumn( x_node ) = getColumnFromInfo( getNodeInfo x_node )
fun getLabel ( x_node ) = getLabelFromInfo ( getNodeInfo x_node )

(* ------------------------------------------------------------------------------------------- *)  
 fun termToString term	= CONCRETE.leavesToStringRaw(getTerm term) 


 
(* ------------------------------------------------------------------------------------------- *)
end; (* struct *)
(* ------------------------------------------------------------------------------------------- *)

