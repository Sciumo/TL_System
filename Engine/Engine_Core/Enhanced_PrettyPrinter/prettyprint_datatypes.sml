(* -------------------------------------------------------------------------------------------------- *)
structure PRETTYPRINT_DATATYPES =
struct
	datatype PP  = process 		of int * string
                 | processTerm  of CONCRETE_REPRESENTATION.ITREE * string
				 | insert 		of string 
				 | thunk 		of unit -> unit 
				 | thunkStr 	of unit -> string 
                 | Nothing;     

	datatype IPP = i_process 	of CONCRETE_REPRESENTATION.ITREE * string 
	             | i_insert 	of string
				 | i_thunk 		of unit -> unit
				 | i_thunkStr 	of unit -> string ;

				 
(* ------------------------------------------------------------------------------------ *)		
	val globalTreeList_ref = ref ([]:CONCRETE_REPRESENTATION.ITREE list)

	fun setTreeListRef(xs) = globalTreeList_ref := xs
	
	fun getSubTree(n) = 
		let
			fun aux(1, x::xs) 	= x
			| aux(n, x::xs) 	= if n > 1 then aux(n-1,xs) 
								  else raise General.Fail("Error in prettyprint.getSubTree.aux: getSubTree called with inappropriate tree index\n")
			| aux	_         	=  raise General.Fail("Error in prettyprint.getSubTree.aux: getSubTree called with inappropriate tree index\n")  
	 in
		aux(n, !globalTreeList_ref)
	end

    fun getSubTreeCount () =
        List.length (!globalTreeList_ref)
    
end; (* struct *)
(* -------------------------------------------------------------------------------------------------- *)
