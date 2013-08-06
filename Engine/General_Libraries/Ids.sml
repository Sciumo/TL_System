
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*                                      Generate New Ids                                       *)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------------------------- *)
structure Ids = struct
open ABSTRACT_REPRESENTATION;

val substring_01 = ref "$";
val counter_01   = ref 1;

val internal_id_01 = ref (itree( inode( "", CONCRETE_REPRESENTATION.default_info ), [] ));

(* ------------------------------------------------------------------------------------------- *)
fun isVariable [ id ] = 
	let
		fun isDollar ( #"$" ) = true
		  | isDollar _        = false

		val id_list   = String.explode( CONCRETE.getLeaf (Strategic_Values.getTerm id) ) 
	in
		if List.exists isDollar id_list then TRUE else FALSE	
	end

  | isVariable _ = raise General.Fail("Error in General_Libraries.Ids.isVariable: inappropriate arguments to function.\n")

  
(* ------------------------------------------------------------------------------------------- *)
val setNew_01 = fn [ expr1, expr2, expr3, expr4 ] => 
				let
				    fun aux( a_tree, node, separator, repeater ) = 
                                              substring_01 := GENERATE.uniqueSubstring( a_tree, node, separator, repeater );

				    val a_tree    = Strategic_Values.getTerm   expr1
				    val node      = Strategic_Values.getString expr2
				    val separator = Strategic_Values.getString expr3
					val repeater  = Strategic_Values.getString expr4
				in
		                  aux(a_tree,node,separator,repeater);
		                  print("\nIn setNew_01, unique substring = " ^ (!substring_01) ^ " current counter = " ^ Int.toString(!counter_01) ^"\n\n");
		                  TRUE
				end

		          | _ => raise General.Fail("Error in General_Libraries.Ids.setNew_01: inappropriate arguments to function.\n")

  
  
(* ------------------------------------------------------------------------------------------- *)
fun new_01 [ expr ] = 
	let
		fun getNew_01(leaf_str) = 	let
										val counter = !counter_01
										val suffix  = !substring_01 ^ Int.toString(counter)
									in
										counter_01 := counter + 1;
										leaf_str ^ suffix
									end;

		val x_info       = Strategic_Values.getTermInfo expr
		val x_term       = Strategic_Values.getTerm expr
		val new_id_str   = getNew_01(CONCRETE.getLeaf x_term)

	in
		ABSTRACT.makeTerm( 	CONCRETE.replaceLeaf (x_term, new_id_str), 
							x_info
						 )
	end

  | new_01 _ = raise General.Fail("Error in General_Libraries.Ids.new_01: inappropriate arguments to function.\n")

(* ------------------------------------------------------------------------------------------- *)
fun reset_01 [internal_id_tree] = 
	let
		val the_tree = Strategic_Values.getTerm internal_id_tree
	in
		counter_01  := 1; 
		internal_id_01 := the_tree;
		TRUE
	end
  | reset_01 _  = raise General.Fail("Error in General_Libraries.Ids.reset_01: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)
fun reset_01_counter [] = 
    (
		counter_01  := 1; 
		TRUE
	)
  | reset_01_counter _  = raise General.Fail("Error in General_Libraries.Ids.reset_01_counter: inappropriate arguments to function.\n");


(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)


val substring_02 = ref "$";
val counter_02   = ref 1;

val internal_id_02 = ref (itree( inode( "", CONCRETE_REPRESENTATION.default_info ), [] ));

  
(* ------------------------------------------------------------------------------------------- *)
val setNew_02 = fn [ expr1, expr2, expr3, expr4 ] => 
				let
				    fun aux( a_tree, node, separator, repeater ) = 
                                              substring_02 := GENERATE.uniqueSubstring( a_tree, node, separator, repeater );

				    val a_tree    = Strategic_Values.getTerm   expr1
				    val node      = Strategic_Values.getString expr2
				    val separator = Strategic_Values.getString expr3
					val repeater  = Strategic_Values.getString expr4
				in
		                  aux(a_tree,node,separator,repeater);
		                  print("\nIn setNew_01, unique substring = " ^ (!substring_02) ^ " current counter = " ^ Int.toString(!counter_02) ^"\n\n");
		                  TRUE
				end

		          | _ => raise General.Fail("Error in General_Libraries.Ids.setNew_01: inappropriate arguments to function.\n")

  
  
(* ------------------------------------------------------------------------------------------- *)
fun new_02 [ expr ] = 
	let
		fun getNew_02(leaf_str) = 	let
										val counter = !counter_02
										val suffix  = !substring_02 ^ Int.toString(counter)
									in
										counter_02 := counter + 1;
										leaf_str ^ suffix
									end;

		val x_info       = Strategic_Values.getTermInfo expr
		val x_term       = Strategic_Values.getTerm expr
		val new_id_str   = getNew_02(CONCRETE.getLeaf x_term)

	in
		ABSTRACT.makeTerm( 	CONCRETE.replaceLeaf (x_term, new_id_str), 
							x_info
						 )
	end

  | new_02 _ = raise General.Fail("Error in General_Libraries.Ids.new_02: inappropriate arguments to function.\n")

(* ------------------------------------------------------------------------------------------- *)
fun reset_02 [internal_id_tree] = 
	let
		val the_tree = Strategic_Values.getTerm internal_id_tree
	in
		counter_02  := 1; 
		internal_id_02 := the_tree;
		TRUE
	end
  | reset_02 _  = raise General.Fail("Error in General_Libraries.Ids.reset_02: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)
fun reset_02_counter [] = 
    (
		counter_02  := 1; 
		TRUE
	)
  | reset_02_counter _  = raise General.Fail("Error in General_Libraries.Ids.reset_02_counter: inappropriate arguments to function.\n");

  
  
  
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)


    val functions = 
		[
			("setNew_01"   	    , setNew_01 	    ),		
			("new_01"   	    , new_01   		    ),
			("reset_01" 	    , reset_01 		    ), 
            ("reset_01_counter" , reset_01_counter  ), 
            
			("setNew_02"   	    , setNew_02 	    ),		
			("new_02"   	    , new_02   		    ),
			("reset_02" 	    , reset_02 		    ), 
            ("reset_02_counter" , reset_02_counter  ), 
            
			("isVariable"	    , isVariable	    )
		];


  
  
(* ------------------------------------------------------------------------------------------- *)
end; (* struct *)
(* ------------------------------------------------------------------------------------------- *)

