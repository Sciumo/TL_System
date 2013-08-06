
(* ------------------------------------------------------------------------------------------- *)
signature GENERATE_SIG =
sig
     val uniqueSubstring 	: CONCRETE_REPRESENTATION.ITREE * string * string * string -> string

 (*    val new 		 		: CONCRETE_REPRESENTATION.ITREE * string -> CONCRETE_REPRESENTATION.ITREE *)
end;
(* ------------------------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------------------------- *)
structure GENERATE : GENERATE_SIG =
struct
open CONCRETE_REPRESENTATION;

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------------------------- *)
fun uniqueSubstring( target_program, node_id, separator_symbol, repeater_symbol) =
	let
	    val unique_substring = ref "";

            (* ------------------------------------------------------------------------------- *)
            fun checkAndChange( id ) = if String.isPrefix (!unique_substring) id then (
                                                                                         unique_substring := !unique_substring ^ repeater_symbol;
                                                                                         checkAndChange id
                                                                                      )
                                       else ();

            (* ------------------------------------------------------------------------------- *)
            fun scan( id, current_pos, stop_pos ) = case stop_pos > current_pos of 
                                                       true  => (
                                                                  checkAndChange( id );
                                                                  scan(id, current_pos + 1, stop_pos)
                                                                ) 
                                                     | false => ();
                                                                         


            (* ------------------------------------------------------------------------------- *)
	    fun traverse( itree(inode(symbol, x_info) , [child] ) ) = 	if symbol = node_id 
																	then
																		let
																			val leaf      = CONCRETE.getLeaf child
																			val leaf_len  = size leaf
																			val sub_len   = size (!unique_substring)
																		in
																			(* scan all possible postions to see if unique_substring is a substring of leaf *)
																			scan( leaf, 1, leaf_len - sub_len + 1 )
																		end
																					
																	else traverse child 
																				
              | traverse( itree( any            , subtrees) ) = (
                                                                  map traverse subtrees;
                                                                  ()
                                                               )
            (* ------------------------------------------------------------------------------- *)
	in
           unique_substring := separator_symbol;
           traverse target_program;
           !unique_substring
	end
(*
(* ------------------------------------------------------------------------------------------- *)
fun new( a_tree, suffix_str ) = 
				let
				    val leaf = CONCRETE.getLeaf a_tree
				in
                    CONCRETE.replaceLeaf(a_tree,suffix_str)
				end

*)				
(* ------------------------------------------------------------------------------------------- *)
end;  (* struct *)
(* ------------------------------------------------------------------------------------------- *)