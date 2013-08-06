
structure Basic_Support =
struct

	(* --------------------------------------------------------------------------------------------- *)																								 
	fun splitExtension str =
		let
			fun aux( #"." :: pre_dot, post_dot ) = ( implode(List.rev pre_dot), implode(post_dot) ) 
			  | aux( x :: xs   , post_dot ) = aux(xs, x :: post_dot)
			  | aux ([], _)                = raise General.Fail("Error in StandAlone.splitExtension.\n")
		in
			(* we want to split on the rightmost dot *)
			aux(List.rev (explode str),[])
		end
																									 

end; (* struct *)
(* --------------------------------------------------------------------------------------------- *)

		
	

