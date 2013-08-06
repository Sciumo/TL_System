(* ------------------------------------------------------------------------------------------- *)
(*                      Begin Comment: Associative Matching                                    *)
(* ------------------------------------------------------------------------------------------- *)
(*

    Associative checking on ids (i.e., tokens) is straightforward because
    we only need to determine if a match is possible - no substitution
    is produced and no alternate solutions are produced.

    Example:

    Let u, v, and w denote arbitrary strings, and let [u] denote
    u in a given context. Under these assumptions an associative
    match looks like:

    *u*v*w*   =    asbd[u]bdrs[v]asdr[w]asdr

    
     So the algorithm simply looks for the first occurrence of
     u, then the first occurrence of v, and finally the first
     occurrence of w. If it succeeds, the match succeeds
     and our substitution list (sigma) remains unchanged.

     The associative match here can be viewed as being between
     to ground terms (since sigma does not change). This perspective
     is advantageous. I believe that the root of trees participating
     in this type of associative match should be explicitly declared
     in HATS to allow the concept to be general. Note that we cannot
     simply interpret strings like a*bc to be an identifier because then
     mathematical expressions like a * bc will need to surround the multiplication
     operator with spaces, otherwise the lexer will tokenize the expression
     as an identifier. It may be possible to encode some intelligence in the
     lexer through labels, but this would need to be looked into further.
     However, a solution that seems almost as good is to declare wildcard ids
     in a production like:

     wild_id ::=  ( [id] [*] )*  . 


     Furthermore, a new matching symbol, ==, should be used when matching trees
     having wildcards. In this matching function, when a tree having
     a wild_id as a root is "matched" with a tree having an "id" as a root,
     the matching function below will be called. Note that in the standard
     matching environment the match between two ids would simply be an equality
     check. 

     IMPORTANT: A restriction in this kind of matching is that both wild_id
     and id must be ground terms -- no schema variables are permitted here.

     The basic idea is to partition a wildcard string as follows:

        * alpha_1 * alpha_2 * ... * alpha_n

        ==>

        [  [alpha_1], [alpha_2], ..., [alpha_n] ]


      Now each list element can be treated as if it is preceeded by
      a star. That is:

        [  [*alpha_1], [*alpha_2], ..., [*alpha_n] ]


      There are two special cases that need to be accounted for:

       1. There is a trailing star.
       2. There is no leading star.
*)
(* ------------------------------------------------------------------------------------------- *)
(*                End Comment: Associative Matching                                            *)
(* ------------------------------------------------------------------------------------------- *)




(* ------------------------------------------------------------------------------------------- *)
signature WILDCARD_SIG =

sig
	val isWild 				: CONCRETE_REPRESENTATION.ITREE * CONCRETE_REPRESENTATION.ITREE -> bool * CONCRETE_REPRESENTATION.ITREE * CONCRETE_REPRESENTATION.ITREE 
	val associativeMatch	: CONCRETE_REPRESENTATION.ITREE * CONCRETE_REPRESENTATION.ITREE -> bool

end;
(* ------------------------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------------------------- *)
structure WILDCARD:WILDCARD_SIG =

struct

open CONCRETE_REPRESENTATION;


(* ------------------------------------------------------------------------------------------- *)
 fun isWild(t1 as itree(inode(x,_), children_x),
            t2 as itree(inode(y,_), children_y) 
           )  =

              if x = "wild_id" andalso y = "id"      then (true, t1, t2) 
         else if x = "id"      andalso y = "wild_id" then (true, t2, t1) 
         else                                             (false, t1, t2)
												
   | isWild(t1,t2) = (false, t1, t2);
																			
(* ------------------------------------------------------------------------------------------- *)
 fun getLeaves(itree(inode(x,_), []))       = x
   | getLeaves(itree(inode(x,_), children)) = foldr (fn (y,ys) => y^ys) "" (map getLeaves children)
   | getLeaves t                            = raise RUNTIME.error([ABSTRACT.makeTerm (t, dummy_node_info)], General.Fail("\n In WILDCARD.get_leaves. Only ground tree structures permitted.\n"),
                                                                 ABSTRACT.printTree, ABSTRACT.getExprInfo, printNodeInfo);
																										
(* ------------------------------------------------------------------------------------------- *)
fun partition(xs, #"*"::ys) =  (xs,ys)
  | partition(xs,  y::ys)   =  partition(xs@[y], ys)
  | partition(xs,  [] )     =  (xs,[])
																					
(* ------------------------------------------------------------------------------------------- *)
fun aux_group [] = []
  | aux_group xs = let
		      val (xs_list,rest) = partition([],xs)
	           in
                      xs_list :: aux_group(rest) 
	           end
																								
(* ------------------------------------------------------------------------------------------- *)
fun star_first( #"*"::xs ) = ([],xs)
  | star_first( xs )       = ([#"-"],xs)
																									
(* ------------------------------------------------------------------------------------------- *)
fun star_last( xs ) = if List.last(xs) = #"*" then ([#"*"], List.take(xs,List.length(xs) - 1))
		                              else ([], xs )
																				
(* ------------------------------------------------------------------------------------------- *)
fun clean( [] :: xs ) = clean(xs)
  | clean( x::xs    ) = x :: clean(xs)
  | clean( [] )       = [];
																		
(* ------------------------------------------------------------------------------------------- *)
fun group( xs ) = let
 		     val (first_element, xs1) = star_first(xs)
		     val (last_element, xs2)  = star_last(xs1)
		     val grouped_xs           = aux_group(xs2)
		     val result               = clean(   (first_element :: grouped_xs) @ [ last_element ]  )
		  in
		     result
		  end
																		
(* ------------------------------------------------------------------------------------------- *)
fun isPrefix( x::xs, y::ys ) = x = y andalso isPrefix(xs,ys)
  | isPrefix( [], _ ) = true
  | isPrefix _        = false
														
(* ------------------------------------------------------------------------------------------- *)
fun isSuffix( xs,ys ) = isPrefix( List.rev(xs), List.rev(ys) )
																			
(* ------------------------------------------------------------------------------------------- *)
fun aux_match( [#"*"]::[], _ )       = true
  | aux_match( [], [] )              = true
  | aux_match( xs, [])               = false
  | aux_match( [], ys)               = false

  | aux_match( [#"-"]::xs::xss, ys ) = isPrefix(xs,ys) andalso aux_match(xss, List.drop(ys,List.length(xs)))

  | aux_match( xs::[], ys ) =  isSuffix(xs,ys)
   
  | aux_match( xs::xss, ys ) = if isPrefix(xs,ys) then aux_match( xss    , List.drop(ys,List.length(xs)))
                                                  else aux_match( xs::xss, tl(ys) )
														
(* ------------------------------------------------------------------------------------------- *)
fun associativeMatch( t1, t2 ) = 
	let
		val xs     = group(explode(getLeaves t1))
	 	val ys     = explode(getLeaves t2)
	in
		aux_match(xs,ys)
	end 
																							
(* ------------------------------------------------------------------------------------------- *)
end (* struct *)
(* ------------------------------------------------------------------------------------------- *)
