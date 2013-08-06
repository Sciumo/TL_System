(* =========================================================================================== *)
(* ------------------------------------------------------------------------------------------- *)
(*                                 Strategic Views                                             *)
(* ------------------------------------------------------------------------------------------- *)
(* =========================================================================================== *)

structure Strategic_Views = struct
open ABSTRACT_REPRESENTATION;

(* ------------------------------------------------------------------------------------------- *)
fun output [expr] = 
	let
	   val s = Strategic_Values.getString expr
	in
	   print(s); 
	   TRUE
	end
  | output _ = raise General.Fail("Error in Strategic_Views.output: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)
fun nl [] = ( print("\n"); TRUE )
  | nl _  = raise General.Fail("Error in Strategic_Views.nl: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)
fun viewTermStructure [ term ] =  

			let
			    val t = Strategic_Values.getFirstOrder term
			in
                            ABSTRACT.printTree t;  
                            TRUE
			end

  | viewTermStructure _ = raise General.Fail("Error in Strategic_Views.viewTermStructure: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)
fun viewTerm [term] =  
		let
		   val t   = Strategic_Values.getFirstOrder term
                   val str = ABSTRACT.leavesToString t false
		in
		   print(str);
                   TRUE
                end
  | viewTerm _ = raise General.Fail("Error in Strategic_Views.viewTerm: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)
fun viewStrategyStructure [term] =  
			let
			    val s_list = Strategic_Values.getHigherOrder term
			in
                            map ABSTRACT.printTree s_list;  
                            TRUE
			end

  | viewStrategyStructure _ = raise General.Fail("Error in Strategic_Views.viewStrategyStructure: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)
fun viewStrategy [expr] =  
		let
		   val s   = Strategic_Values.getStrategy expr
                   val str = ABSTRACT.leavesToString s false
		in
		   print(str);
                   TRUE
                end

  | viewStrategy _ = raise General.Fail("Error in Strategic_Views.viewStrategy: inappropriate arguments to function.\n");



(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*                                 Exported Function List                                      *)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)

    val functions = 
			[
				("output"					, output				),
				("nl"						, nl					),
																		
				("viewTerm"					, viewTerm				),
				("viewTermStructure"		, viewTermStructure		),
																			
				("viewStrategy"				, viewStrategy			),
				("viewStrategyStructure"	, viewStrategyStructure	)
			]

  
(* ------------------------------------------------------------------------------------------- *)
end; (* struct *)
(* ------------------------------------------------------------------------------------------- *)

