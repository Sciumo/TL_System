
(* ------------------------------------------------------------------------------------------- *)
structure ABSTRACT_REPRESENTATION =
struct

open CONCRETE_REPRESENTATION;


type INFO = { CONTEXT : string, INDEX : int option } 	(* CONTEXT is the name (e.g., label) of the strategy in which the ref occurs 	  *)
							(* The absolute address in the (global) store where the strategic value is stored *)

datatype EXPR =

     PROG 			of EXPR list * NODE_INFO

	| SIGNATURE		of EXPR * NODE_INFO
    | LIST 			of EXPR list * NODE_INFO

	| RECURSIVE     of  EXPR * EXPR list * EXPR * NODE_INFO
	| NON_RECURSIVE of  EXPR * EXPR * NODE_INFO

	| ANDALSO 		of EXPR * EXPR * NODE_INFO
	| ORELSE 		of EXPR * EXPR * NODE_INFO

	| MATCH  		of EXPR * EXPR * NODE_INFO
	| BIND   		of EXPR * EXPR * NODE_INFO   (* (lvalue,strategic expression). E.g., s := r1 <+ r2  *)

	| CHOICE  		of EXPR * EXPR * NODE_INFO
	| LCHOICE 		of EXPR * EXPR * NODE_INFO
	| RCHOICE 		of EXPR * EXPR * NODE_INFO
	| LSEQ    		of EXPR * EXPR * NODE_INFO
	| RSEQ    		of EXPR * EXPR * NODE_INFO
	| LSTAR   		of EXPR * EXPR * NODE_INFO
	| RSTAR   		of EXPR * EXPR * NODE_INFO

	| RULE         	of EXPR * EXPR * NODE_INFO
	| COND_RULE  	of EXPR * EXPR * EXPR * NODE_INFO

	| B_OR   		of EXPR * EXPR * NODE_INFO
	| B_AND  		of EXPR * EXPR * NODE_INFO

	| EQ      		of EXPR * EXPR * NODE_INFO
	| NEQ     		of EXPR * EXPR * NODE_INFO
	| LEQ     		of EXPR * EXPR * NODE_INFO
	| LT      		of EXPR * EXPR * NODE_INFO
	| GEQ     		of EXPR * EXPR * NODE_INFO
	| GT      		of EXPR * EXPR * NODE_INFO

	| CONCAT  		of EXPR * EXPR * NODE_INFO
	| PLUS    		of EXPR * EXPR * NODE_INFO
	| MINUS   		of EXPR * EXPR * NODE_INFO
	| TIMES   		of EXPR * EXPR * NODE_INFO
	| DIVIDE  		of EXPR * EXPR * NODE_INFO
	| DIV     		of EXPR * EXPR * NODE_INFO
	| MOD     		of EXPR * EXPR * NODE_INFO

	| APP      		of EXPR * EXPR * NODE_INFO
	| ITERATOR 		of EXPR * EXPR list  * NODE_INFO   	(* iterator name followed by 0 or more arguments. E.g., ITERATOR( TDL,[s] ), ITERATOR(FIX, [s])      *)
														(* IMPORTANT: the ITERATOR term structure gets created during the optimization phase after inlining  *)

	| BOOL         	of bool   * NODE_INFO
	| INT          	of int    * NODE_INFO
	| REAL         	of string * NODE_INFO  (* otherwise the result is not an equality type *)
	| STRING       	of string * NODE_INFO
	| IDENTIFIER   	of string * NODE_INFO
	| REF          	of string * INFO * NODE_INFO
	| TERM         	of ITREE  * NODE_INFO

	| LIBRARY_CALL_0 of EXPR * NODE_INFO              (* empty arg list     *)
	| LIBRARY_CALL   of EXPR * EXPR list  * NODE_INFO (* non-empty arg list *)

	| ID  			of NODE_INFO
	| SKIP 			of NODE_INFO
        | FAIL                       of NODE_INFO

	| NOT          	of EXPR  * NODE_INFO
	| BANG         	of EXPR  * NODE_INFO
	| TILDE        	of EXPR  * NODE_INFO

	| TRANSIENT    	of EXPR  * NODE_INFO
	| OPAQUE       	of EXPR  * NODE_INFO
	| RAISE        	of EXPR  * NODE_INFO
	| HIDE         	of EXPR  * NODE_INFO
	| LIFT         	of EXPR  * NODE_INFO

	| MAPL         	of EXPR  * NODE_INFO
	| MAPR         	of EXPR  * NODE_INFO
	| MAPB         	of EXPR  * NODE_INFO

	| FOLD_CHOICE  	of EXPR  * NODE_INFO  (* homogeneous strategy composition *)
	| FOLD_LCHOICE 	of EXPR  * NODE_INFO
	| FOLD_RCHOICE 	of EXPR  * NODE_INFO
	| FOLD_LSEQ    	of EXPR  * NODE_INFO
	| FOLD_RSEQ    	of EXPR  * NODE_INFO
	| FOLD_LSTAR   	of EXPR  * NODE_INFO
	| FOLD_RSTAR   	of EXPR  * NODE_INFO

	| FOLDS_CHOICE  	of EXPR * NODE_INFO   (* heterogeneous strategy composition *)
	| FOLDS_LCHOICE 	of EXPR * NODE_INFO
	| FOLDS_RCHOICE 	of EXPR * NODE_INFO
	| FOLDS_LSEQ    	of EXPR * NODE_INFO
	| FOLDS_RSEQ    	of EXPR * NODE_INFO
	| FOLDS_LSTAR   	of EXPR * NODE_INFO
	| FOLDS_RSTAR   	of EXPR * NODE_INFO

   (* UNIT is a special value that is used exclusively as a possible return value for an SML function.
      As such, UNIT should not be part of a mapping (E.g., fromConcrete, toFile, fromFile).
   *)

	| TRUE
	| FALSE;

   end; (* structure *)
(* ------------------------------------------------------------------------------------------- *)
