(* ------------------------------------------------------------------------------------------- *)
structure STACK =
struct

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(* Note that false values are never pushed on the application stack or the reduction 
   stack. What this implies is that these "stacks" can be implemented as simple counters
   over the domain of non-negative integers!
*)

val TRUE_STACK  = 1;   (* stack value *)
val FALSE_STACK = 0;   (* stack value *)

fun applicationObserved( state ) = STATE_MODEL.getApplicationStack(state) > 0
fun reductionObserved  ( state ) = STATE_MODEL.getReductionStack(state)   > 0

fun orStack ( stack1, stack2)    = Int.max( stack1, stack2 ); 
fun andStack( stack1, stack2)    = Int.min( stack1, stack2 );

fun popStack( 0 )    = 0
  | popStack( n )    = n - 1;

fun dupStackTop( 0 ) = 0
  | dupStackTop( n ) = n + 1;

(* ------------------------------------------------------------------------------------------- *)
end;  (* struct *)
(* ------------------------------------------------------------------------------------------- *)