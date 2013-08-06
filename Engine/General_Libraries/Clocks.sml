(* =========================================================================================== *)
(* ------------------------------------------------------------------------------------------- *)
(*                                 Clock Functions                                             *)
(* ------------------------------------------------------------------------------------------- *)
(* =========================================================================================== *)

structure Clocks = struct
open ABSTRACT_REPRESENTATION;

(* ------------------------------------------------------------------------------------------- *)

val startTime      = ref Time.zeroTime;
fun getTime()      = IntInf.toString(Time.toSeconds(Time.-(Time.now(),(!startTime))))

fun startClock([ expr_str ])  = 
	let 
	    val s = Strategic_Values.getString expr_str
	in
	    print(s);
	    startTime := Time.now(); 
	    TRUE
	end
  | startClock _    = raise General.Fail("Error in UserDefined.startClock: inappropriate arguments to function.\n");

fun stopClock([expr_str]) = 
	let
	    val s = Strategic_Values.getString expr_str
	in
	    print(s ^ ":Elapsed Time = " ^ getTime() ^ "\n"); 
	    TRUE
	end

  | stopClock _ = raise General.Fail("Error in UserDefined.stopClock: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)

val startTime2     = ref Time.zeroTime;
fun getTime2()     = IntInf.toString(Time.toSeconds(Time.-(Time.now(),(!startTime2))))

fun startClock2([ expr_str ])  = 
	let 
	    val s = Strategic_Values.getString expr_str
	in
	    print(s);
	    startTime2 := Time.now(); 
	    TRUE
	end
  | startClock2 _    = raise General.Fail("Error in UserDefined.startClock2: inappropriate arguments to function.\n");

fun stopClock2([expr_str]) = 
	let
	    val s = Strategic_Values.getString expr_str
	in
	    print(s ^ ":Elapsed Time = " ^ getTime2() ^ "\n"); 
	    TRUE
	end

  | stopClock2 _ = raise General.Fail("Error in UserDefined.stopClock2: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)

val intervalTimeTotal       = ref Time.zeroTime;
val startIntervalTime       = ref Time.zeroTime;
fun getIntervalTime()       = Time.-(Time.now(),(!startIntervalTime));
fun getIntervalTimeTotal()  = IntInf.toString(Time.toSeconds(!intervalTimeTotal));

fun resetIntervalClock([]) =
	(
	   intervalTimeTotal := Time.zeroTime;
	   TRUE
	)
  | resetIntervalClock _ = raise General.Fail("Error in UserDefined.resetIntervalClock: inappropriate arguments to function.\n");

fun startIntervalClock([])  = 
	(
	    startIntervalTime := Time.now(); 
	    TRUE
	)
  | startIntervalClock _    = raise General.Fail("Error in UserDefined.startIntervalClock: inappropriate arguments to function.\n");

fun pauseIntervalClock([]) = 
	let
	    val delta = getIntervalTime()
	in
	    intervalTimeTotal := Time.+( !intervalTimeTotal, delta);
	    TRUE
	end

  | pauseIntervalClock _ = raise General.Fail("Error in UserDefined.pauseIntervalClock: inappropriate arguments to function.\n");

fun intervalClockTotal([expr_str]) = 
	let
	    val s = Strategic_Values.getString expr_str
	in
	    print(s ^ ":Elapsed Time = " ^ getIntervalTimeTotal() ^ "\n"); 
	    TRUE
	end

  | intervalClockTotal _ = raise General.Fail("Error in UserDefined.intervalClockTotal: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)

val intervalTimeTotal2       = ref Time.zeroTime;
val startIntervalTime2       = ref Time.zeroTime;
fun getIntervalTime2()       = Time.-(Time.now(),(!startIntervalTime2));
fun getIntervalTimeTotal2()  = IntInf.toString(Time.toSeconds(!intervalTimeTotal2));

fun resetIntervalClock2([]) =
	(
	   intervalTimeTotal2 := Time.zeroTime;
	   TRUE
	)
  | resetIntervalClock2 _ = raise General.Fail("Error in UserDefined.resetIntervalClock2: inappropriate arguments to function.\n");

fun startIntervalClock2([])  = 
	(
	    startIntervalTime2 := Time.now(); 
	    TRUE
	)
  | startIntervalClock2 _    = raise General.Fail("Error in UserDefined.startIntervalClock2: inappropriate arguments to function.\n");

fun pauseIntervalClock2([]) = 
	let
	    val delta = getIntervalTime2()
	in
	    intervalTimeTotal2 := Time.+( !intervalTimeTotal2, delta);
	    TRUE
	end

  | pauseIntervalClock2 _ = raise General.Fail("Error in UserDefined.pauseIntervalClock2: inappropriate arguments to function.\n");

fun intervalClockTotal2([expr_str]) = 
	let
	    val s = Strategic_Values.getString expr_str
	in
	    print(s ^ ":Elapsed Time = " ^ getIntervalTimeTotal2() ^ "\n"); 
	    TRUE
	end

  | intervalClockTotal2 _ = raise General.Fail("Error in UserDefined.intervalClockTotal2: inappropriate arguments to function.\n");

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*                                 Exported Function List                                      *)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)

    val functions = 
			[
				("startClock"			, startClock			),
				("stopClock"			, stopClock				),
				("startClock2"			, startClock2			),
				("stopClock2"			, stopClock2			),
																		
				("resetIntervalClock"   , resetIntervalClock	),
																		
				("startIntervalClock"   , startIntervalClock	),
				("pauseIntervalClock"   , pauseIntervalClock	),
				("intervalClockTotal"   , intervalClockTotal	),
																	
				("resetIntervalClock2"  , resetIntervalClock2	),
				("startIntervalClock2"  , startIntervalClock2	),
				("pauseIntervalClock2"  , pauseIntervalClock2	),
				("intervalClockTotal2"  , intervalClockTotal2	)
			]
  
(* ------------------------------------------------------------------------------------------- *)
end; (* struct *)
(* ------------------------------------------------------------------------------------------- *)

