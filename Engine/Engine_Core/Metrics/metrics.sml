

(* ------------------------------------------------------------------------------------------- *)
signature METRICS_SIG =
sig
	val matchCall				: unit -> unit;
	val matchFail				: unit -> unit;

	val resetMatchIntervalClock : unit -> unit
	val startMatchIntervalClock : unit -> unit
	val pauseMatchIntervalClock : unit -> unit
	val matchIntervalClockTotal : unit -> string
	
	val ruleApplicationSuccess	: unit -> bool;
	val ruleApplicationAttempt	: unit -> unit;

	val toFile					: string -> unit;
	val printMetrics			: unit   -> unit;
  	val setStartTime			: unit   -> unit;
	
end;
(* ------------------------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
structure METRICS : METRICS_SIG =
struct

(* ------------------------------------------------------------------------------------------- *)
val match_calls = ref 0;
val match_fails = ref 0;

val rule_application_successes  = ref 0;

val start_time = ref Time.zeroTime;


(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(* modeled as a large number consisting of the concatenation of two ints *)
val rule_application_attemptsLow   = ref 0;
val rule_application_attemptsHi    = ref 0;
val NINE      = 9;
val MAX_LOW   = 999999999;

fun getAttemptsLow() = !rule_application_attemptsLow;
fun getAttemptsHi()  = !rule_application_attemptsHi;
fun attemptsIsBig()  = getAttemptsHi() > 0;

fun incHi() 		 = rule_application_attemptsHi  := !rule_application_attemptsHi + 1;
fun incLow() 		 = rule_application_attemptsLow := !rule_application_attemptsLow + 1;
fun resetLow()		 = rule_application_attemptsLow := 0;
fun resetHi()		 = rule_application_attemptsHi  := 0;
fun resetCounters()  = (resetLow(); resetHi())

fun incRuleApplicationAttempt() = if !rule_application_attemptsLow = MAX_LOW then (resetLow(); incHi()) else incLow();

fun ruleAttemptsToString() =
	let
		fun pad(0) = ""
		  | pad(n) = "0" ^ pad(n-1)
		   
		val hi     = getAttemptsHi()   
		val hi_str = if hi = 0 then "" else Int.toString(hi)
		val low_str = Int.toString(getAttemptsLow())
		val padding = if hi > 0 then pad(NINE - List.length(explode(low_str))) else "" 
	in
		hi_str ^ padding ^ low_str
	end;
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)




(* ------------------------------------------------------------------------------------------- *)


(* ------------------------------------------------------------------------------------------- *)
val matchTimeTotal               = ref Time.zeroTime;
val startMatchIntervalTime       = ref Time.zeroTime;
fun getMatchIntervalTime()       = Time.-(Time.now(),(!startMatchIntervalTime));

fun resetMatchIntervalClock() = matchTimeTotal         := Time.zeroTime;
fun startMatchIntervalClock() = startMatchIntervalTime := Time.now(); 
fun pauseMatchIntervalClock() = matchTimeTotal := Time.+( !matchTimeTotal, getMatchIntervalTime());
fun matchIntervalClockTotal() = IntInf.toString(Time.toSeconds(!matchTimeTotal));
						
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
fun matchCall     () = match_calls := !match_calls + 1;
fun matchFail     () = match_fails := !match_fails + 1;    
fun matchSuccesses() = !match_calls - !match_fails;

(* ------------------------------------------------------------------------------------------- *)
fun ruleApplicationSuccess () = (rule_application_successes  := !rule_application_successes  + 1; true);
fun ruleApplicationAttempt () = incRuleApplicationAttempt(); 

(* ------------------------------------------------------------------------------------------- *)

fun setStartTime() = start_time := Time.now();

fun getTime() = Time.toReal(Time.-(Time.now(),(!start_time)))

(* ------------------------------------------------------------------------------------------- *)
fun toFile(pathname) =
				let
					val out_stream = TextIO.openOut(pathname);
				in
   					print("\n Data being written to: " ^ pathname ^ "\n");


					TextIO.output(out_stream,"\n nodes_visited  = "  ^ Int.toString(0)) ; 
					TextIO.output(out_stream,"\n rule_count     = "  ^ Int.toString(!rule_application_successes)) ; 
					TextIO.output(out_stream,"\n rule_attempts  = "  ^ ruleAttemptsToString()); 
					
		(*
					TextIO.output(out_stream,"\n match_count    = "  ^ Int.toString(matchSuccesses())) ; 
					TextIO.output(out_stream,"\n match_attempts = "  ^ Int.toString(!match_calls)) ; 
					TextIO.output(out_stream,"\n cast_count     = "  ^ Int.toString(0)) ; 
					TextIO.output(out_stream,"\n cast_attempts  = "  ^ Int.toString(0)) ; 
        *)          
						
					TextIO.closeOut(out_stream)
				end;

(* ------------------------------------------------------------------------------------------- *)
val real_format = StringCvt.FIX (SOME 2);

fun strategicPrecision() = 
	let
		val precision_based_on_low = Real.fmt real_format (Real.fromInt(!rule_application_successes) / Real.fromInt(getAttemptsLow()) * 100.0)
		                             ^ "%   (i.e., (rule_application_successes/rule_application_attempts) * 100)"
									 
		val result = if attemptsIsBig() then "data not available due to large rule attempts count" else precision_based_on_low
	in
	    result
	end
(* ------------------------------------------------------------------------------------------- *)
fun printMetrics() =
		let
			val time_taken        = getTime();
			val application_rate  = if time_taken > 0.0 
                                        then Real.fromInt(!rule_application_successes) / time_taken
                                        else 0.0
            
		in
			print("\n ======================================== Metrics ========================================== \n");
            
			print("Rule Execution Time       \t = " ^ Real.fmt real_format (time_taken) ^ " seconds \n");
			print("Rule execution rate       \t = " ^ Real.fmt real_format (application_rate) ^ " per second\n\n");
			
			print("Number of Rules Applied   \t = " ^ Int.toString(!rule_application_successes) ^ "\n");
			print("Number of Rules Attempted \t = " ^ ruleAttemptsToString() ^ "\n" );
			print("Strategic Precision       \t = " ^ strategicPrecision() );
		(*
	                    print("\n Matches                               = "  ^ Int.toString(matchSuccesses()));
	                    print("\n Match Attempts                        = "  ^ Int.toString(!match_calls) );
	                    print("\n Total time spent on matching          = "  ^ matchIntervalClockTotal() );
		*)
			print("\n ======================================================================================== \n")
		end
								
(* ------------------------------------------------------------------------------------------- *)
end;  (* struct *)
(* ------------------------------------------------------------------------------------------- *)