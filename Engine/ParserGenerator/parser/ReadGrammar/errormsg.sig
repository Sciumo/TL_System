(* ReadGrammar/errormsg.sig *)

signature ERRORMSG =
 sig
    type body
    datatype severity = WARNING | ERROR
    type complainer = severity -> string -> body -> unit
    val nullErrorBody : body
 end
