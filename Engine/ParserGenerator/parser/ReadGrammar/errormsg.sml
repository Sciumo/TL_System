(* ReadGrammar/errormsg.sml *)

structure ErrorMsg :> ERRORMSG =
  struct
    type body = unit (* was (PrettyPrint.ppstream -> unit) *)
    datatype severity = WARNING | ERROR
    type complainer = severity -> string -> body -> unit
    val nullErrorBody = ()
  end
