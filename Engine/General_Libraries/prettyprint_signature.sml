
(* ===================================================================== *)
signature PRETTYPRINT_STYLES_SIG =
sig
	type PP = PRETTYPRINT_DATATYPES.PP
	val format_list : (string * (string -> PP list)) list
end;
(* ===================================================================== *)



