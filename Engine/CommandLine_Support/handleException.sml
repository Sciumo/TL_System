structure HANDLER =
struct

(* --------------------------------------------------------------------------------------------- *)
fun handleException(message, e) =
    let
        val TAG = "<FAIL>"
        fun aux(Empty) =
                (
                    print("\n\nSML exception = Empty\n" );
                    print(message)
                )
          | aux(General.Bind) =
                (
                    print("\n" ^ TAG ^ "\nSML exception = General.Bind\n" );
                    print(message)
                )
          | aux(General.Chr) =
                (
                    print("\n\nSML exception = General.Chr\n" );
                    print(message)
                )
          | aux(General.Div) =
                (
                    print("\n\nSML exception = General.Div\n" );
                    print(message)
                )
          | aux(General.Domain) =
                (
                    print("\n\nSML exception = General.Domain\n" );
                    print(message)
                )
          | aux(General.Fail(msg)) =
                (
                    print("\n" ^ TAG ^ "\nSML exception = General.Fail(\"" ^ msg ^ "\")\n");
                    print(message)
                )
          | aux(General.Match) =
                (
                    print("\n" ^ TAG ^ "\nSML exception = General.Match\n" );
                    print(message)
                )
          | aux(General.Overflow) =
                (
                    print("\n\nSML exception = General.Overflow\n" );
                    print(message)
                )
          | aux(General.Size) =
                (
                    print("\n\nSML exception = General.Size\n" );
                    print(message)
                )
          | aux(General.Span) =
                (
                    print("\n\nSML exception = General.Span\n" );
                    print(message)
                )
          | aux(General.Subscript) =
                (
                    print("\n\nSML exception = General.Subscript\n" );
                    print(message)
                )
          | aux(Option) =
                (
                    print("\n\nSML exception = Option\n" );
                    print(message)
                )
          | aux(IO.Io{cause=e, function=fun_str, name=name_str}) =
                (
                    print("\n" ^ TAG ^ "\nSML exception = IO.Io" );
                    print("\nfunction = " ^ fun_str);
                    print("\nname = " ^ name_str);
                    print("\nException Name = " ^ General.exnName(e) ^ "\n");
                    print("Exception Message = " ^ General.exnMessage(e) ^ "\n");
                    print(message)
                )
          | aux(OS.SysErr(s,_)) =
                (
                    print("\n" ^ TAG ^ "\nSML exception = OS.SysErr" );
                    print("\nProblem: " ^ s ^ "\n");
                    print(message)
                )
          | aux ex =
                (
                    print("\n" ^ TAG ^ "\nSML exception = <unexpected> (" ^ General.exnName ex ^ ")\n");
                    print(message)
                );
    in
        aux e;
        print ("Exception history:\n");
        map (fn x => print ("\t" ^ x ^ "\n")) (SMLofNJ.exnHistory e);
        print ("\n");
        OS.Process.exit OS.Process.failure
    end
(* --------------------------------------------------------------------------------------------- *)
end;
