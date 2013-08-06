
(* ================================================================================================================ *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(*                                       CommandLineArgs                                                            *)
(* ---------------------------------------------------------------------------------------------------------------- *)
(* ================================================================================================================ *)

structure CommandLineArgs =
struct

	val args = CommandLine.arguments();
	val _ = map (fn x_str => 
						let
						val xs = explode x_str
						in
							map (fn x => print(Char.toString x)) xs;
							print("\n")
						end
					) args
									
	val [_, transformation_folder, bnf, start_symbol, tlp, standalone_name] = args
										
	val TGT_grammar = OS.Path.joinDirFile {dir = OS.Path.joinDirFile {dir = transformation_folder, file = "Syntax"}, file = bnf}

end;


