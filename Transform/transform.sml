(* --------------------------------------------------------------------------------------------- *)

val _ = Environment.setTargetParser (Target.parser)
val _ = Environment.setTargetStringParser (Target.parseString)

(* CONCRETE_REPRESENTATION.fullPrintTree "    \n" (Target.parseString "testing.a.b.c" "miscLabel" "QualifiedId");
print("\n"); *)

val transformFile = OS.Path.joinDirFile {dir = OS.Path.joinDirFile {dir = Environment.getTransformationFolder (), file = "bin"}, file = "transform"}
val _ = Environment.setTransformExe (Transform_Support.transformExe)

val _ = print ("Writing transform: " ^ transformFile ^ "\n")
val _ = SMLofNJ.exportFn (transformFile, Transform_Support.transformExe)

(*
val [targetFile] = CommandLineArgs.args
                   handle Bind => raise General.Fail ("error: exactly one target must be specified")

val _ = Transform_Support.transformFile (targetFile)
*)

(* --------------------------------------------------------------------------------------------- *)
