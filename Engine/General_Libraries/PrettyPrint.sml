local
    structure OSP = OS.Path
in
structure PrettyPrint =
struct

structure PP_Views = PRETTYPRINT_ENGINE_FN (structure UserStyles = PRETTYPRINT_STYLES)

(* ------------------------------------------------------------------------------------------- *)
fun ppToFile (programTerm, filename) =
    let
        val program = Strategic_Values.getTerm programTerm

        val outFilename = OSP.concat (Environment.getOutputFolder (), filename)

        val _ = FileUtility.mkDirs (OSP.dir outFilename)
        val outStream = TextIO.openOut outFilename
    in
        PP_Views.prettyprint (outStream, program);
        TextIO.closeOut outStream
    end

(* ------------------------------------------------------------------------------------------- *)
fun pp (programTerm, extension) =
    ppToFile (programTerm, OSP.joinBaseExt {base = Environment.getTargetFileName (), ext = SOME extension})

(* ------------------------------------------------------------------------------------------- *)
fun ppToString programTerm =
    PP_Views.prettyprintString programTerm

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*                                 Exported Function List                                      *)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)

local
    fun TL_ppToFile [programTerm, filenameStringOrTerm] =
        let
            val filename = Strategic_Values.getString filenameStringOrTerm
               handle _ => Strategic_Values.termToString filenameStringOrTerm
        in
            ppToFile (programTerm, filename);
            ABSTRACT_REPRESENTATION.TRUE
        end
      | TL_ppToFile _ = raise Fail ("PrettyPrint.TL_ppToFile: expected 2 arguments")

    fun TL_pp [programTerm] =
        (
            pp (programTerm, Environment.getTargetExtension ());
            ABSTRACT_REPRESENTATION.TRUE
        )
      | TL_pp _ = raise Fail "PrettyPrint.TL_pp: expects 1 argument"
      
    fun ppTo_stdOut [term] =
        let
            val t = Strategic_Values.getTerm term
        in
            PP_Views.prettyprint (TextIO.stdOut, t);
            ABSTRACT_REPRESENTATION.TRUE
        end
      | ppTo_stdOut _ = raise General.Fail ("Error in PrettyPrint.ppTo_stdOut: expects 1 argument");

in
    val functions = 
        [
            ("ppToFile", TL_ppToFile),
            ("ppTo_stdOut"      , ppTo_stdOut  ),
            ("prettyprint", TL_pp)
        ]
end

end (* struct *)
end (* local *)
