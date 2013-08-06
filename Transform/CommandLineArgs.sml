(* ============================================================================================== *)
(* CommandLineArgs                                                                                *)
(* ============================================================================================== *)

local
    val grammarOpt = ref NONE
    val startSymbolOpt = ref NONE
    
    val args = CommandLine.arguments ()
in
    structure CommandLineArgs =
    struct
        fun parseArgs (args) = 
            GetOpt.getOpt
                {
                    argOrder = GetOpt.Permute,
                    errFn = (fn opt => raise General.Fail ("Invalid option: " ^ opt)),
                    options =
                        [
                            {
                                short = "d", long = ["dir"], help = "?",
                                desc = GetOpt.ReqArg 
                                    ((
                                        fn f => Environment.setTransformationFolder (f)
                                    ), "TRANSFORMATION_DIRECTORY")
                            },
                            {
                                short = "g", long = ["grammar"], help = "?",
                                desc = GetOpt.ReqArg 
                                    ((
                                        fn f => grammarOpt := SOME f
                                    ), "GRAMMAR")
                            },
                            {
                                short = "s", long = ["start-symbol"], help = "?",
                                desc = GetOpt.ReqArg 
                                    ((
                                        fn f => startSymbolOpt := SOME f
                                    ), "START_SYMBOL")
                            },
                            {
                                short = "t", long = ["target-dir"], help = "?",
                                desc = GetOpt.ReqArg 
                                    ((
                                        fn f => Environment.setTargetFolder (f)
                                    ), "TARGET_DIRECTORY")
                            },
                            {
                                short = "i", long = ["target-index"], help = "?",
                                desc = GetOpt.ReqArg 
                                    ((
                                        fn f => Environment.setTargetIndex (case Int.fromString f of
                                                                                SOME i => i 
                                                                              | NONE   => raise General.Fail("Target index should be an integer.")
                                                                            )
                                    ), "TARGET_INDEX")
                            },
                            {
                                short = "p", long = ["tlp"], help = "?",
                                desc = GetOpt.ReqArg 
                                    ((
                                        fn f => Environment.setTL (f)
                                    ), "TRANSFORMATION_PROGRAM")
                            },
                            {
                                short = "T", long = ["target-type"], help = "?",
                                desc = GetOpt.ReqArg
                                    ((
                                        fn "single" => Environment.setTransformerMode Environment.SingleFile
                                         | "multi"  => Environment.setTransformerMode Environment.MultiFile
                                         | _ => raise Fail ("invalid target-type")
                                    ), "TARGET_TYPE")
                            }
                        ]
                }
                args
        
        val (opts, args) = parseArgs (args)
        
        val grammar = if isSome (!grammarOpt) then valOf (!grammarOpt) else ""
        val startSymbol = if isSome (!startSymbolOpt) then valOf (!startSymbolOpt) else ""
    end
end;
