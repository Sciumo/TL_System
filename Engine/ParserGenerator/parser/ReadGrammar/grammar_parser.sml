(* ReadGrammar/grammar_parser.sml *)

functor GrammarParserFn(structure AST : GRAMMAR_ABSTRACT_SYNTAX) :> sig
    val makeParser : {name:string, inputn:int -> string} -> (int -> unit) -> AST.grammar
end =
  struct
    structure GrammarParserLrVals = GrammarParserLrValsFn(
        structure Token = LrParser.Token
        structure AST = AST
      )

    structure GrammarLexer = GrammarLexFn(
        structure Tokens = GrammarParserLrVals.Tokens
      )

    structure GrammarParser = JoinWithArg(
        structure ParserData = GrammarParserLrVals.ParserData
        structure Lex = GrammarLexer
        structure LrParser = LrParser
      )

    fun makeParser{name, inputn} =
      let
        val source_map = SourceMap.newmap(2, {fileName=name, line=1, column=1})

        fun posToString(lpos, rpos) =
          let
            val {fileName  , line=l_line, column=l_column} = SourceMap.filepos(source_map)(Word.toInt(lpos))
            val {fileName=_, line=r_line, column=r_column} = SourceMap.filepos(source_map)(Word.toInt(rpos))
            fun linecolToString(line, column) = Int.toString(line) ^ "." ^ Int.toString(column)
           in
            fileName ^ ":" ^ linecolToString(l_line, l_column) ^ "-" ^ linecolToString(r_line, r_column)
          end

        fun complain(lpos, rpos)(sev)(msg)(bod) =
          let
            val sevname = case sev of ErrorMsg.WARNING => " Warning: " | ErrorMsg.ERROR => " Error: "
           in
            print(posToString(lpos, rpos) ^ sevname ^ msg ^ "\n")
          end

        fun print_error(s, lpos, rpos) = complain(lpos, rpos)(ErrorMsg.ERROR)(s)(ErrorMsg.nullErrorBody)

        val lexer_arg = {
            commentLevel = ref 0w0,
            stringBuf = ref "",
            lastStart = ref 0w0,
            sourceMap = ref source_map,
            issueMsg = complain
          }

        val lexer = ref(GrammarParser.makeLexer(inputn)(lexer_arg))

        (* val testEOF = GrammarParserLrVals.Tokens.EOF(0w0, 0w0) *)

        fun parser(parser_arg) = (* if GrammarParser.sameToken(#1(GrammarParser.Stream.get(!lexer)), testEOF) then NONE else *)
          let
            val (result, next_lexer) = GrammarParser.parse(15, !lexer, print_error, parser_arg)
           in
            (lexer := next_lexer; result)
          end
       in
        parser
      end
  end
