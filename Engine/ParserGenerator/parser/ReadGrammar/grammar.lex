(* ReadGrammar/grammar.lex *)

type pos = word
type svalue = Tokens.svalue
type ('a, 'b) token = ('a, 'b) Tokens.token
type lexresult = (svalue, pos) token

type arg =
  {
    commentLevel : word ref,
    stringBuf : string ref,
    lastStart : word ref,
    sourceMap : SourceMap.sourcemap ref,
    issueMsg : pos * pos -> ErrorMsg.complainer
  }

open ErrorMsg

fun mkpos(n, s) = (Word.fromInt n, Word.fromInt(n + size(s) - 1))

fun mkpos'(t, n, s) = (t, Word.fromInt n, Word.fromInt(n + size(s) - 1))

fun mkstr({stringBuf, lastStart, issueMsg, ...} : arg, isClosed, endPos) =
  let
    val _ = if not isClosed then issueMsg (!lastStart, endPos) ERROR "unclosed string" nullErrorBody else ()

    val tok = Tokens.LID(!stringBuf, !lastStart, endPos)
   in
    (stringBuf := ""; lastStart := 0w0; tok)
  end

fun
  addChar({stringBuf, ...} : arg, SOME c, NONE) = stringBuf := !stringBuf ^ String.str(c)
| addChar({stringBuf, issueMsg, ...} : arg, c_opt, SOME{pos, sev, msg}) =
  (
    case c_opt of SOME c => stringBuf := !stringBuf ^ String.str(c)
      | NONE => issueMsg pos sev msg nullErrorBody
  )
| addChar _ = raise General.Fail("Bug:  invalid case of addChar")

fun eof ({commentLevel, stringBuf, lastStart, sourceMap, issueMsg}) =
  let
      val pos = Word.max(!lastStart + 0w2, Word.fromInt(SourceMap.lastChange(!sourceMap)))
      val _ = if !commentLevel > 0w0
	            then issueMsg (pos, pos) ERROR "unclosed comment" nullErrorBody
              else ()
   in
	Tokens.EOF(pos, pos)
  end

%%

%header (functor GrammarLexFn(structure Tokens : Grammar_TOKENS) : ARG_LEXER);

%arg ({commentLevel, stringBuf, lastStart, sourceMap, issueMsg});

%s COMMENT STRING S_CONT;


WS =            [\000-\009\011-\032]+;

EOL =           [\010];

LETTER =        [A-Za-z];

DEC_DIGIT =     [0-9];

HEX_DIGIT =     ( {DEC_DIGIT} | [a-fA-F] );

ALNUM =         ( {LETTER} | {DEC_DIGIT} | \' | "_" );

ID =            {LETTER}  {ALNUM}*;

TID =           "<" {ID} ">";

ESCAPE =        ( [abtnvfr] | "^" [@-_] | {DEC_DIGIT}{3} | "u" {HEX_DIGIT}{4} | \" | "\\" );

%%

<INITIAL>{WS}           =>  ( continue() );
<INITIAL>{EOL}          =>  ( SourceMap.newline(!sourceMap)(yypos); continue() );
<INITIAL>"::="          =>  ( Tokens.EQUALS(mkpos(yypos, yytext)) );
<INITIAL>"("            =>  ( Tokens.LPAREN(mkpos(yypos, yytext)) );
<INITIAL>")"            =>  ( Tokens.RPAREN(mkpos(yypos, yytext)) );
<INITIAL>"["            =>  ( Tokens.LBRACK(mkpos(yypos, yytext)) );
<INITIAL>"]"            =>  ( Tokens.RBRACK(mkpos(yypos, yytext)) );
<INITIAL>"{"            =>  ( Tokens.LBRACE(mkpos(yypos, yytext)) );
<INITIAL>"}"            =>  ( Tokens.RBRACE(mkpos(yypos, yytext)) );
<INITIAL>"|"            =>  ( Tokens.VBAR(mkpos(yypos, yytext)) );
<INITIAL>"*"            =>  ( Tokens.ASTERISK(mkpos(yypos, yytext)) );
<INITIAL>"+"            =>  ( Tokens.PLUS(mkpos(yypos, yytext)) );
<INITIAL>"?"            =>  ( Tokens.QUESTION(mkpos(yypos, yytext)) );
<INITIAL>"."            =>  ( Tokens.END_PRODUCTION(mkpos(yypos, yytext)) );
<INITIAL>"(*"	        =>  ( YYBEGIN COMMENT; commentLevel := 0w1; lastStart := Word.fromInt yypos; continue() );
<INITIAL>"*)"	        =>  ( issueMsg (mkpos(yypos, yytext)) ERROR "unmatched close comment" nullErrorBody; continue() );
<INITIAL>\"             =>  ( YYBEGIN STRING; lastStart := Word.fromInt yypos; continue() );
<INITIAL>{ID}           =>  ( Tokens.ID(mkpos'(yytext, yypos, yytext)) );
<INITIAL>{TID}          =>  ( Tokens.TID(mkpos'(String.substring(yytext, 1, String.size(yytext) - 2), yypos, yytext)) );
<INITIAL>"%NON_ASSOC"   =>  ( Tokens.NON_ASSOC(mkpos(yypos, yytext)) );
<INITIAL>"%LEFT_ASSOC"  =>  ( Tokens.LEFT_ASSOC(mkpos(yypos, yytext)) );
<INITIAL>"%RIGHT_ASSOC" =>  ( Tokens.RIGHT_ASSOC(mkpos(yypos, yytext)) );
<INITIAL>"%PREC"        =>  ( Tokens.PREC(mkpos(yypos, yytext)) );
<INITIAL>.              =>  ( issueMsg (mkpos(yypos, yytext)) ERROR "illegal token" nullErrorBody; continue() );

<COMMENT>"*)"           =>  ( commentLevel := !commentLevel - 0w1; if !commentLevel = 0w0 then YYBEGIN INITIAL else (); continue());
<COMMENT>"(*"           =>  ( commentLevel := !commentLevel + 0w1; continue() );
<COMMENT>{EOL}          =>  ( SourceMap.newline(!sourceMap)(yypos); continue() );
<COMMENT>.              =>  ( continue() );

<STRING>\"              =>  ( YYBEGIN INITIAL; mkstr(yyarg, true, Word.fromInt(yypos) + 0w1) );
<STRING>{EOL}           =>  ( YYBEGIN INITIAL; SourceMap.newline(!sourceMap)(yypos); mkstr(yyarg, false, Word.fromInt yypos) );
<STRING>\\{ESCAPE}      =>  ( addChar(yyarg, Char.fromString(yytext), SOME{pos=mkpos(yypos, yytext), sev=WARNING, msg="illegal string escape ignored"}); continue() );
<STRING>\\{WS}          =>  ( YYBEGIN S_CONT; continue() );
<STRING>\\{EOL}         =>  ( YYBEGIN S_CONT; SourceMap.newline(!sourceMap)(yypos+1); continue() );
<STRING>\\              =>  ( addChar(yyarg, SOME #"\\", NONE); issueMsg (mkpos(yypos, yytext)) WARNING "illegal string escape ignored" nullErrorBody; continue() );
<STRING>[\032-\126]     =>  ( addChar(yyarg, SOME(String.sub(yytext, 0)), NONE); continue());
<STRING>.               =>  ( issueMsg (mkpos(yypos, yytext)) WARNING "illegal non-printing character in string ignored" nullErrorBody; continue() );

<S_CONT>\\              =>  ( YYBEGIN STRING; continue());
<S_CONT>{WS}		    =>  ( continue() );
<S_CONT>{EOL}           =>  ( SourceMap.newline(!sourceMap)(yypos); continue() );
<S_CONT>\"              =>  ( YYBEGIN INITIAL; issueMsg (mkpos(yypos, yytext)) WARNING "unclosed string continuation sequence" nullErrorBody; mkstr(yyarg, true, Word.fromInt(yypos) + 0w1) );
<S_CONT>[\032-\126]     =>  ( YYBEGIN STRING; addChar(yyarg, SOME(String.sub(yytext, 0)), NONE); issueMsg (mkpos(yypos, yytext)) WARNING "unclosed string continuation sequence" nullErrorBody; continue() );
<S_CONT>.               =>  ( issueMsg (mkpos(yypos, yytext)) WARNING "illegal non-printing character in string continuation sequence ignored" nullErrorBody; continue() );
