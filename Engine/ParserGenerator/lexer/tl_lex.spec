(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
datatype lexresult =   SHELL of string * string * {line: word, column: word}
                     | SDT of string * CONCRETE_REPRESENTATION.TREE * {line: word, column: word} ;



fun stripQuotes( str ) = let
                             val tail         = tl (explode str) handle Empty => raise General.Fail("Error in tl_lex_spec: empty string token encountered.\n");
                             val the_str_list = List.take(tail, List.length(tail) - 1)
                         in
                              implode the_str_list
                         end;




val error          = fn x => TextIO.output(TextIO.stdOut,x ^ "\n")
val eof            = fn () => SHELL("","dollar",getNextTokenPos(""))
val remove_quotes  = fn x => let
								val xs = explode x
							 in
								implode( List.take(xs, List.length(xs) - 1) )
							 end
							 
(* val remove_quotes  = fn x => implode(LIST_OPS.remove_last(tl(explode(x))))  *)
val counter        = ref 0; 
val sig_counter    = ref 0;

fun inc_sigCounter() = (
						   sig_counter := !sig_counter + 1; if !sig_counter > 1 then raise General.Fail("\nTL Parser Error: A TL program may contain at most one signature declaration.\n\n") else ()
					   )


%%

%full
%header (functor TL_LexFn(val getNextTokenPos : string -> {line: word, column: word};
                          val call_aux_parser : string -> (int -> string) -> CONCRETE_REPRESENTATION.TREE));

alpha        = [A-Za-z];
digit        = [0-9];
alphanumeric = [A-Za-z0-9_'];
identifier   = {alpha}{alphanumeric}*;
string       = \"{alphanumeric}*\";
comment      = "//" .* ;
ws           = [\ \t\n\r];

TL_alpha           = [A-Za-z_'];
TL_alphanumeric    = [A-Za-z0-9_'];
schema_id          = "<" {TL_alpha}{TL_alphanumeric}* ">_" {TL_alphanumeric}+ ;

old_begin_marker = {identifier} "[:]";
new_begin_marker = {identifier} \239\128\154;

%s COMMENT ;
%%

{ws}+                         => ( getNextTokenPos(yytext); lex()  );

<INITIAL> {schema_id}         => ( SHELL("schema_var"          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> {new_begin_marker}  => ( let val pos = getNextTokenPos(yytext) in SDT("target_tree_phrase", call_aux_parser(yytext)(yyinput), pos) end );
<INITIAL> {old_begin_marker}  => ( let val pos = getNextTokenPos(yytext) in SDT("target_tree_phrase", call_aux_parser(yytext)(yyinput), pos) end );

<INITIAL> {comment}           => ( getNextTokenPos(yytext); lex()  );

<INITIAL> "/*"                => ( YYBEGIN COMMENT; 
                                   counter := !counter + 1; 
                                   getNextTokenPos(yytext); lex()                                  );

<COMMENT> "/*"                => ( counter := !counter + 1; getNextTokenPos(yytext); lex()         );
<COMMENT> "*/"                => ( counter := !counter - 1; 
                                   if !counter = 0 then YYBEGIN INITIAL else (); 
                                   getNextTokenPos(yytext); lex()                                  );
<COMMENT> .                   => ( getNextTokenPos(yytext); lex()                                  );


<INITIAL> "<;"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> ";>"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "<*"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "*>"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "<+"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "+>"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "<+>"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> "module"     		=> ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "DerivedForm" 	=> ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "import_opened"	=> ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "import_closed"	=> ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> "def"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "strategy"   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> "fold"       => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "foldS"      => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "hide"       => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lift"       => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "transient"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "opaque"     => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "raise"      => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "mapL"       => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "mapR"       => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "mapB"       => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> "if"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "{"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "}"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "andalso"    => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "orelse"     => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "not"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "true"       => ( SHELL("bool_value"    , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "false"      => ( SHELL("bool_value"    , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "ID"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "SKIP"       => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "FAIL"       => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> "TdlBul"     => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "TDL"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "TDR"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "BUL"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "BUR"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "TD"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "FIX"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lseq_tdl"   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lseq_tdr"   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lseq_bul"   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lseq_bur"   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rseq_tdl"   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rseq_tdr"   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rseq_bul"   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rseq_bur"   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lcond_tdl"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lcond_tdr"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lcond_bul"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lcond_bur"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rcond_tdl"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rcond_tdr"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rcond_bul"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rcond_bur"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lstar_tdl"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lstar_tdr"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lstar_bul"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "lstar_bur"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rstar_tdl"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rstar_tdr"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rstar_bul"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "rstar_bur"  => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> "term"       => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> "^"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "||"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "&&"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> "=="          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "!="          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "<"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> ">"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "<="         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> ">="         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "+"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "-"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "*"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "/"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "div"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "mod"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "!"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "~"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> ","          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "("          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> ")"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> "->"         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "="          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> ":="         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> ":"          => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> "."                           => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "sml"                         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "UserDefinedFunctions"        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "sig"                         => ( inc_sigCounter(); SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "end"                         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "<" {identifier} ">"          => ( SHELL("schemaType"    , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "unit"                        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "int"                         => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "real"                        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "string"                      => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "bool"                        => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "precision"                   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "verbosity"                   => ( SHELL(yytext          , yytext,     getNextTokenPos(yytext))  );

<INITIAL> {identifier} 		  		    => ( SHELL("id"         , yytext, getNextTokenPos(yytext))  );
<INITIAL> {digit}+  			      => ( SHELL("int_value" 	, yytext, getNextTokenPos(yytext))  );
<INITIAL> {digit}*"."{digit}+ 		=> ( SHELL("real_value"	, yytext, getNextTokenPos(yytext))  );
<INITIAL> "\"" ([^\"\\] | \\. )* "\""  	=> ( SHELL("string_value",stripQuotes(yytext), getNextTokenPos(yytext))  );
