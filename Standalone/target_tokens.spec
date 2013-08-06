
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ 
  
op_symbol	= [\<\>\=\*\+\-\~\|\&\^]; ---bug, this order is not permitted??
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

datatype lexresult=   SHELL of string * string * {line: word, column: word};

val error = fn x => TextIO.output(TextIO.stdOut,x ^ "\n")
val eof = fn () => SHELL("","eof",getNextTokenPos(""))

val comment_counter	= ref 0;


(* ------------------------------------------------------------------ *)
(* assumes that ">" does not occur as part of a nonterminal symbol *)
fun generateSchemaTokenName( yytext ) =
    let
		fun split(x, []   ) =  raise General.Fail("an_error")
		  | split(x, y::ys) = if x=y then ys else split(x,ys);
													
		fun splitFirst(symbol,[])    = 	[] (* symbol was not in the input list *)
		  | splitFirst(symbol,x::xs) = 	if x = symbol 
						then (* found split point *)
							[]
						else (* keep looking      *)
							x::splitFirst(symbol,xs);
																		
        val s0   = explode(yytext);
        val s1   = split(#"<",s0);
        val s2   = splitFirst(#">",s1);  
    in
        implode(explode("!#schema_variable_") @ s2)        
    end;
	
(* ------------------------------------------------------------------ *)


%%
%full
%header (functor Target_LexFn(val getNextTokenPos : string -> {line: word, column: word}));

letter    			= [A-Za-z];
digit     			= [0-9];
ident		     	= {letter}({letter}|{digit} | "_")*;
integer_value   	= {digit}{digit}*;

ws           		= [\ \t \n];


FILE_alpha        = [a-zA-Z0-9]  	    ;
FILE_alphanumeric = [-a-zA-Z0-9_\/:\.]      ;
FILE_blank        = [\ ]		    ;
FILE_ID           = \"{FILE_alpha}{FILE_alphanumeric}*({FILE_blank}+{FILE_alphanumeric}+)*\"  ;


alpha              = [A-Za-z];
alphanumericPlus   = [A-Za-z0-9_];

schema_id    		= "<" {alpha}{alphanumericPlus}* ">_" {alphanumericPlus}+;
old_end_marker 		= "[:]";
new_end_marker 		= \239\128\155;


%s COMMENT;
%%

<INITIAL> {ws}+ 	=> ( getNextTokenPos(yytext); lex()                                     );

<INITIAL> "module"	=> ( SHELL(yytext           , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "import"	=> ( SHELL(yytext           , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "end"		=> ( SHELL(yytext           , yytext,     getNextTokenPos(yytext))  );

<INITIAL> ";"		=> ( SHELL(yytext           , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "{"		=> ( SHELL(yytext           , yytext,     getNextTokenPos(yytext))  );
<INITIAL> "}"		=> ( SHELL(yytext           , yytext,     getNextTokenPos(yytext))  );
<INITIAL> ":="		=> ( SHELL(yytext           , yytext,     getNextTokenPos(yytext))  );


<INITIAL> "(*"		=> 	( YYBEGIN COMMENT; 
             			 comment_counter := !comment_counter + 1; 
						 getNextTokenPos(yytext); lex()                                 
						);

<COMMENT> "(*"		=> 	( comment_counter := !comment_counter + 1; 
					 	  getNextTokenPos(yytext); lex()
						);
<COMMENT> "*)"		=>  ( comment_counter := !comment_counter - 1; 
						  if !comment_counter = 0 then YYBEGIN INITIAL else (); 
						  getNextTokenPos(yytext); lex()      
                        );
<COMMENT> "\n"		=> ( getNextTokenPos(yytext); lex()                                  );
<COMMENT> .			=> ( getNextTokenPos(yytext); lex()                                  );


<INITIAL> {FILE_ID}	  	  	=> ( SHELL("file_id"    , yytext,     getNextTokenPos(yytext))  );
<INITIAL> {integer_value}	=> ( SHELL("integer_value"        	   		, yytext, getNextTokenPos(yytext))  );
<INITIAL> {ident}			=> ( SHELL("ident"        		   			, yytext, getNextTokenPos(yytext))  );
<INITIAL> {schema_id}      	=> ( SHELL(generateSchemaTokenName(yytext) 	, yytext, getNextTokenPos(yytext))  );
<INITIAL> {old_end_marker} 	=> ( SHELL(""                              	, yytext, getNextTokenPos(yytext))  );
<INITIAL> {new_end_marker} 	=> ( SHELL(""                              	, yytext, getNextTokenPos(yytext))  );

