rem Example build process.

set TL=%CD%\..\..\TL_System
set DOMAIN=%CD%\..\..\Phase_I_Field_Resolution

mlyacc %TL%\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm
mllex %TL%\Engine\ParserGenerator\lexer\tl_lex.spec

mllex %DOMAIN%\Transformation\bin\target_tokens.spec

call mlton.bat ^
    -mlb-path-var "TL %TL%" ^
    -mlb-path-var "DOMAIN %DOMAIN%" ^
    -output %DOMAIN%\Transformation\bin\parser.exe ^
    -verbose 1 ^
    -const "Exn.keepHistory true" ^
    %TL%\Parse\parser.mlb

%DOMAIN%\Transformation\bin\parser.exe ^
    %DOMAIN%\Transformation ^
    grammar-1_7.bnf ^
    CompilationUnit
