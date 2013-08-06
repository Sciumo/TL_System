rem Example build process

rem Parser must have already been built

set TL=%CD%\..\..\TL_System
set DOMAIN=%CD%\..\..\Phase_I_Field_Resolution

call mlton.bat ^
    -mlb-path-var "TL %TL%" ^
    -mlb-path-var "DOMAIN %DOMAIN%" ^
    -output %DOMAIN%\Transformation\bin\transform.exe ^
    -verbose 1 ^
    -const "Exn.keepHistory true" ^
    transform.mlb

%DOMAIN%\Transformation\bin\transform.exe ^
    --dir=%DOMAIN%\Transformation ^
    --grammar=grammar-1_7.bnf ^
    --start-symbol=CompilationUnit
