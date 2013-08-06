rem Example build process

set TL=%CD%\..\..\TL_System
set DOMAIN=%CD%\..\..\Phase_I_Field_Resolution

call mlton.bat ^
    -mlb-path-var "TL %TL%" ^
    -mlb-path-var "DOMAIN %DOMAIN%" ^
    -output %DOMAIN%\Transformation\bin\prettyprint.exe ^
    -verbose 1 ^
    -const "Exn.keepHistory true" ^
    prettyprint.mlb
