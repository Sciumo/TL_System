
call 99_setAbsolutePaths.bat
CD  %TL_SYSTEM_BACKSLASH%\Transform_with_parser


REM ====================================
REM Copying Lex files
REM ====================================
del /q target_tokens.spec
del /q target_tokens.spec.sml
copy %TRANSFORMATION_FOLDER_BACKSLASH%\Syntax\%TARGET_TOKENS% target_tokens.spec


REM ====================================
REM Copying UserLibrary
REM ====================================
rmdir SML_Modules /s/q
mkdir SML_Modules
xcopy %TRANSFORMATION_FOLDER_BACKSLASH%\SML_Modules SML_Modules /s

sml transform_with_parser.sml %TRANSFORMATION_FOLDER% %BNF% %START_SYMBOL% 

