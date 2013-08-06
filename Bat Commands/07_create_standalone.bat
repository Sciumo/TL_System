
call 99_setAbsolutePaths.bat

REM ====================================
REM Parse TL
REM ====================================
%SML_RUN% @SMLload=%TRANSFORMATION_FOLDER%/bin/parser.X86-win32 TLP %TRANSFORMATION_FOLDER% %TL%


REM ==================================================================================================================

CD  %TL_SYSTEM_BACKSLASH%\Standalone

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




sml createStandalone.sml %TRANSFORMATION_FOLDER% %BNF% %START_SYMBOL% %TL% %STANDALONE_NAME%

