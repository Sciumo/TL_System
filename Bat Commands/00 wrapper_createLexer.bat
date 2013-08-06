@echo off

call 99_verbose_setAbsolutePaths.bat

REM ====================================================================================================================================================
@echo on
@echo =============================================================================================
@echo Creating target lexer based on the file: %TARGET_TOKENS%
@echo Absolute Path to target lex file:        %TRANSFORMATION_FOLDER_BACKSLASH%\SyntaxLibrary\%TARGET_TOKENS%
@echo Parser location:                         %TL_SYSTEM_BACKSLASH%\Parse
@echo =============================================================================================
@echo.
@echo.
@echo off

pause


REM ====================================================================================================================================================
call 00_createLexer.bat

@echo on
@echo.
@echo.
@echo Execution of 00_createLexer.bat completed.
@echo off

pause
