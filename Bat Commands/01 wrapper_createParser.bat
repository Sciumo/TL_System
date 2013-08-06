@echo off


call 99_verbose_setAbsolutePaths.bat

REM ====================================================================================================================================================
@echo on
@echo =============================================================================================
@echo creating target parser based on the file         = %BNF%
@echo creating target parser based on the start symbol = %START_SYMBOL%
@echo DOMAIN_FOLDER                                    = %DOMAIN_FOLDER%
@echo =============================================================================================
@echo.
@echo.
@echo off

pause

REM ====================================================================================================================================================
call 01_createParser

@echo on
@echo.
@echo.
@echo Execution of 01_createParser.bat completed.
@echo off

pause
