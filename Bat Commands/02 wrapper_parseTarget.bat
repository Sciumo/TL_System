@echo off

call 99_verbose_setAbsolutePaths.bat

REM ====================================================================================================================================================
@echo on
@echo =============================================================================================
@echo parsing target program = %TGT_W_EXTENSION%
@echo DOMAIN_FOLDER          = %DOMAIN_FOLDER%
@echo =============================================================================================
@echo.
@echo.
@echo off

pause

call 02_parseTarget

@echo on
@echo.
@echo.
@echo Execution of 02_parseTarget.bat completed.
@echo off

pause
