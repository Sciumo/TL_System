@echo off

call 99_verbose_setAbsolutePaths.bat

REM ====================================================================================================================================================
@echo on
@echo ============================================================================================
@echo parsing tl program = %TL%
@echo DOMAIN_FOLDER      = %DOMAIN_FOLDER%
@echo ============================================================================================
@echo.
@echo.
@echo off

pause

call 03_parseTL.bat

@echo on
@echo.
@echo.
@echo Execution of 03_parseTL.bat completed.
@echo off

pause