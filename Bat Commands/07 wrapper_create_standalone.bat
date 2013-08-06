@echo off

call 99_verbose_setAbsolutePaths.bat

REM ==============================================================================================================================================================
@echo on
@echo ===========================================================================================
@echo Applying %TL% to %TGT% 
@echo.
@echo DOMAIN_FOLDER               = %DOMAIN_FOLDER%
@echo BNF                         = %BNF%
@echo START_SYMBOL                = %START_SYMBOL%
@echo TL                          = %TL%
@echo STANDALONE_NAME             = %STANDALONE_NAME%
@echo.
@echo ===========================================================================================
@echo.
@echo.
@echo off
pause

call 07_create_standalone.bat

@echo on
@echo.
@echo.
@echo Execution of 07_create_standalone.bat completed.
@echo off

pause
