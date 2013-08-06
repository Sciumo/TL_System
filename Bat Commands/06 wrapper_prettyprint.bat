@echo off

call 99_verbose_setAbsolutePaths.bat

REM ==============================================================================================================================================================
@echo on
@echo ========================================================================
@echo Prettyprinting the transformed version of %TGT_W_EXTENSION% using %FORMAT%
@echo.
@echo TL_SYSTEM_BACKSLASH             = %TL_SYSTEM_BACKSLASH%
@echo TRANSFORMATION_FOLDER_BACKSLASH = %TRANSFORMATION_FOLDER_BACKSLASH%
@echo OUTPUT_FOLDER                   = %OUTPUT_FOLDER%

@echo ========================================================================
@echo.
@echo.
@echo off

pause

REM ==============================================================================================================================================================
call 06_prettyprint.bat

@echo on
@echo.
@echo.
@echo Execution of 06_prettyprint.bat completed.
@echo off

pause
