@echo off

call 99_verbose_setAbsolutePaths.bat

REM ==============================================================================================================================================================
@echo on
@echo ===========================================================================================
@echo Applying %TL% to %TGT% 
@echo.
@echo TL_SYSTEM                   = %TL_SYSTEM% 
@echo DOMAIN_FOLDER               = %DOMAIN_FOLDER%
@echo DOMAIN_FOLDER_BACKSLASH     = %DOMAIN_FOLDER_BACKSLASH%
@echo TGT_EXTENSION               = %TGT_EXTENSION% 
@echo CREATE_TRANSFORM_EXE_FLAG   = %CREATE_TRANSFORM_EXE_FLAG%
@echo.
@echo ===========================================================================================
@echo.
@echo.
@echo off
pause

call 04_build_transform_without_parser.bat

@echo on
@echo.
@echo.
@echo Execution of 04_build_transform_without_parser.bat completed.
@echo off

pause
