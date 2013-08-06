@echo off

call 99_verbose_setAbsolutePaths.bat

REM ==============================================================================================================================================================
@echo on
@echo ===========================================================================================
@echo Applying %TL% to %TGT% 
@echo.
@echo TL_SYSTEM                   = %TL_SYSTEM% 
@echo DOMAIN_FOLDER               = %DOMAIN_FOLDER%
@echo TGT_W_EXTENSION             = %TGT_W_EXTENSION%
@echo.
@echo ===========================================================================================
@echo.
@echo.
@echo off
pause

call 04b_apply_transform_without_parser.bat

@echo on
@echo.
@echo.
@echo Execution of 04b_apply_transform_without_parser.bat completed.
@echo off

pause
