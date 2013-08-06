@echo off

call 99_verbose_setAbsolutePaths.bat

REM ==============================================================================================================================================================
@echo on
@echo ===========================================================================================
@echo Applying %TL% to %TGT_W_EXTENSION% 
@echo.
@echo TRANSFORMATION_FOLDER_BACKSLASH = %TRANSFORMATION_FOLDER_BACKSLASH%
@echo INPUT_FOLDER                    = %INPUT_FOLDER%
@echo OUTPUT_FOLDER                   = %OUTPUT_FOLDER%
@echo.
@echo ===========================================================================================
@echo.
@echo.
@echo off
pause

call 05b_apply_transform_with_parser.bat

@echo on
@echo.
@echo.
@echo Execution of 05b_apply_transform_with_parser.bat completed.
@echo off

pause
