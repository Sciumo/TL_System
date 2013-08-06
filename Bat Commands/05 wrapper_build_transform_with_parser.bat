@echo off

call 99_verbose_setAbsolutePaths.bat

REM ==============================================================================================================================================================
@echo on
@echo ===========================================================================================
@echo.
@echo TL_SYSTEM_BACKSLASH                 = %TL_SYSTEM_BACKSLASH% 
@echo TRANSFORMATION_FOLDER_BACKSLASH     = %TRANSFORMATION_FOLDER_BACKSLASH%
@echo TRANSFORMATION_FOLDER               = %TRANSFORMATION_FOLDER%
@echo BNF                                 = %BNF%
@echo START_SYMBOL                        = %START_SYMBOL%
@echo TARGET_TOKENS                       = %TARGET_TOKENS%
@echo.
@echo ===========================================================================================
@echo.
@echo.
@echo off
pause

call 05_build_transform_with_parser.bat

@echo on
@echo.
@echo.
@echo Execution of 05_build_transform_with_parser.bat completed.
@echo off

pause
