
call 99_setAbsolutePaths.bat
CD  %TL_SYSTEM_BACKSLASH%\Transform_without_parser

REM ====================================
REM Copying UserLibrary
REM ====================================
rmdir SML_Modules /s/q
mkdir SML_Modules
xcopy %TRANSFORMATION_FOLDER_BACKSLASH%\SML_Modules SML_Modules /s

sml transform_without_parser.sml %TRANSFORMATION_FOLDER%

