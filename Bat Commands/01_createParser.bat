
call 99_setAbsolutePaths.bat
CD  %TL_SYSTEM_BACKSLASH%\Parse
sml createParser.sml %TRANSFORMATION_FOLDER% %BNF% %START_SYMBOL%
