
call 99_setAbsolutePaths.bat
CD  %TL_SYSTEM_BACKSLASH%\PrettyPrint
del /q format.sty
del /s/q CM
copy %TRANSFORMATION_FOLDER_BACKSLASH%\Syntax\%FORMAT% format.sty
sml prettyprint.sml %OUTPUT_FOLDER%/%TGT_W_EXTENSION%

