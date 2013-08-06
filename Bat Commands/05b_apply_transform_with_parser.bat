
call 99_setAbsolutePaths.bat

SET MULTIFILE_FLAG="false"

REM CD is needed so that Err log shows up in the bin directory.
CD %TRANSFORMATION_FOLDER_BACKSLASH%\bin
%SML_RUN% @SMLload=%TRANSFORMATION_FOLDER%/bin/transform_with_parser.x86-win32 %INPUT_FOLDER% %OUTPUT_FOLDER% %TL% %TGT_W_EXTENSION% %MULTIFILE_FLAG%

