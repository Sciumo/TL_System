@echo off

REM IMPORTANT: Note that here the DOMAIN_FOLDER path uses forward slashes (as well as the composition in the call). This is required because this string is fed to SML.
REM For some reason, I have not been able to define SML_RUN relative to SML.

REM In the summary below, for variables that end in the string "_BACKSLASH" it is assumed that their (string) values contain no forward
REM slashes. Such values are appropriate for system-level calls (e.g., XP command line calls). 

REM In contrast, for variables that do not end in "_BACKSLASH" it is assumed that their (string) values contain no backslashes.
REM Such values are appropriate as arguments to sml functions.


REM ================================
REM Alphabetical List
REM ================================
REM 
REM %BNF%
REM %DOMAIN_FOLDER%
REM %FORMAT%
REM %INPUT_FOLDER%
REM %OUTPUT_FOLDER%
REM %STANDALONE_NAME%
REM %START_SYMBOL%
REM %SML_RUN% 
REM %TARGET_TOKENS% 
REM %TGT_W_EXTENSION% 
REM %TL%
REM %TL_SYSTEM_BACKSLASH%		
REM %TRANSFORMATION_FOLDER%
REM %TRANSFORMATION_FOLDER_BACKSLASH%


REM ================================
REM Absolute Paths -- System-level
REM ================================
SET MY_LOCATION_BACKSLASH="C:\Users\vwinter\UNO-Courses\PhDthesis\AZ\Domains"
SET MY_LOCATION="C:/Users/vwinter/UNO-Courses/PhDthesis/AZ/Domains"
SET MY_DOMAIN_NAME="Victor_01"


SET TL_SYSTEM_BACKSLASH="C:\Users\vwinter\UNO-Hats\TL_Redesign\Bundle\TL_System"
REM TL_SYSTEM could be made a system-level environment variable.


SET TRANSFORMATION_FOLDER_BACKSLASH=%MY_LOCATION_BACKSLASH%\%MY_DOMAIN_NAME%\Transformation
SET SML_RUN="C:/sml/bin/.run/run.x86-win32.exe"


REM ================================
REM Absolute Paths as Strings - SML-level
REM ================================
SET DOMAIN_FOLDER=%MY_LOCATION%/%MY_DOMAIN_NAME%
SET INPUT_FOLDER=%MY_LOCATION%/%MY_DOMAIN_NAME%/Input
SET OUTPUT_FOLDER=%MY_LOCATION%/%MY_DOMAIN_NAME%/Output
SET TRANSFORMATION_FOLDER=%MY_LOCATION%/%MY_DOMAIN_NAME%/Transformation

REM ================================
REM Transformaion/SyntaxLibrary
REM ================================
SET BNF="simple.bnf"
SET START_SYMBOL="prog"
SET TARGET_TOKENS="simple.spec"
SET FORMAT="Basic_Style.sty"


REM ================================
REM Transformation/TL_Library
REM ================================
SET TL="test_01"

REM ================================
REM Domain_Data/Input
REM ================================
SET TGT_W_EXTENSION="prog_01.tgt"
SET MULTIFILE_TGT_W_EXTENSION="main.listfile"

REM ================================
REM Standalone
REM ================================

SET STANDALONE_NAME="migrator"
