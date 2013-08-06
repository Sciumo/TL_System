
call 99_setAbsolutePaths.bat

CD  %TL_SYSTEM_BACKSLASH%\Parse
del /q target_tokens.spec
del /q target_tokens.spec.sml
copy %TRANSFORMATION_FOLDER_BACKSLASH%\Syntax\%TARGET_TOKENS% target_tokens.spec


sml createLexer.sml

