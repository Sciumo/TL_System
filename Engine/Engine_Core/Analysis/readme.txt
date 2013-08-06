To compile:
 - append the following file paths to file ../../parser_lib.cm
  Engine_Core/Analysis/optimize.sml
  Engine_Core/Analysis/environment.sml
  Engine_Core/Analysis/util.sml
  Engine_Core/Analysis/unification.sml
  Engine_Core/Analysis/grammar.sml
  Engine_Core/Analysis/reduce.sml
  Engine_Core/Analysis/composition.sml
  Engine_Core/Analysis/typecheck.sml 

 - launch ../../stabilize.bat
 - if no errors are reported, then compilation completed successfully

Also:
 -  append the following file paths to file ../../../Parse/parser.cm
  ../Engine/Engine_Core/Analysis/optimize.sml
  ../Engine/Engine_Core/Analysis/environment.sml
  ../Engine/Engine_Core/Analysis/util.sml
  ../Engine/Engine_Core/Analysis/unification.sml
  ../Engine/Engine_Core/Analysis/grammar.sml
  ../Engine/Engine_Core/Analysis/reduce.sml
  ../Engine/Engine_Core/Analysis/composition.sml
  ../Engine/Engine_Core/Analysis/typecheck.sml
