

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   filename           : universal 
   programmer         : Victor Winter
   date last modified : 1/10/99

   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)

(* ======================================================= *)

structure auxiliary_universal = struct

val unique_counter     = ref 0;

val targetLex_TokenStartPos_ref = ref {line = 0w0, column = 0w0}
val tlLex_TokenStartPos_ref = ref {line = 0w0, column = 0w0}

fun posToString{line, column} = Int.toString(Word.toInt(line)) ^ "." ^ Int.toString(Word.toInt(column))

fun makeGetNextTokenPos(startPos_ref) =
  let
    fun advance(c, pos as {line = lineNum, column = colNum}) = case c of
        #"\n" => {line = lineNum + 0w1, column = 0w1}
      | _     => {line = lineNum, column = colNum + 0w1}

    fun getNextTokenPos(token_string) =
      let
        val cur_pos = !startPos_ref
       in
        (startPos_ref := foldl advance cur_pos (explode token_string); cur_pos)
      end
   in
     getNextTokenPos
  end

exception ParseError of string

end
(* ======================================================= *)


