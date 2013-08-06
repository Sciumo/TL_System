(* ----------------------------------------------------------------------------------------------------------------------- *)

structure Grammar_AbstractSyntax : GRAMMAR_ABSTRACT_SYNTAX =
  struct
    type filepos = {left:word, right:word}
    type symbol = {name : string, delim_opt : char option, filepos : filepos}
    
    datatype
        regular_expression =
            SYMBOL of symbol
          | SEQUENCE of regular_expression list
          | CHOICE of regular_expression * regular_expression
          | REPETITION of regular_expression

    datatype
        precassoc_rule =
            NON_ASSOCIATIVE of symbol list
          | LEFT_ASSOCIATIVE of symbol list
          | RIGHT_ASSOCIATIVE of symbol list
    
    type production = {name : string, filepos : filepos, regex : regular_expression, precsymb_opt : symbol option}
    
    datatype grammar = GRAMMAR of {precassoc_rules : precassoc_rule list, production_list : production list}
  end

(* ----------------------------------------------------------------------------------------------------------------------- *)
