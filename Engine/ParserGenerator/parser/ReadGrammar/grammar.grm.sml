functor GrammarParserLrValsFn(
            structure Token : TOKEN;
            structure AST : GRAMMAR_ABSTRACT_SYNTAX)
         = 
struct
structure ParserData=
struct
structure Header = 
struct
(*#line 1.2 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)(* ReadGrammar/grammar.grm *)

open AST


(*#line 15.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
end
structure LrTable = Token.LrTable
structure Token = Token
local open LrTable in 
val table=let val actionRows =
"\
\\001\000\001\000\003\000\000\000\
\\001\000\001\000\013\000\002\000\012\000\000\000\
\\001\000\001\000\018\000\002\000\017\000\003\000\016\000\000\000\
\\001\000\009\000\052\000\015\000\041\000\000\000\
\\001\000\011\000\051\000\015\000\041\000\000\000\
\\001\000\013\000\050\000\015\000\041\000\000\000\
\\001\000\014\000\022\000\000\000\
\\001\000\014\000\023\000\000\000\
\\001\000\019\000\025\000\000\000\
\\001\000\019\000\026\000\000\000\
\\001\000\019\000\027\000\000\000\
\\001\000\019\000\047\000\000\000\
\\001\000\019\000\053\000\000\000\
\\001\000\020\000\000\000\000\000\
\\055\000\000\000\
\\056\000\001\000\013\000\002\000\012\000\000\000\
\\057\000\000\000\
\\058\000\000\000\
\\059\000\000\000\
\\060\000\000\000\
\\061\000\000\000\
\\062\000\001\000\018\000\002\000\017\000\003\000\016\000\008\000\034\000\
\\010\000\033\000\012\000\032\000\000\000\
\\062\000\001\000\018\000\002\000\017\000\003\000\016\000\008\000\034\000\
\\010\000\033\000\012\000\032\000\016\000\039\000\017\000\038\000\
\\018\000\037\000\000\000\
\\063\000\000\000\
\\064\000\000\000\
\\065\000\000\000\
\\066\000\000\000\
\\067\000\000\000\
\\068\000\000\000\
\\069\000\000\000\
\\070\000\000\000\
\\071\000\004\000\008\000\005\000\007\000\006\000\006\000\000\000\
\\072\000\000\000\
\\073\000\000\000\
\\074\000\000\000\
\\075\000\000\000\
\\076\000\007\000\042\000\015\000\041\000\000\000\
\\077\000\000\000\
\\078\000\001\000\018\000\002\000\017\000\003\000\016\000\000\000\
\\079\000\000\000\
\\080\000\000\000\
\\081\000\000\000\
\\082\000\000\000\
\"
val actionRowNumbers =
"\000\000\031\000\031\000\001\000\
\\002\000\002\000\002\000\032\000\
\\015\000\014\000\006\000\007\000\
\\038\000\008\000\042\000\041\000\
\\040\000\009\000\010\000\016\000\
\\021\000\021\000\039\000\035\000\
\\034\000\033\000\024\000\022\000\
\\019\000\036\000\021\000\021\000\
\\021\000\036\000\023\000\026\000\
\\025\000\027\000\011\000\021\000\
\\002\000\005\000\004\000\003\000\
\\012\000\018\000\020\000\037\000\
\\030\000\029\000\028\000\017\000\
\\013\000"
val gotoT =
"\
\\001\000\052\000\000\000\
\\007\000\003\000\008\000\002\000\000\000\
\\007\000\007\000\008\000\002\000\000\000\
\\002\000\009\000\003\000\008\000\000\000\
\\010\000\013\000\011\000\012\000\000\000\
\\010\000\017\000\011\000\012\000\000\000\
\\010\000\018\000\011\000\012\000\000\000\
\\000\000\
\\002\000\019\000\003\000\008\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\010\000\022\000\011\000\012\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\029\000\005\000\028\000\006\000\027\000\011\000\026\000\000\000\
\\004\000\033\000\005\000\028\000\006\000\027\000\011\000\026\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\005\000\034\000\006\000\027\000\011\000\026\000\000\000\
\\000\000\
\\009\000\038\000\000\000\
\\004\000\041\000\005\000\028\000\006\000\027\000\011\000\026\000\000\000\
\\004\000\042\000\005\000\028\000\006\000\027\000\011\000\026\000\000\000\
\\004\000\043\000\005\000\028\000\006\000\027\000\011\000\026\000\000\000\
\\009\000\044\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\004\000\046\000\005\000\028\000\006\000\027\000\011\000\026\000\000\000\
\\011\000\047\000\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\\000\000\
\"
val numstates = 53
val numrules = 28
val s = ref "" and index = ref 0
val string_to_int = fn () => 
let val i = !index
in index := i+2; Char.ord(String.sub(!s,i)) + Char.ord(String.sub(!s,i+1)) * 256
end
val string_to_list = fn s' =>
    let val len = String.size s'
        fun f () =
           if !index < len then string_to_int() :: f()
           else nil
   in index := 0; s := s'; f ()
   end
val string_to_pairlist = fn (conv_key,conv_entry) =>
     let fun f () =
         case string_to_int()
         of 0 => EMPTY
          | n => PAIR(conv_key (n-1),conv_entry (string_to_int()),f())
     in f
     end
val string_to_pairlist_default = fn (conv_key,conv_entry) =>
    let val conv_row = string_to_pairlist(conv_key,conv_entry)
    in fn () =>
       let val default = conv_entry(string_to_int())
           val row = conv_row()
       in (row,default)
       end
   end
val string_to_table = fn (convert_row,s') =>
    let val len = String.size s'
        fun f ()=
           if !index < len then convert_row() :: f()
           else nil
     in (s := s'; index := 0; f ())
     end
local
  val memo = Array.array(numstates+numrules,ERROR)
  val _ =let fun g i=(Array.update(memo,i,REDUCE(i-numstates)); g(i+1))
       fun f i =
            if i=numstates then g i
            else (Array.update(memo,i,SHIFT (STATE i)); f (i+1))
          in f 0 handle Subscript => ()
          end
in
val entry_to_action = fn 0 => ACCEPT | 1 => ERROR | j => Array.sub(memo,(j-2))
end
val gotoT=Array.fromList(string_to_table(string_to_pairlist(NT,STATE),gotoT))
val actionRows=string_to_table(string_to_pairlist_default(T,entry_to_action),actionRows)
val actionRowNumbers = string_to_list actionRowNumbers
val actionT = let val actionRowLookUp=
let val a=Array.fromList(actionRows) in fn i=>Array.sub(a,i) end
in Array.fromList(map actionRowLookUp actionRowNumbers)
end
in LrTable.mkLrTable {actions=actionT,gotos=gotoT,numRules=numrules,
numStates=numstates,initialState=STATE 0}
end
end
local open Header in
type pos = word
type arg = int -> unit
structure MlyValue = 
struct
datatype svalue = VOID | ntVOID of unit | LID of  (string) | TID of  (string) | ID of  (string) | symbol of  (symbol) | symbol_list of  (symbol list) | precsymb_opt of  (symbol option) | precassoc_rule of  (precassoc_rule) | precassoc_rules of  (precassoc_rule list) | atomic_regexp of  (regular_expression) | sequence_regexp of  (regular_expression list) | choice_regexp of  (regular_expression) | production of  (production) | production_list of  (production list) | grammar of  (grammar)
end
type svalue = MlyValue.svalue
type result = grammar
end
structure EC=
struct
open LrTable
infix 5 $$
fun x $$ y = y::x
val is_keyword =
fn _ => false
val preferred_change : (term list * term list) list = 
nil
val noShift = 
fn (T 19) => true | _ => false
val showTerminal =
fn (T 0) => "ID"
  | (T 1) => "TID"
  | (T 2) => "LID"
  | (T 3) => "NON_ASSOC"
  | (T 4) => "LEFT_ASSOC"
  | (T 5) => "RIGHT_ASSOC"
  | (T 6) => "PREC"
  | (T 7) => "LPAREN"
  | (T 8) => "RPAREN"
  | (T 9) => "LBRACK"
  | (T 10) => "RBRACK"
  | (T 11) => "LBRACE"
  | (T 12) => "RBRACE"
  | (T 13) => "EQUALS"
  | (T 14) => "VBAR"
  | (T 15) => "ASTERISK"
  | (T 16) => "PLUS"
  | (T 17) => "QUESTION"
  | (T 18) => "END_PRODUCTION"
  | (T 19) => "EOF"
  | _ => "bogus-term"
local open Header in
val errtermvalue=
fn _ => MlyValue.VOID
end
val terms : term list = nil
 $$ (T 19) $$ (T 18) $$ (T 17) $$ (T 16) $$ (T 15) $$ (T 14) $$ (T 13) $$ (T 12) $$ (T 11) $$ (T 10) $$ (T 9) $$ (T 8) $$ (T 7) $$ (T 6) $$ (T 5) $$ (T 4) $$ (T 3)end
structure Actions =
struct 
exception mlyAction of int
local open Header in
val actions = 
fn (i392,defaultPos,stack,
    (rule):arg) =>
case (i392,stack)
of  ( 0, ( ( _, ( MlyValue.production_list production_list, _, production_list1right)) :: ( _, ( MlyValue.precassoc_rules precassoc_rules, _, _)) :: ( _, ( _, ID1left, _)) :: rest671)) => let val  result = MlyValue.grammar ((*#line 62.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(00); GRAMMAR {precassoc_rules=precassoc_rules, production_list=production_list}(*#line 255.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 0, ( result, ID1left, production_list1right), rest671)
end
|  ( 1, ( ( _, ( MlyValue.production production, production1left, production1right)) :: rest671)) => let val  result = MlyValue.production_list ((*#line 66.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(01); [production](*#line 259.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 1, ( result, production1left, production1right), rest671)
end
|  ( 2, ( ( _, ( MlyValue.production_list production_list, _, production_list1right)) :: ( _, ( MlyValue.production production, production1left, _)) :: rest671)) => let val  result = MlyValue.production_list ((*#line 68.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(02); production :: production_list(*#line 263.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 1, ( result, production1left, production_list1right), rest671)
end
|  ( 3, ( ( _, ( _, _, END_PRODUCTION1right)) :: ( _, ( MlyValue.precsymb_opt precsymb_opt, _, _)) :: ( _, ( MlyValue.choice_regexp choice_regexp, _, _)) :: _ :: ( _, ( MlyValue.ID ID, ID1left, ID1right)) :: rest671)) => let val  result = MlyValue.production ((*#line 72.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(03); {name=ID, filepos={left=ID1left, right=ID1right}, regex=choice_regexp, precsymb_opt=precsymb_opt}(*#line 267.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 2, ( result, ID1left, END_PRODUCTION1right), rest671)
end
|  ( 4, ( ( _, ( _, _, END_PRODUCTION1right)) :: ( _, ( MlyValue.precsymb_opt precsymb_opt, _, _)) :: ( _, ( MlyValue.choice_regexp choice_regexp, _, _)) :: _ :: ( _, ( MlyValue.TID TID, TID1left, TID1right)) :: rest671)) => let val  result = MlyValue.production ((*#line 74.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(03); {name=TID, filepos={left=TID1left, right=TID1right}, regex=choice_regexp, precsymb_opt=precsymb_opt}(*#line 271.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 2, ( result, TID1left, END_PRODUCTION1right), rest671)
end
|  ( 5, ( ( _, ( MlyValue.sequence_regexp sequence_regexp, sequence_regexp1left, sequence_regexp1right)) :: rest671)) => let val  result = MlyValue.choice_regexp ((*#line 78.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(04); SEQUENCE sequence_regexp(*#line 275.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, sequence_regexp1left, sequence_regexp1right), rest671)
end
|  ( 6, ( ( _, ( MlyValue.choice_regexp choice_regexp2, _, choice_regexp2right)) :: _ :: ( _, ( MlyValue.choice_regexp choice_regexp1, choice_regexp1left, _)) :: rest671)) => let val  result = MlyValue.choice_regexp ((*#line 80.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(05); CHOICE(choice_regexp1, choice_regexp2)(*#line 279.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 3, ( result, choice_regexp1left, choice_regexp2right), rest671)
end
|  ( 7, ( rest671)) => let val  result = MlyValue.sequence_regexp ((*#line 84.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(06); nil(*#line 283.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, defaultPos, defaultPos), rest671)
end
|  ( 8, ( ( _, ( MlyValue.sequence_regexp sequence_regexp, _, sequence_regexp1right)) :: ( _, ( MlyValue.atomic_regexp atomic_regexp, atomic_regexp1left, _)) :: rest671)) => let val  result = MlyValue.sequence_regexp ((*#line 86.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(07); atomic_regexp :: sequence_regexp(*#line 287.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 4, ( result, atomic_regexp1left, sequence_regexp1right), rest671)
end
|  ( 9, ( ( _, ( MlyValue.symbol symbol, symbol1left, symbol1right)) :: rest671)) => let val  result = MlyValue.atomic_regexp ((*#line 90.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(08); SYMBOL symbol(*#line 291.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, symbol1left, symbol1right), rest671)
end
|  ( 10, ( ( _, ( _, _, PLUS1right)) :: ( _, ( MlyValue.atomic_regexp atomic_regexp, atomic_regexp1left, _)) :: rest671)) => let val  result = MlyValue.atomic_regexp ((*#line 92.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(09); REPETITION atomic_regexp(*#line 295.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, atomic_regexp1left, PLUS1right), rest671)
end
|  ( 11, ( ( _, ( _, _, QUESTION1right)) :: ( _, ( MlyValue.atomic_regexp atomic_regexp, atomic_regexp1left, _)) :: rest671)) => let val  result = MlyValue.atomic_regexp ((*#line 94.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(10); CHOICE(SEQUENCE[], atomic_regexp)(*#line 299.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, atomic_regexp1left, QUESTION1right), rest671)
end
|  ( 12, ( ( _, ( _, _, ASTERISK1right)) :: ( _, ( MlyValue.atomic_regexp atomic_regexp, atomic_regexp1left, _)) :: rest671)) => let val  result = MlyValue.atomic_regexp ((*#line 96.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(11); CHOICE(SEQUENCE[], REPETITION atomic_regexp)(*#line 303.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, atomic_regexp1left, ASTERISK1right), rest671)
end
|  ( 13, ( ( _, ( _, _, RPAREN1right)) :: ( _, ( MlyValue.choice_regexp choice_regexp, _, _)) :: ( _, ( _, LPAREN1left, _)) :: rest671)) => let val  result = MlyValue.atomic_regexp ((*#line 98.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(12); choice_regexp(*#line 307.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, LPAREN1left, RPAREN1right), rest671)
end
|  ( 14, ( ( _, ( _, _, RBRACK1right)) :: ( _, ( MlyValue.choice_regexp choice_regexp, _, _)) :: ( _, ( _, LBRACK1left, _)) :: rest671)) => let val  result = MlyValue.atomic_regexp ((*#line 100.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(13); CHOICE(SEQUENCE[], choice_regexp)(*#line 311.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, LBRACK1left, RBRACK1right), rest671)
end
|  ( 15, ( ( _, ( _, _, RBRACE1right)) :: ( _, ( MlyValue.choice_regexp choice_regexp, _, _)) :: ( _, ( _, LBRACE1left, _)) :: rest671)) => let val  result = MlyValue.atomic_regexp ((*#line 102.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(14); CHOICE(SEQUENCE[], REPETITION choice_regexp)(*#line 315.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 5, ( result, LBRACE1left, RBRACE1right), rest671)
end
|  ( 16, ( rest671)) => let val  result = MlyValue.precassoc_rules ((*#line 106.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(15); nil(*#line 319.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 6, ( result, defaultPos, defaultPos), rest671)
end
|  ( 17, ( ( _, ( MlyValue.precassoc_rules precassoc_rules, _, precassoc_rules1right)) :: ( _, ( MlyValue.precassoc_rule precassoc_rule, precassoc_rule1left, _)) :: rest671)) => let val  result = MlyValue.precassoc_rules ((*#line 108.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(16); precassoc_rule :: precassoc_rules(*#line 323.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 6, ( result, precassoc_rule1left, precassoc_rules1right), rest671)
end
|  ( 18, ( ( _, ( _, _, END_PRODUCTION1right)) :: ( _, ( MlyValue.symbol_list symbol_list, _, _)) :: ( _, ( _, NON_ASSOC1left, _)) :: rest671)) => let val  result = MlyValue.precassoc_rule ((*#line 112.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(17); NON_ASSOCIATIVE symbol_list(*#line 327.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, NON_ASSOC1left, END_PRODUCTION1right), rest671)
end
|  ( 19, ( ( _, ( _, _, END_PRODUCTION1right)) :: ( _, ( MlyValue.symbol_list symbol_list, _, _)) :: ( _, ( _, LEFT_ASSOC1left, _)) :: rest671)) => let val  result = MlyValue.precassoc_rule ((*#line 114.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(18); LEFT_ASSOCIATIVE symbol_list(*#line 331.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, LEFT_ASSOC1left, END_PRODUCTION1right), rest671)
end
|  ( 20, ( ( _, ( _, _, END_PRODUCTION1right)) :: ( _, ( MlyValue.symbol_list symbol_list, _, _)) :: ( _, ( _, RIGHT_ASSOC1left, _)) :: rest671)) => let val  result = MlyValue.precassoc_rule ((*#line 116.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(19); RIGHT_ASSOCIATIVE symbol_list(*#line 335.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 7, ( result, RIGHT_ASSOC1left, END_PRODUCTION1right), rest671)
end
|  ( 21, ( rest671)) => let val  result = MlyValue.precsymb_opt ((*#line 120.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(20); NONE(*#line 339.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 8, ( result, defaultPos, defaultPos), rest671)
end
|  ( 22, ( ( _, ( MlyValue.symbol symbol, _, symbol1right)) :: ( _, ( _, PREC1left, _)) :: rest671)) => let val  result = MlyValue.precsymb_opt ((*#line 122.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(21); SOME symbol(*#line 343.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 8, ( result, PREC1left, symbol1right), rest671)
end
|  ( 23, ( ( _, ( MlyValue.symbol symbol, symbol1left, symbol1right)) :: rest671)) => let val  result = MlyValue.symbol_list ((*#line 126.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(22); [symbol](*#line 347.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 9, ( result, symbol1left, symbol1right), rest671)
end
|  ( 24, ( ( _, ( MlyValue.symbol_list symbol_list, _, symbol_list1right)) :: ( _, ( MlyValue.symbol symbol, symbol1left, _)) :: rest671)) => let val  result = MlyValue.symbol_list ((*#line 128.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(23); symbol :: symbol_list(*#line 351.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 9, ( result, symbol1left, symbol_list1right), rest671)
end
|  ( 25, ( ( _, ( MlyValue.ID ID, ID1left, ID1right)) :: rest671)) => let val  result = MlyValue.symbol ((*#line 132.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(24); {name=ID, delim_opt=NONE, filepos={left=ID1left, right=ID1right}}(*#line 355.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 10, ( result, ID1left, ID1right), rest671)
end
|  ( 26, ( ( _, ( MlyValue.TID TID, TID1left, TID1right)) :: rest671)) => let val  result = MlyValue.symbol ((*#line 134.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(25); {name=TID, delim_opt=SOME #"<", filepos={left=TID1left, right=TID1right}}(*#line 359.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 10, ( result, TID1left, TID1right), rest671)
end
|  ( 27, ( ( _, ( MlyValue.LID LID, LID1left, LID1right)) :: rest671)) => let val  result = MlyValue.symbol ((*#line 136.82 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm"*)rule(26); {name=LID, delim_opt=SOME #"'", filepos={left=LID1left, right=LID1right}}(*#line 363.1 "C:\Users\vwinter\UNO-Research\Project_Library_Migration\Domains\Monarch-Repository\TL_System\Engine\ParserGenerator\parser\ReadGrammar\grammar.grm.sml"*)
)
 in ( LrTable.NT 10, ( result, LID1left, LID1right), rest671)
end
| _ => raise (mlyAction i392)
end
val void = MlyValue.VOID
val extract = fn a => (fn MlyValue.grammar x => x
| _ => let exception ParseInternal
	in raise ParseInternal end) a 
end
end
structure Tokens : Grammar_TOKENS =
struct
type svalue = ParserData.svalue
type ('a,'b) token = ('a,'b) Token.token
fun ID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 0,(ParserData.MlyValue.ID i,p1,p2))
fun TID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 1,(ParserData.MlyValue.TID i,p1,p2))
fun LID (i,p1,p2) = Token.TOKEN (ParserData.LrTable.T 2,(ParserData.MlyValue.LID i,p1,p2))
fun NON_ASSOC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 3,(ParserData.MlyValue.VOID,p1,p2))
fun LEFT_ASSOC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 4,(ParserData.MlyValue.VOID,p1,p2))
fun RIGHT_ASSOC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 5,(ParserData.MlyValue.VOID,p1,p2))
fun PREC (p1,p2) = Token.TOKEN (ParserData.LrTable.T 6,(ParserData.MlyValue.VOID,p1,p2))
fun LPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 7,(ParserData.MlyValue.VOID,p1,p2))
fun RPAREN (p1,p2) = Token.TOKEN (ParserData.LrTable.T 8,(ParserData.MlyValue.VOID,p1,p2))
fun LBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 9,(ParserData.MlyValue.VOID,p1,p2))
fun RBRACK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 10,(ParserData.MlyValue.VOID,p1,p2))
fun LBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 11,(ParserData.MlyValue.VOID,p1,p2))
fun RBRACE (p1,p2) = Token.TOKEN (ParserData.LrTable.T 12,(ParserData.MlyValue.VOID,p1,p2))
fun EQUALS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 13,(ParserData.MlyValue.VOID,p1,p2))
fun VBAR (p1,p2) = Token.TOKEN (ParserData.LrTable.T 14,(ParserData.MlyValue.VOID,p1,p2))
fun ASTERISK (p1,p2) = Token.TOKEN (ParserData.LrTable.T 15,(ParserData.MlyValue.VOID,p1,p2))
fun PLUS (p1,p2) = Token.TOKEN (ParserData.LrTable.T 16,(ParserData.MlyValue.VOID,p1,p2))
fun QUESTION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 17,(ParserData.MlyValue.VOID,p1,p2))
fun END_PRODUCTION (p1,p2) = Token.TOKEN (ParserData.LrTable.T 18,(ParserData.MlyValue.VOID,p1,p2))
fun EOF (p1,p2) = Token.TOKEN (ParserData.LrTable.T 19,(ParserData.MlyValue.VOID,p1,p2))
end
end
