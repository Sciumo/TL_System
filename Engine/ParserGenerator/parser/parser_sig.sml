(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   filename      : parser_sig
   programmer    : Gary Fuehrer
   last modified : 7/25/2001

   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


(* ###################################################################### *)
(*                          PARSER                                        *)
(* ###################################################################### *)

signature PARSER =
  sig
    type grammar
    type parser
    type parse_result
    val readGrammar : TextIO.instream * {stream_name:string} -> grammar
    val makeParser : grammar -> parser
    val writeParser : BinIO.outstream * parser -> unit
    val readParser : BinIO.instream -> parser
    val parse : parser -> {start_symbol:string} -> (int -> string) -> parse_result
	
	val getGrammar : grammar -> Grammar_AbstractSyntax.grammar 
  end;

(* ###################################################################### *)
(*                        end PARSER                                      *)
(* ###################################################################### *)

(*
(* ###################################################################### *)
(*                          PARSER                                        *)
(* ###################################################################### *)

signature LR_PARSER =
  sig
    type grammar
    type parser
    type parse_result
    val readGrammar : TextIO.instream * {stream_name:string} -> grammar
    val makeParser : grammar -> parser
    val writeParser : BinIO.outstream * parser -> unit
    val parse : parser -> {start_symbol:string} -> (int -> string) -> parse_result
	
	val getGrammar : grammar -> Grammar_AbstractSyntax.grammar
  end;

(* ###################################################################### *)
(*                        end PARSER                                      *)
(* ###################################################################### *)
*)