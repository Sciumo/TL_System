structure UTIL = struct
structure A = ABSTRACT
structure C = CONCRETE_REPRESENTATION
open ENV
open ABSTRACT_REPRESENTATION

(* line-separator (carriage-return, line-feed); windows: "\r\n", *nix/mac: "\n" *)
val crlf = "\n"

fun println msg = print(msg ^ crlf)

(* Converts NODE_INFO to a string representation of the form: lineLow.columnLow-lineHigh.columnHigh *)
fun ninfoToString (C.info {id, line=(llo,lhi), column=(clo,chi), label=label_info})
      = label_info ^ ":" ^
        Int.toString llo ^ "." ^ Int.toString clo ^ "-" ^ Int.toString lhi ^ "." ^ Int.toString chi ^ " "

(* Gets the node info string from the given expression *)
fun ninfostring expr = ninfoToString (A.getExprInfo expr)

fun exprToString expr = A.leavesToString expr false

(* =====================================================================================================================
 * Auxiliary functions to raise type errors with pretty-printed error messages.
 * ================================================================================================================== *)
fun raiseOpEqError(ty1, ty2, expr)
    = raise TypeError(ninfostring expr ^
                      "Type error: types of operands don't agree:"  ^ crlf ^
                      "  left operand:  " ^ deepToString ty1 ^ crlf ^
                      "  right operand: " ^ deepToString ty2 ^ crlf ^
                      "  in expression: " ^ exprToString expr)

fun raiseTautologyError taut expr
    = raise TypeError(ninfostring expr ^
                      "Type error: expression always succeeds/fails, attempting to create/negate a tautology" ^ crlf ^
                      "  expression:    " ^ exprToString taut   ^ crlf ^
                      "  in expression: " ^ exprToString expr)

fun raiseOperandError expectedTy givenTy expr msg
    = raise TypeError(ninfostring expr ^
                      "Type error: " ^ msg ^ crlf ^
                      "  expected:      " ^ pp expectedTy ^ crlf ^
                      "  found:         " ^ pp givenTy    ^ crlf ^
                      "  in expression: " ^ exprToString expr)

fun raisePolyOpError(ty1, expr)
    = raise TypeError(ninfostring expr ^
                      "Type error: overloaded operator not defined for this type:" ^ crlf ^
                      "  type:          " ^ pp ty1 ^ crlf ^
                      "  in expression: " ^ exprToString expr)

fun raiseAppError s t expr msg
    = raise TypeError(ninfostring expr ^
                      "Type error: " ^ msg  ^ crlf ^
                      "  strategy:      " ^ pp s ^ crlf ^
                      "  term:          " ^ pp t ^ crlf ^
                      "  in expression: " ^ exprToString expr)

fun raiseCompositionError left right expr msg
    = raise TypeError(ninfostring expr ^
                      "Type error: " ^ msg ^ crlf ^
                      "  left operand:  " ^ pp left ^ crlf ^
                      "  right operand: " ^ pp right ^ crlf ^
                      "  in expression: " ^ exprToString expr)

fun raiseTypeError expr msg
    = raise TypeError(ninfostring expr ^
                      msg ^ crlf ^
                      "  in expression: " ^ exprToString expr)

(* ============================================================================================= *)
fun inferPrimType(a as TyTerm(s,[]))
    = if isSome(Bool.fromString s)
      then TyBool
      else if List.exists (fn c => c = hd (explode ".")) (String.explode s) andalso isSome(Real.fromString s)
           then TyReal
           else if isSome(Int.fromString s)
                then TyInt
                else if String.isPrefix "\"" s andalso String.substring(s,String.size(s)-1,1)="\""
                     then TyString
                     else a
  | inferPrimType ty1 = raise TypeError("UTIL.inferPrimType.match: " ^ pp ty1)

fun convertLeafsToPrims ty1
    = mapTy (fn (a as TyTerm(x,[])) => inferPrimType a
                | x => x) ty1

fun equalModPrims ty1 ty2 = convertLeafsToPrims ty1 = convertLeafsToPrims ty2

fun pickATree (p as TyTerm _, _            ) = p
  | pickATree ( _           , p as TyTerm _) = p
  | pickATree (ty1          , _            ) = ty1

fun skipNonBoolExpr (m as APP (ID   _,_,_) ) _ p = raiseTautologyError m p
  | skipNonBoolExpr (m as APP (SKIP _,_,_) ) _ p = raiseTautologyError m p
  | skipNonBoolExpr (     APP (_,     _,_) ) _ _ = TyBool
  | skipNonBoolExpr  _ actualTy                _ = actualTy

fun replaceLeaf tyChoices ty1
    = let
          fun match leafTy (x::xs) = if leafTy = x then x else match leafTy xs
            | match leafTy [] = raise TypeError("UTIL.replaceLeaf.match.match: " ^ pp leafTy ^ " []")
      in
          mapTy (fn (a as TyTerm(x,[])) => match (inferPrimType a) tyChoices
                    | x => x) ty1
      end

(* =====================================================================================================================
 * Auxiliary functions for folding abstract and concrete trees.
 * foldNode: (INODE * 'a) -> 'a -> (INODE * 'a) -> 'a *)
fun foldNode f (p as inode _     , z) = f(p, z)
  | foldNode f (p as imatch_var _, z) = f(p, z)

(* foldTerm: (INODE * 'a) -> 'a -> (ITREE * 'a) -> 'a *)
fun foldTerm f (itree (t, kids), z) = foldl (foldTerm f) (f(t,z)) kids

(* foldExpr: (EXPR * 'a) -> 'a -> (ITREE * 'a) -> 'a -> (EXPR * 'a) -> 'a *)
fun foldExpr f g (p as PROG         (es,_), z) = f(p, foldl (foldExpr f g) z es)
  | foldExpr f g (p as SIGNATURE    (e ,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as LIST         (es,_), z) = f(p, foldl (foldExpr f g) z es)

  | foldExpr f g (p as RECURSIVE(e1,es,e2,_), z) = f(p, foldExpr f g (e2, (foldl(foldExpr f g)(foldExpr f g (e1,z))es)))
  | foldExpr f g (p as NON_RECURSIVE(e1,e2,_),z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )

  | foldExpr f g (p as ITERATOR   (e,es,_), z) = f(p, foldl (foldExpr f g) (foldExpr f g (e,z)) es)
  | foldExpr f g (p as MAPL          (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as MAPR          (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as MAPB          (e,_), z) = f(p, foldExpr f g (e,z) )

  | foldExpr f g (p as FOLD_CHOICE   (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLD_LCHOICE  (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLD_RCHOICE  (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLD_LSEQ     (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLD_RSEQ     (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLD_LSTAR    (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLD_RSTAR    (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLDS_CHOICE  (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLDS_LCHOICE (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLDS_RCHOICE (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLDS_LSEQ    (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLDS_RSEQ    (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLDS_LSTAR   (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as FOLDS_RSTAR   (e,_), z) = f(p, foldExpr f g (e,z) )

  | foldExpr f g (p as CHOICE    (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as LCHOICE   (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as RCHOICE   (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as LSEQ      (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as RSEQ      (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as LSTAR     (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as RSTAR     (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )

  | foldExpr f g (p as TRANSIENT     (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as OPAQUE        (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as RAISE         (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as HIDE          (e,_), z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as LIFT          (e,_), z) = f(p, foldExpr f g (e,z) )

  | foldExpr f g (p as APP       (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )

  | foldExpr f g (p as RULE     (e1,e2  ,_),z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as COND_RULE(e1,e2,c,_),z) = f(p, foldExpr f g (e2, foldExpr f g (c, foldExpr f g (e1,z) ) ) )

  | foldExpr f g (p as MATCH     (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as BIND      (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as ANDALSO   (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as ORELSE    (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as NOT       (e    ,_), z) = f(p, foldExpr f g (e,z) )

  | foldExpr f g (p as LIBRARY_CALL_0 (e,_) , z) = f(p, foldExpr f g (e,z) )
  | foldExpr f g (p as LIBRARY_CALL (e,es,_), z) = f(p, foldl (foldExpr f g) (foldExpr f g (e,z)) es)

  | foldExpr f g (p as B_OR    (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as B_AND   (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as BANG    (e1   ,_), z) = f(p, foldExpr f g (e1,z) )
  | foldExpr f g (p as EQ      (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as NEQ     (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as LEQ     (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as LT      (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as GEQ     (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as GT      (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as CONCAT  (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as PLUS    (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as MINUS   (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as TIMES   (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as DIVIDE  (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as DIV     (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as MOD     (e1,e2,_), z) = f(p, foldExpr f g (e2, foldExpr f g (e1,z) ) )
  | foldExpr f g (p as TILDE   (e1   ,_), z) = f(p, foldExpr f g (e1,z) )

  | foldExpr f g (     TERM        (t,_), z) = g(t, z)
  | foldExpr f g (p as REF            _ , z) = f(p, z)
  | foldExpr f g (p as BOOL           _ , z) = f(p, z)
  | foldExpr f g (p as INT            _ , z) = f(p, z)
  | foldExpr f g (p as REAL           _ , z) = f(p, z)
  | foldExpr f g (p as STRING         _ , z) = f(p, z)
  | foldExpr f g (p as IDENTIFIER     _ , z) = f(p, z)
  | foldExpr f g (p as ID             _ , z) = f(p, z)
  | foldExpr f g (p as SKIP           _ , z) = f(p, z)
  | foldExpr f g (p as TRUE             , z) = f(p, z)
  | foldExpr f g (p as FALSE            , z) = f(p, z)
(* ================================================================================================================== *)

fun listToString lst = foldr (op ^) "" lst

(* For use in folding lists. *)
fun myOr (x,z) = z orelse x
fun myAnd(x,z) = z andalso x

(* flattenSums: ty list list -> ty list -> ty list list *)
fun flattenSums z (TySum(x,y)::xs)
      = let
            val choice1: ty list list = map (fn aList => x::aList) z
            val choice2: ty list list = map (fn aList => y::aList) z
            val deepChoice1: ty list list = foldr (op @) [] ((map (flattenSums [[]]) choice1): ty list list list)
            val deepChoice2: ty list list = foldr (op @) [] ((map (flattenSums [[]]) choice2): ty list list list)
        in
            flattenSums (deepChoice1@deepChoice2) xs
        end
  | flattenSums z (x::xs) = flattenSums (map (fn aList => x::aList) z) xs
  | flattenSums z []      = map (List.rev) z

(* Increments the specified ref value and returns the new value *)
fun incRef x = (x := !x + 1; !x)

(* Stores the TL program tree for proper re-orientation of match equations during type analysis. *)
val inputTree = ref (TERM (itree (inode("", C.default_info), []), C.dummy_node_info) )

(* Boolean constant defining the mode of the type-checker: in or out of regression testing.*)
val inTestingMode = ref false

(* Type-checking can be performed at varying levels of precision:
     0: no analysis is performed
     1: rewrite rules only
     2: level 1 and combinators
     3: level 2 and fold operators
     4: level 3 and one-layer iterators
     5: level 4 and full iterators *)
val precision = ref 3;

(* Verbosity level:
     0: OFF:     no logging
     1: ERROR:   log only error messages
     2: WARNING: level 1 and warnings
     3: INFO:    level 2 and info messages
     4: DEBUG:   level 3 and debug messages
     5: FINE:    level 4 and fine messages
     6: FINER:   level 5 and finer messages
     7: FINEST:  level 6 and finest messages
     8: ALL:     log all messages *)
val verbosity = ref 3
val indent = ref ""
fun incIndent() = indent := !indent ^ " "
fun decIndent() = indent := implode(tl(explode(!indent)))
fun decode flag msg = case flag of
                        0 => println(!indent ^ msg)
                      | 1 => (incIndent(); println(!indent ^ msg))
                      | 2 => (incIndent(); println(!indent ^ msg); decIndent())
                      | _ => (println(!indent ^ msg); decIndent())
fun error   msg flag = if !verbosity < 1 then () else decode flag msg
fun warning msg flag = if !verbosity < 2 then () else decode flag msg
fun info    msg flag = if !verbosity < 3 then () else decode flag msg
fun debug   msg flag = if !verbosity < 4 then () else decode flag msg
fun fine    msg flag = if !verbosity < 5 then () else decode flag msg
fun finer   msg flag = if !verbosity < 6 then () else decode flag msg
fun finest  msg flag = if !verbosity < 7 then () else decode flag msg
fun all     msg flag = if !verbosity < 8 then () else decode flag msg

type configuration = {precision: int, verbosity: int}

fun init prec verb
    = (inTestingMode := false; (* set to false to skip assertion-checking/regression-testing *)
       precision := prec;      (* precision levels of type-checking from 0 to 5 in the increasing order *)
       verbosity := verb)      (* verbosity of output from 0 to 6 in the increasing order *)
end