structure ENV = struct
structure S = IntBinaryMap (* smlnj-lib structure; for efficient mapping of int keys to types *)

datatype ty
  = TyBool | TyInt | TyReal | TyString (* for arithmetic operations *)
  | TyUnit                             (* for SML function calls *)
  | TyError
  | TyInf                              (* type of TL constructs unsupported at a given precision level *)

  | TyVar  of int
  | TySome of ty                       (* for type-inferencing terms with unknown structure: \exists ty1 \in [kids] *)
                                       (* used when target grammar contains Kleene closure ops: * and +. *)
  | TyTerm of string * ty list
  | TyRule of ty * ty
  | TySum  of ty * ty

  | TyList  of ty list                 (* used to accumulate dynamic rules *)

  | TyMap   of ty                      (* one-layer iterators *)
  | TyIter  of string * ty             (* pre-defined iterators *)
  | TyRec   of string * ty list * ty   (* recursive definitions *)

(* Applies the specified function f to the specified argument in a bottom-up manner.
 * mapTy: (ty -> ty) -> ty -> ty *)
fun mapTy f (TyTerm (st1,ts)    ) = f (TyTerm (st1, map (mapTy f) ts))
  | mapTy f (TyRule (ty1,ty2)   ) = f (TyRule (mapTy f ty1, mapTy f ty2))
  | mapTy f (TySum  (ty1,ty2)   ) = f (TySum  (mapTy f ty1, mapTy f ty2))
  | mapTy f (TyList ts          ) = f (TyList (map (mapTy f) ts))
  | mapTy f (TyMap  ty1         ) = f (TyMap  (mapTy f ty1))
  | mapTy f (TyIter (st1,ty1)   ) = f (TyIter (st1, mapTy f ty1))
  | mapTy f (TyRec  (st1,ts,ty1)) = f (TyRec  (st1, map (mapTy f) ts, mapTy f ty1))
  | mapTy f (TySome ty1         ) = f (TySome (mapTy f ty1))
  | mapTy f anyOther              = f anyOther

(* Applies the specified function f to the specified argument in a top-down manner.
 * mapTyTD: (ty -> ty) -> ty -> ty *)
fun mapTyTD f tyT = case f tyT of
                      TyTerm(t,ts)       => TyTerm (t, map (mapTyTD f) ts)
                    | TySome ty1         => TySome (mapTyTD f ty1)
                    | TyRule(ty1,ty2)    => TyRule (mapTyTD f ty1, mapTyTD f ty2)
                    | TySum (ty1,ty2)    => TySum  (mapTyTD f ty1, mapTyTD f ty2)
                    | TyList ts          => TyList (map (mapTyTD f) ts)
                    | TyMap  ty1         => TyMap  (mapTyTD f ty1)
                    | TyIter(st1,ty1)    => TyIter (st1, mapTyTD f ty1)
                    | TyRec (st1,ts,ty1) => TyRec  (st1, map (mapTyTD f) ts, mapTyTD f ty1)
                    | anyOther           => anyOther

(* Folds the specified argument using the specified function f.
 * foldTy: (ty * 'a) -> 'a  -> (ty * 'a) -> 'a *)
fun foldTy f (p as TyTerm ( _ ,ts    ), z) = f(p, foldl (foldTy f) z ts)
  | foldTy f (p as TyRule (ty1,ty2   ), z) = f(p, foldTy f (ty2, foldTy f (ty1, z)))
  | foldTy f (p as TySum  (ty1,ty2   ), z) = f(p, foldTy f (ty2, foldTy f (ty1, z)))
  | foldTy f (p as TyList ts          , z) = f(p, foldl (foldTy f) z ts)
  | foldTy f (p as TyMap  ty1         , z) = f(p, foldTy f (ty1, z))
  | foldTy f (p as TyIter ( _ ,ty1   ), z) = f(p, foldTy f (ty1, z))
  | foldTy f (p as TyRec  ( _ ,ts,ty1), z) = f(p, foldTy f (ty1, foldl (foldTy f) z ts))
  | foldTy f (p as TySome ty1         , z) = f(p, foldTy f (ty1, z))
  | foldTy f (anyOther                , z) = f(anyOther, z)


(*--------------------------------------------------------------------------------------------------------------------*)
type context = ty S.map (* typing context: efficient map of integer keys to types *)

exception TypeError of string;
exception SymbolExn

val initialEnv: context = S.empty

val nextSym = ref 0

(* hashes strings and maps hashed values to nat numbers *)
val hashtable: (string, int) HashTable.hash_table = HashTable.mkTable(HashString.hashString, op =) (128, SymbolExn)


(* Looks up a symbol for a given name or creates a new symbol if none exists.
 * symbol: string -> (string, int) *)
fun symbol name = case HashTable.find hashtable name of
                    SOME i => (name, i)
                  | NONE   => let
                                  val i = !nextSym
                              in
                                  nextSym := i + 1;
                                  HashTable.insert hashtable (name, i);
                                  (name, i)
                              end

fun enter   (table, id: string, ty1: ty) = S.insert  (table, #2(symbol id), ty1)
fun look    (table, id: string)          = S.find    (table, #2(symbol id))
fun inDomain(table, id: string)          = S.inDomain(table, #2(symbol id))


(*--------------------------------------------------------------------------------------------------------------------*)
fun nextVar() = let
                    val i = !nextSym
                in
                    nextSym := i + 1;
                    TyVar i
                end


(* Propagates the bindings from the typing context into the argument type.
 * applySubst: context -> ty -> ty *)
fun applySubst env tyIn
    = let
          (*val _ = fine("applySubst.input: " ^ toString tyIn) 1*)
          val tyOut = mapTyTD (fn (p as TyVar x) => (case S.find(env,x) of
                                                       SOME ty1 => ty1
                                                     | NONE     => p)
                                | (p as TyTerm(r,[TyVar x])) => (case S.find(env,x) of
                                                                   SOME (TyTerm y) => TyTerm y
                                                                 | SOME baseTy => TyTerm(r,[baseTy])
                                                                 | NONE     => p)
                                | anyOther  => anyOther
                              )
                              tyIn
          (*val _ = fine("applySubst.output: " ^ toString tyOut) ~1*)
      in
          tyOut
      end 

(* Converts a nat number into a (multi-)character string; for pretty-printing type variables.
 * chr(65)=#"A", ord(#"A")=65, chr(90)=#"Z"
 * chr(97)=#"a", ord(#"a")=97, chr(122)=#"z"
 * myChr: int -> string -> string *)
fun myChr n acc =      if n > 122 then myChr (n - 123) (acc ^ "a")
                  else if n >= 97 then acc ^ str (chr n)
                  else myChr (n + 97) acc

(* Aux values to shorten the identifiers of type variables for readability. *)
val offset = ref 0;
fun getMinVarIndex tyExpr = foldTy (fn (TyVar x, min) => Int.min(x,min)
                                     | ( _     , min) => min
                                   )
                                   (tyExpr, valOf(Int.maxInt))


(*--------------------------------------------------------------------------------------------------------------------*)
fun toString  TyBool            = "bool"
  | toString  TyInt             = "int"
  | toString  TyReal            = "real"
  | toString  TyString          = "string"
  | toString  TyUnit            = "unit"
  | toString  TyError           = "type error"
  | toString  TyInf             = "unsupported"
  | toString (TyVar x)          = "'" ^ myChr (x - (!offset + 97)) ""

  | toString (TyTerm (st1,tys)) = let
                                      fun getLeaf (TyTerm (t,[]))        = t ^ " " (* terminal string *)
                                        | getLeaf (TyTerm (t,[TyVar x])) = t ^ "[ " ^ toString (TyVar x) ^ " ] "
                                        | getLeaf (TyTerm (_,xs))        = foldr (op ^) "" (map getLeaf xs)
                                        | getLeaf  anyOther              = toString anyOther ^ " "
                                  in
                                      st1 ^ "[ " ^ (foldr (op ^) "" (map getLeaf tys)) ^ "]"
                                  end

  | toString (TyRule (a,b)        ) = toString a ^ " -> " ^ toString b
  | toString (TySum  (a,b)        ) = "(" ^ toString a ^ " + "  ^ toString b ^ ")"
  | toString (TyList ts           ) = "[ " ^ (foldr (fn (x,"" ) => x
                                                      | (x,acc) => x ^ " , " ^ acc) "" (map toString ts)) ^ " ]"

  | toString (TyMap  ty1          ) = "map " ^ toString ty1
  | toString (TyIter (st1,ty1)    ) = st1 ^ " " ^ toString ty1

  | toString (TyRec  (st1,[] ,ty1)) = toString ty1
  | toString (TyRec  (st1,tys,ty1)) = st1 ^ " (" ^ (foldl (fn (x,xs) => if xs = "" then x
                                                                        else x ^ "," ^ xs)
                                                          ""
                                                          (map toString tys))
                                          ^ ") -> " ^ toString ty1
  | toString (TySome ty1          ) = "exists( " ^ toString ty1 ^ " )"

fun deepToString (TyTerm (st1,tys)) = st1 ^ "[ " ^ (foldr (op ^) "" (map deepToString tys)) ^ "]"
  | deepToString (TySome ty1)       = "exists( " ^ deepToString ty1 ^ " )"
  | deepToString (TyRule (ty1,ty2)) = deepToString ty1 ^ " -> " ^ deepToString ty2
  | deepToString (TySum  (ty1,ty2)) = "(" ^ deepToString ty1 ^ " + "  ^ deepToString ty2 ^ ")"
  | deepToString (TyMap  ty1      ) = "map " ^ deepToString ty1
  | deepToString (TyIter (st1,ty1)) = st1 ^ " " ^ deepToString ty1
  | deepToString  anyOther          = toString anyOther

fun pp x = toString x

fun envToString (env: context)
      = let
            val nameKeyPairs: (string * int) list = HashTable.listItemsi hashtable
            val keyTypePairs: (int * ty) list  = S.listItemsi env
            fun lookupName key ((name, i)::rest) = if key = i then name else lookupName key rest
              | lookupName key []                = "'" ^ myChr key ""
        in
            "Type Assertions: \n" ^
            foldl (fn ((key1,ty1),s)
                     => let
                            val name = lookupName key1 nameKeyPairs
                            val _ = offset := getMinVarIndex ty1
                        in
                            if String.isPrefix "assert_" name (* skip type assertions *)
                            then s
                            else if String.isPrefix "'" name (* skip type variable bindings *)
                                 then s
                                 else s ^ "  " ^ name ^ ": " ^ toString ty1 ^ "\n"
                        end
                  )
                  ""
                  (keyTypePairs)
        end
end
