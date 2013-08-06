structure GRAMMAR = struct
structure S = IntBinaryMap
structure G = Grammar_AbstractSyntax
open UNIFICATION

(* Map of non-terminal symbols to productions. *)
val tgtGrammar = ref (S.empty: (G.regular_expression) S.map)

(*--------------------------------------------------------------------------------------------------------------------*)
(* symbolToString: symbol -> string *)
fun symbolToString {name, delim_opt, filepos} = name

(* regexToString: regular_expression -> string *)
fun regexToString (G.SYMBOL x)     = symbolToString x ^ " "
  | regexToString (G.SEQUENCE xs)  = foldr (op ^) "" (map regexToString xs)
  | regexToString (G.CHOICE (x,y)) = "{" ^ regexToString x ^ " | " ^ regexToString y ^ "}"
  | regexToString (G.REPETITION x) = "repetition(" ^ (regexToString x) ^ ")"

(* productionToString: production -> string *)
fun productionToString {name, regex, filepos, precsymb_opt} = name ^ " ::= " ^ (regexToString regex) ^ crlf

(* grammarToString: grammar -> string *)
fun grammarToString (G.GRAMMAR {precassoc_rules, production_list})
      = print (foldr (op ^) "" (map productionToString production_list))

(* tableToString: (G.regular_expression) S.map -> string *)
fun tableToString table
      = let
            val nameIdPairs : (string * int) list = HashTable.listItemsi hashtable
            val keyRegexPairs: (int * G.regular_expression) list = S.listItemsi table
            fun lookupName key ((name, i)::rest) = if key = i then name else lookupName key rest
              | lookupName key []                = Int.toString key
        in
            "Grammar:" ^ crlf ^
            foldl
              (fn ((key1,regex1),s) => s ^ "  " ^ (lookupName key1 nameIdPairs) ^ ": " ^ regexToString regex1 ^ crlf)
              ""
              (keyRegexPairs)
        end

(* normalizes and simplifies regular expressions *)
fun norm (G.SYMBOL x    ) = G.SYMBOL x
  | norm (G.CHOICE (x,y)) = G.CHOICE (norm x, norm y)
  | norm (G.REPETITION x) = G.REPETITION (norm x)
  | norm (G.SEQUENCE [] ) = G.SEQUENCE []
  | norm (G.SEQUENCE [x]) = norm x (* a single regex is not a sequence *)
  | norm (G.SEQUENCE xs )
    = let
          val xs1 = map norm xs
          fun delistify [q] = q
            | delistify qs  = G.SEQUENCE qs
          fun aux acc ((G.CHOICE (x,y))::zs) = let (* a (x|y) b => axb | ayb *)
                                                   fun listify (G.SEQUENCE []) = []
                                                     | listify (G.SEQUENCE bs) = bs
                                                     | listify anyOther        = [anyOther]
                                                   val rest1 = aux (acc@listify x) zs
                                                   val rest2 = aux (acc@listify y) zs
                                               in
                                                   [G.CHOICE (delistify rest1, delistify rest2)]
                                               end
            | aux acc (z::zs) = aux (acc@[z]) zs
            | aux acc []      = acc
      in
          delistify (aux [] xs1)
      end

(* Collects multiple productions with the same head symbol into a single production and stores them in the map.
 * crop: production list -> regex map -> regex map *)
fun crop ({name,regex,filepos,precsymb_opt}::xs) table
      = let
            val key = #2(symbol name)
        in
            if S.inDomain(table, key)
            then crop xs (S.insert(table, key, G.CHOICE (valOf(S.find(table, key)), norm regex)))
            else crop xs (S.insert(table, key, norm regex))
        end
  | crop [] table = table

(*--------------------------------------------------------------------------------------------------------------------*)
(* Checks if the specified term string exists in the specified regular expression.
 * existsString: string -> regex -> bool *)
fun existsString "'term" _          = true
  | existsString t (G.SYMBOL x)     = symbolToString x = t
  | existsString t (G.CHOICE (x,y)) = existsString t x orelse existsString t y
  | existsString t (G.REPETITION x) = existsString t x
  | existsString t (G.SEQUENCE xs)  = foldl myOr false (map (existsString t) xs)

(* Checks structural integrity of a term type with respect to the target grammar.
 * isParseable: ty -> bool *)
fun isParseable (TyTerm(_,[]        )) = true (* terminal symbols *)
  | isParseable (TyTerm(_,[TyVar _ ])) = true (* unknown structure *)
  | isParseable (TyTerm(_,[TyBool  ])) = true (* structure with a boolean leaf *)
  | isParseable (TyTerm(_,[TyInt   ])) = true
  | isParseable (TyTerm(_,[TyReal  ])) = true
  | isParseable (TyTerm(_,[TyString])) = true
  | isParseable (TyTerm(root,kids))
    = if not (inDomain(!tgtGrammar, root))
      then true (* lexer symbols outside the grammar: e.g. ident, integer_value etc. *)
      else 
        if List.exists (fn TyVar _ => true | _ => false ) kids
        then true
        else let
               val regex1 = valOf( look(!tgtGrammar, root) )
               val kidRoots = foldr (fn (TyTerm (st1,_), s) => st1 ^ " " ^ s
                                      | (anyOther      , s) => toString anyOther ^ " " ^ s) "" kids
               fun exists i pattern (G.CHOICE (x,y)) = exists i pattern x orelse exists i pattern y
                 | exists i pattern (g as (G.REPETITION x))
                     = let
                         val tokens = String.tokens (fn #" " => true | _ => false) pattern
                         val prefixTokens = if i <= List.length tokens 
                                            then List.take(tokens,i)
                                            else []
                         val prefix = foldr (fn (w,ws) => w ^ " " ^ ws) "" prefixTokens
                       in
                         prefixTokens <> [] andalso (exists i prefix x orelse exists (i+1) pattern g)
                       end
                 | exists _ pattern anyOther = regexToString anyOther = pattern
               val flag = exists 1 kidRoots regex1
             in
               flag andalso foldl myAnd true (map isParseable kids)
             end
  | isParseable (TySum(x,y)          ) = isParseable x andalso isParseable y
  | isParseable anyOtherTy = false

(* Checks if a string symbol t can be derived from non-terminal "root".
 * isDerivable: string -> string ->  *)
fun isDerivable t root acc
      = let (* rule's terms have been parsed so we can assume they have valid structure *)
          fun exists sym (G.CHOICE (x,y)) = exists sym x orelse exists sym y
            | exists sym (G.REPETITION x) = exists sym x
            | exists sym (G.SEQUENCE xs)  = foldr myOr false (map (exists sym) xs)
            | exists sym (G.SYMBOL x)
                = let
                    val xString = symbolToString x
                  in
                    xString = sym orelse
                      (xString <> root (* to avoid infinite descent *)
                       andalso (* called 'isDerivable' on this symbol already? *)
                       not (List.exists (fn x => x = xString) acc)
                       andalso isDerivable sym (xString) (root::acc)
                      )
                  end
        in
          t = root orelse
            (inDomain(!tgtGrammar, root) andalso exists t (valOf(look(!tgtGrammar, root))) )
        end

(*--------------------------------------------------------------------------------------------------------------------*)
(* Checks if the first term is a subtype of the second: i.e. term1 is more specific than term2.
 * subtype: ty -> ty -> bool *)
fun subtype _ (TyVar _) = true
  | subtype (TyTerm (x,xs)) (TyTerm (y,ys)) = (x = y orelse y = "'term") andalso subtypeL xs ys
  | subtype (TyRule (a,b)) (TyRule (c,d)) = subtype c a andalso subtype b d
  | subtype (TySome x) (TySome y) = subtype x y
  | subtype a b = if a = b then true else false

(* subtypeL: ty list -> ty list -> bool *)
and subtypeL [] [] = true
  | subtypeL [] _  = false
  | subtypeL _  [] = false
  | subtypeL (x::xs) (y::ys) = subtype x y andalso subtypeL xs ys

(* Converts a given term to a more generic term. A type variable is more generic than a concrete term.
 * generify: ty -> ty *)
fun generify (TyBool)   = TyBool
  | generify (TyInt)    = TyInt
  | generify (TyReal)   = TyReal
  | generify (TyString) = TyString
  | generify (TyUnit)   = TyUnit
  | generify (TyError)  = TyError
  | generify (TyInf)    = TyInf
  | generify (TyVar x)  = TyVar x
  | generify (TySome x) = TySome (generify x)
  | generify (TyTerm(x,xs))
      = let
            val xs2 = generifyL xs
        in
            if xs = xs2 then nextVar()
            else TyTerm(x,xs2)
        end
  | generify (TyRule(TyVar x,b)) = TyRule(TyVar x, generify b)
  | generify (TyRule(a,b))       = TyRule(generify a, b)
  | generify (TySum (TyVar x,b)) = TySum(TyVar x, generify b)
  | generify (TySum (a,b))       = TySum(generify a, b)
  | generify t = raise TypeError("GRAMMAR.generify.match: " ^ pp t)

(* generifyL: ty list -> ty list *)
and generifyL [] = []
  | generifyL (x::xs)
      = let
            val x2 = generify x
        in
            if x = x2 then x::(generifyL xs)
            else x2::xs
        end

(* Computes the lowest upper bound of two types.
 * join: ty -> ty -> ty *)
fun join a b
    = if subtype a b then b
      else if subtype b a then a
      else let
               val a2 = generify a
               val _ = finer("join.fst: " ^ pp a2) 2
           in
               if pp a = pp a2
               then let
                        val b2 = generify b
                        val _ = finer("join.snd: " ^ pp b2) 2
                    in
                        join a b2
                    end
               else join a2 b
           end

(* Computes intersection of two contexts; if a key that is present in both contexts is mapped to
 * two distinct types, then the key is mapped to a join of the two types (lowest upper bound) in the result.
 * intersect: (context * context) -> context *)
fun intersect (env1,env2)
    = let
          val joins = ref []
          (* map tyVars in the old type to corresponding elements in the new type *)
          fun getNewBindings oldTy newTy
              = let
                    val _ = finer("getNewBindings. input: " ^ toString oldTy ^ " | " ^ toString newTy) 1
                    val collectVars = foldTy (fn (TyVar x, acc) => (TyVar x)::acc
                                               | (_,acc) => acc)
                    val varsInOldTy = collectVars (oldTy, [])
                    val ctx1 = unify(oldTy, [newTy], initialEnv, !inputTree)
                    val ctx2 = S.filter (fn ty1 => List.exists (fn x => x = ty1) varsInOldTy) ctx1
                    val _ = finer("intersect.lub.output: ok") ~1
                in
                    S.listItemsi ctx2
                end
          fun lub i a b
              = let
                    val _ = fine("intersect.lub. input: " ^ pp (TyVar i) ^ " | " ^ pp a ^ " | " ^ pp b) 1
                    val joinTy = join a b
                    val _ = joins := (getNewBindings a joinTy)@(getNewBindings b joinTy)
                    val _ = fine("intersect.lub.output: " ^ toString joinTy) ~1
                in
                    joinTy
                end
          val env3 = S.intersectWithi
                      (fn (i, x, y) => if x = y then x else lub i x y)
                      (*(fn (TyVar x, TyVar y) => if x = y then TyVar x else nextVar()
                        | (x,y) => if x = y then x else nextVar()) (*TySum(x,y))*)*)
                      (env1, env2)
          fun update e ((key,ty1)::rest) = update (S.insert(e, key, ty1)) rest
            | update e [] = e
      in
          update env3 (!joins)
      end

end