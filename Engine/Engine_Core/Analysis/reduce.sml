structure REDUCE = struct
open GRAMMAR

(* =====================================================================================================================
 * Observation: if there are no primitive types in a rule's premise p, then the rule is guaranteed to succeed if
 * premise p and term t are type-unifiable and
 *   a. p has a type variable in it, or
 *   b. p has no type variables (is precise) and t is also precise
 * In such applications, there is no need to track failure term. *)
fun isPrim TyBool   = true
  | isPrim TyInt    = true
  | isPrim TyReal   = true
  | isPrim TyString = true
  | isPrim _        = false

fun isVar (TyVar _) = true
  | isVar  _        = false

fun hasPrimPremise (t as TyTerm _ ) = foldTy (fn (ty1,acc) => acc orelse isPrim ty1) (t,false)
  | hasPrimPremise (TyRule (lhs,_)) = foldTy (fn (ty1,acc) => acc orelse isPrim ty1) (lhs,false)
  | hasPrimPremise (TySum  (a,b)  ) = hasPrimPremise a orelse hasPrimPremise b
  | hasPrimPremise TyInf = false
  | hasPrimPremise arg = raise TypeError("REDUCE.hasPrimPremise.match: " ^ pp arg)

fun hasVarPremise  (t as TyTerm _ ) = foldTy (fn (ty1,acc) => acc orelse isVar ty1) (t,false)
  | hasVarPremise  (TyRule (lhs,_)) = foldTy (fn (ty1,acc) => acc orelse isVar ty1) (lhs,false)
  | hasVarPremise  (TySum  (a,b)  ) = hasVarPremise a orelse hasVarPremise b
  | hasVarPremise  TyInf = false
  | hasVarPremise  arg = raise TypeError("REDUCE.hasVarPremise.match: " ^ pp arg)

fun isPrecise ty1 = not (hasPrimPremise ty1) andalso not (hasVarPremise ty1)

(* Checks if strategy s is guaranteed to apply to term t *)
fun willApply s t = hasVarPremise s orelse hasVarPremise t orelse (isPrecise s andalso isPrecise t)
(* ================================================================================================================== *)

(* Computes the order of a type expression.
 * getOrder: ty -> int *)
fun getOrder (TyRule (_,TyVar _)) = 1
  | getOrder (TyRule (_,nonVar )) = 1 + getOrder nonVar
  | getOrder (TySum  (t1,t2)) = Int.min(getOrder t1, getOrder t2)
  | getOrder (TyList  ts)     = foldl (fn (a,acc)=> if getOrder a < acc then getOrder a else acc) (valOf(Int.maxInt)) ts
  | getOrder (TyMap  ty1    ) = getOrder ty1
  | getOrder (TyIter (_,ty1)) = getOrder ty1
  | getOrder (TyVar   _     ) = ~1
  | getOrder _                = 0

(* Compares the order of two strategies and raises an error if the orders are not equal.
 * checkOrder: ty * ty -> expr -> unit *)
fun checkOrder (TyInf       , _          ) _ = () (* ignore unsupported constructs *)
  | checkOrder ( _          , TyInf      ) _ = ()
  | checkOrder (a as TyError, b          ) p = raiseCompositionError a b p "left operand contains a type error"
  | checkOrder (a           ,b as TyError) p = raiseCompositionError a b p "right operand contains a type error"
  | checkOrder (TyVar  _    , _          ) _ = ()
  | checkOrder ( _          , TyVar _    ) _ = ()
  | checkOrder (TyRule (_,b), TyRule(_,d)) p = checkOrder(b,d) p
  | checkOrder (a           , TySum (b,c)) p = (checkOrder(a,b) p; checkOrder(a,c) p)
  | checkOrder (TySum  (a,b), c          ) p = (checkOrder(a,c) p; checkOrder(b,c) p)
  | checkOrder (ty1,ty2) p
      = let
            val ord1 = getOrder ty1
            val ord2 = getOrder ty2
        in
            if ord1 = ~1 orelse ord2 = ~1
            then ()
            else if ord1 = ord2
                 then ()
                 else raiseCompositionError ty1 ty2 p "the order of operands must be the same; use foldS otherwise"
        end

(* Removes the failure term (either the original input term or SKIP) to reduce the number of possible outcomes.
 * stripFailTerm: ty -> ty *)
fun stripFailTerm (     TySum (rhs, TyRule (TyVar _, TyVar _) )) = rhs (* omit SKIPs *)
  | stripFailTerm (p as TySum (_,   TyRule  _ )) = p
  | stripFailTerm (p as TySum (_,   TySum   _ )) = p
  | stripFailTerm (     TySum (rhs, failTerm  )) = rhs
  | stripFailTerm anyTy                          = anyTy

(* =====================================================================================================================
 * Computes the type of applying a strategy to a term.
 * reduce: (ty * ty * ctx) -> EXPR -> ty *)
fun reduce(TyInf, _, e) _ = (TyInf, e)
  | reduce(r as TyRule (_, TyList _), t, _) p
    = raiseAppError r t p "applying a higher-order rule without fold or foldS"

  | reduce(s as TyVar _, t, e) p (* applying a strategy of unknown type; perform type-inferencing *)
    = let
          val _ = debug("reduce.tyvar.input: " ^ pp s ^ " | " ^ pp t) 1
          val s2 = TyRule(nextVar(), nextVar())
          val (tyF, e2) = reduce(s2, t, e) p
          val eF = if !precision = 1
                   then e2
                   else unify(s, [applySubst e2 s2], e2, p)
          val _ = debug("reduce.tyvar.inferred: " ^ pp (applySubst eF s)) 0
          val _ = debug("reduce.tyvar.output: result is " ^ pp tyF) ~1
      in
          (tyF, eF)
      end

  | reduce(r as TyRule (lhs as TyTerm (_,[TySome _]), rhs as TyTerm (_,[TySome _])), t as TyTerm(_,[TyVar z]), e) p
    = let
          val _ = debug("reduce.rule.some.abstract.input: " ^ pp r ^ " | " ^ pp t) 1
          val eF = unify (t, [lhs], e, p)
          val tyF = applySubst eF rhs
          val _ = debug("reduce.rule.some.abstract.output: " ^ pp tyF) ~1
      in
          (tyF, eF)
      end
  | reduce(r as TyRule (lhs as TyTerm (_,[TySome a]), rhs as TyTerm (_,[TySome b])), t as TyTerm(root,kids), e) p
    = let
          val _ = debug("reduce.rule.some.concrete.input: " ^ pp r ^ " | " ^ pp t) 1
          val eF = unify (t, [lhs], e, p)
          val rhs2 = applySubst eF rhs
          val r2 = TyRule(applySubst eF a, applySubst eF b)
          fun mapReduce acc (x::xs)
              = let
                    val (x2,_) = reduce(r2, x, eF) p handle TypeError _ => (x,eF)
                in
                    mapReduce (x2::acc) xs
                end
            | mapReduce acc [] = List.rev acc
          val newKids = mapReduce [] kids
          val newTerms = map (fn aList => TyTerm(root, aList)) (flattenSums [[]] newKids)
          val validTerms = List.filter isParseable newTerms
          val _ = if List.length validTerms = 0
                  then raiseAppError r2 t p "application cannot produce a term with valid structure"
                  else ()
          val tyF = foldl (fn (term,acc) => TySum(acc,term)) (hd validTerms) (tl validTerms)
          val _ = debug("reduce.rule.some.concrete.output: " ^ pp tyF) ~1
      in
          (tyF, eF)
      end
  | reduce(r as TyRule (lhs,rhs), t, e) p
    = let
          val _ = debug("reduce.rule.input: " ^ pp r ^ " | " ^ pp t) 1
          val e2 = unify (t, [lhs], e, p)
          val rhs2 = applySubst e2 rhs
          val (tyF, eF)
                = case getOrder rhs of
                    0 => if willApply r t
                         then (rhs2, e2)
                         else if rhs2 = t
                              then (rhs2, e2)
                              else (TySum (rhs2,t), e2)
                  | _ => (rhs2, e2) (* for optimization, do not include SKIPs *)
          val _ = debug("reduce.rule.output: " ^ pp tyF) ~1
      in
          (tyF, eF)
      end
  | reduce(s as TySum (a,b), t, e) p
    = let (* skip rules with incompatible types *)
          val (illTyped1, (rhs1, e1)) = (false, reduce (a,t,e) p) handle TypeError _ => (true, (t, e))
          val (illTyped2, (rhs2, e2)) = (false, reduce (b,t,e) p) handle TypeError _ => (true, (t, e))
          val e12 = intersect (e1,e2)
          val isHetero = #1( (false, checkOrder (rhs1,rhs2) p) handle TypeError _ => (true, ()) )
      in
          if illTyped1 andalso illTyped2 then raiseAppError s t p "unexpected arguments in strategy application"
          else if illTyped1 then (rhs2, e2)
          else if illTyped2 then (rhs1, e1)
          else if isHetero then (TySum (rhs1, rhs2), e12)
          else if willApply a t orelse willApply b t (* 1 rule is guaranteed to succeed *)
               then (TySum (rhs1, rhs2), e12) (* leave results as they are *)
               else (TySum(TySum (stripFailTerm rhs1, stripFailTerm rhs2), t), e12) (* turn two fail-terms into 1 *)
      end

  (*** MAP ***)
  | reduce(TyMap _, t as TyTerm(_,[]), e) _ = (t,e) (* base case: no immediate subterms *)
  | reduce(TyMap(r as TyRule(_,TyRule _)), TyTerm(_,[one]), e) p = reduce(r, one, e) p
  | reduce(s as TyMap(TyRule(_,TyRule _)), t as TyTerm _, _) p  (* higher-order rule, multiple kids *)
      = raiseAppError s t p "generated/dynamic strategies need to be composed using fold or foldS"
  | reduce(s as TyMap(r as TyRule(a, b)), t as TyTerm(root,[TyVar z]), e) p
      = let
          val _ = debug("reduce.tymap-tyrule-tyvar. input: " ^ pp s ^ " | " ^ pp t) 1
          val _ = case root of
                    "'term" => () (* do not check generic nodes *)
                  | _ => let val regexOption = look(!tgtGrammar, root)
                         in  if not (isSome regexOption)
                             then raiseTypeError p ("Node " ^ root ^ " does not have rewritable children")
                             else case a of
                                    TyTerm(aRoot,_) =>
                                      if not (existsString aRoot (valOf regexOption))
                                      then raiseAppError s t p "there are no suitable subterms for mapX to apply to"
                                      else (case b of 
                                             TyTerm(bRoot,_) =>
                                               if not (existsString bRoot (valOf regexOption))
                                               then raiseAppError s t p "application cannot produce a term with valid structure"
                                               else ()
                                           | _ => ())
                                  | _ => ()
                         end
          val tyIn   = TyTerm(root,[TySome a])
          val tyOut  = if hasPrimPremise a
                       then TySum(TyTerm(root,[TySome b]), tyIn)
                       else TyTerm(root,[TySome b])
          val eF = unify(TyVar z, [tyIn], e, p)
          val _ = debug("reduce.tymap-tyrule-tyvar.output: " ^ pp tyOut) ~1
        in
          (tyOut, eF)
        end
  | reduce(s as TyMap(r as TyRule _), t as TyTerm(root,kids), e) p
    = let
          val _ = debug("reduce.tymap-tyrule-kids. input: " ^ pp s ^ " | " ^ pp t) 1
          val mapAppCounter = ref 0
          fun mapReduce acc e (x::xs)
              = let val (applied,(x2,e2)) = (true, reduce(r,x,e) p) handle TypeError _ => (false, (x,e))
                in  if   applied
                    then (incRef mapAppCounter; mapReduce (x2::acc) e2 xs)
                    else mapReduce (x::acc) e xs
                end
            | mapReduce acc e [] = (List.rev acc, e)
          val (newKids, eF) = mapReduce [] e kids
          val _ = if (!mapAppCounter = 0)
                  then raiseAppError s t p "there are no suitable subterms to apply to"
                  else ()
          val newTerms = map (fn aList => TyTerm(root,aList)) (flattenSums [[]] newKids)
          val validTerms = List.filter isParseable newTerms
          val _ = if List.length validTerms = 0
                  then raiseAppError s t p "application cannot produce a term with valid structure"
                  else ()
          val tyF = foldl (fn (term,acc) => TySum(acc,term)) (hd validTerms) (tl validTerms)
          val _ = debug("reduce.tymap-tyrule-kids.output: " ^ pp tyF) ~1
      in
          (tyF, eF)
      end
  | reduce(s as TyMap(TySum(a,b)), t, e) p
    = let
          val _ = debug("reduce.tymap-tysum. input: " ^ pp s ^ " | " ^ pp t) 1
          val (illTyped1, (t1, e1)) = (false, reduce(TyMap a, t, e) p) handle TypeError _ => (true, (t, e))
          val (illTyped2, (t2, e2)) = (false, reduce(TyMap b, t, e) p) handle TypeError _ => (true, (t, e))
          val (tyF, eF) = if illTyped1 andalso illTyped2 then raiseAppError s t p "unexpected arguments in strategy application"
                          else if illTyped1 then (t2, e2)
                          else if illTyped2 then (t1, e1)
                          else (TySum (t1, t2), intersect (e1, e2))
          val _ = debug("reduce.tymap-tysum.output: " ^ pp tyF) ~1
      in
          (tyF, eF)
      end

  (*** ITERATOR ***)
  | reduce(s as TyIter ("FIX", r as TyRule(TyTerm(lhs,_),TyTerm(rhs,_))), t, e) p
    = if lhs = rhs
      then reduce(r, t, e) p
      else raiseAppError s t p "the type of FIX must be (T->T)->T (e.g. (expr->expr)->expr)"
  | reduce(TyIter (_, TyRule(TyVar _, TyVar _)), t as TyTerm _, e) _ = (t,e) (* ID/SKIP *)
  | reduce(TyIter (F, TyIter("FIX", s2)), t, e) p = reduce(TyIter(F,s2), t, e) p (* e.g. TDL (FIX r) t *)
  | reduce(s as TyIter (_, r as TyRule(lhs as TyTerm(x,_),rhs as TyTerm(y,_))), t, e) p
    = let
        val appCounter = ref 1
        fun trav (term as TyTerm(root,[TyVar _])) ctx (* argument term (tyT) structure is unknown *)
            = let
                (*val (unified, ctx2) = (true, unify(term,[lhs],ctx,p)) handle TypeError _ => (false,ctx)
                val (term1, ctx3) = if unified
                                    then (appCounter := !appCounter + 1; (applySubst ctx2 rhs, ctx2))
                                    else (term, ctx2)*)
              in
                (*if unified orelse (isDerivable x root [] andalso isDerivable y root [])
                then (appCounter := !appCounter + 1; (term1,ctx3))
                else raise TypeError(ninfostring p ^
                        "Type error: lhs or rhs of the rule don't exist in argument term's structure" ^ crlf ^
                        "  iterator:      " ^ toString s ^ crlf ^
                        "  rewrite rule:  " ^ toString r    ^ crlf ^
                        "  local term:    " ^ toString term ^ crlf ^
                        "  argument term: " ^ toString t    ^ crlf ^
                        "  in expression: " ^ exprToString p)*)
                (TyTerm(root,[nextVar()]), ctx)
              end
          | trav (term as TyTerm(root,kids)) ctx
            = let
                fun aux e acc (k::ks)
                    = let
                        val (k2,e2) = trav k e (* bottom-up *)
                        (*val _ = if isParseable (TyTerm (root,List.rev(k2::acc)@ks))
                                then ()
                                else appCounter := !appCounter - 1*)
                      in
                        aux e2 (k2::acc) ks
                      end
                  | aux e acc [] = (List.rev acc, e)
                val (kids2, ctx2) = aux ctx [] kids
                (*val (unified, ctx3) = (true, unify(term,[lhs],ctx2,p)) handle TypeError _ => (false,ctx2)*)
              in
                (*if unified
                then (appCounter := !appCounter + 1; (applySubst ctx3 rhs, ctx3))
                else*) (TyTerm(root,kids2), ctx2)
              end
          | trav term ctx = (term,ctx)
        val (newTerm, e2) = trav t e
      in
        if (!appCounter > 0)
        then (newTerm, e2)
        else raiseAppError s t p "iterator cannot successfully modify any subterm of the argument term"
      end

  | reduce(TyIter(F,TySum(a,b)), t, e) p
    = let
          val (ty1,_) = reduce(TyIter(F,a), t, e) p
          val (ty2,_) = reduce(TyIter(F,b), t, e) p
      in
          (TySum(ty1,ty2),e)
      end

  | reduce(s as TyIter (F, r as TyRule(lhs as TyTerm(x,_),rhs)), t, e) p
    = let
        val appCounter = ref 1
        fun trav (term as TyTerm(root,[TyVar _])) ctx (* argument term's structure is unknown *)
            = let
                val (unified, ctx2) = (true, unify(term,[lhs],ctx,p)) handle TypeError _ => (false,ctx)
                val (rules, ctx3) = if unified
                                    then ([applySubst ctx2 rhs], ctx2)
                                    else ([TyRule(nextVar(), nextVar())], ctx2)
              in
                (*if unified orelse isDerivable x root []
                then (appCounter := !appCounter + 1; (rules,ctx3))
                else raise TypeError(ninfostring p ^
                        "Type error: lhs of the higher-order rule does not exist in the argument term's "^
                        "structure" ^ crlf ^
                        "  iterator:      " ^ pp s ^ crlf ^
                        "  rewrite rule:  " ^ pp r ^ crlf ^
                        "  argument term: " ^ pp t ^ crlf ^
                        "  in expression: " ^ exprToString p)*)
                (rules, ctx3)
              end
          | trav (term as TyTerm(_,kids)) ctx
            = let
                fun aux e acc (k::ks)
                    = let
                        val (s1,e1) = trav k e
                      in
                        aux e1 (s1@acc) ks
                      end
                  | aux e acc [] = (List.rev acc, e)
                val (rules, ctx2) = aux ctx [] kids
                val (unified, ctx3) = (true, unify(term,[lhs],ctx2,p)) handle TypeError _ => (false,ctx2)
                val rules2 = if unified
                             then (appCounter := !appCounter + 1; ((applySubst ctx3 rhs)::rules))
                             else rules
              in
                (rules2,ctx3)
              end
          | trav _ ctx = ([],ctx)
        val (strats,e2) = trav t e
        (*fun comp(x,y) = #1(case F of
                         "lcond_tdl"    => createComp "<+" x y env2 p
                       | "lcond_tdr"    => createComp "<+" x y env2 p
                       | "lcond_bul"    => createComp "<+" x y env2 p
                       | "lcond_bur"    => createComp "<+" x y env2 p
                       | "rcond_tdl"    => createComp "+>" x y env2 p
                       | "rcond_tdr"    => createComp "+>" x y env2 p
                       | "rcond_bul"    => createComp "+>" x y env2 p
                       | "rcond_bur"    => createComp "+>" x y env2 p
                       |  "lseq_tdl"    => createComp "<;" x y env2 p
                       |  "lseq_tdr"    => createComp "<;" x y env2 p
                       |  "lseq_bul"    => createComp "<;" x y env2 p
                       |  "lseq_bur"    => createComp "<;" x y env2 p
                       |  "rseq_tdl"    => createComp ";>" x y env2 p
                       |  "rseq_tdr"    => createComp ";>" x y env2 p
                       |  "rseq_bul"    => createComp ";>" x y env2 p
                       |  "rseq_bur"    => createComp ";>" x y env2 p
                       | "lconjunct_tdl"=> createComp "<*" x y env2 p
                       | "lstar_tdr"    => createComp "<*" x y env2 p
                       | "lstar_bul"    => createComp "<*" x y env2 p
                       | "lstar_bur"    => createComp "<*" x y env2 p
                       | "rconjunct_tdl"=> createComp "*>" x y env2 p
                       | "rstar_tdr"    => createComp "*>" x y env2 p
                       | "rstar_bul"    => createComp "*>" x y env2 p
                       | _              => createComp "*>" x y env2 p)
                       *)
      in
        if (!appCounter > 0)
        then (*(foldl comp (hd strats) (tl strats),env2)*)
             (TyRule(nextVar(), nextVar()),e2)
        else raiseAppError s t p "iterator cannot successfully generate any new dynamic rules"
      end

  (*** Custom traversals ***)
  | reduce(TyRec (_, [], body), t, e) p = reduce(body,t,e) p (* custom traversal: 1 arg *)
  | reduce(TyRec (F, x::xs, body), t, e) p
    = let
        val (unified, e2) = (true, unify(t,[x],e,p)) handle TypeError _ => (false, e)
      in
        if unified then (TyRec (F, xs, applySubst e2 body),e2)
        else raiseOperandError x t p "unexpected argument in recursive iterator application"
      end

  | reduce(s, t, _) p = raiseAppError s t p "REDUCE.reduce.match"

end