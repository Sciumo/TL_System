structure COMPOSITION = struct
open REDUCE

(* ==================================================================================================================
 * Alpha-renames a type expression: creates a new context with fresh bindings and propagates it.
 * alphaRename: ty -> ty
 * ================================================================================================================== *)
fun alphaRename ty1
      = applySubst (foldTy (fn (TyVar x, e) => solve [(TyVar x, nextVar())] e
                             | (_,       e) => e
                           )
                           (ty1,initialEnv)
                   )
                   ty1

(* ==================================================================================================================
 * Converts type expressions into normal forms.
 * normalize: ctx -> ty -> ty
 * ================================================================================================================== *)
fun (* if choices on the lhs and the rhs are the same, pick one choice for both lhs and rhs *)
    (*normalize _ (r as TyRule(TyTerm(t1,[z1 as TySum(a,b)]), TyTerm(t2,[z2 as TySum _])))
      = if t1 = t2 andalso z1 = z2
        then TyRule(TyTerm(t1,[a]), TyTerm(t2,[a]))
        else r*)

    (* map each choice on the lhs of a rule to the corresponding choice on the rhs *)
  (*| normalize e (TyRule(lhs as TyTerm(t,[TySum(a,b)]), TySum(x,y)))
      = let
          val x1 = normalize e (TyRule (TyTerm(t,[a]),x))
          val y1 = normalize e (TyRule (TyTerm(t,[b]),y))
        in
          TySum(x1,y1)
        end*)

    (* flatten rules by lifting sums from a rule's rhs to the outside of the rule:
     *   e.g. a -> (x + y) => (a -> x) + (a -> y) *)
    normalize e (r as TyRule(a as TyTerm _, TySum(b,c)))
      = let
          val ab = normalize e (TyRule (a,b))
          val ac = normalize e (alphaRename (TyRule (a,c)))
          val tyF = (* if ac is an ID, then skip it, because ab is already a rule (ID is built into rules) *)
                    case ac of
                      TyRule(x,y) => if x = y then ab else TySum(ab,ac)
                    | _ => TySum(ab,ac)
        in
          tyF
        end
  (*| normalize e (TyRule(lhs as TyTerm _, TyTerm(t2,[TySum(x,y)])) )
      = let
          val x1 = normalize e (TyRule (lhs, TyTerm(t2,[x])) )
          val y1 = normalize e (alphaRename (TyRule (lhs, TyTerm(t2,[y]))))
        in
          TySum(x1,y1)
        end*)
  | normalize _ (r as TyRule(TyTerm _,_)) = r
  | normalize _ r = raise TypeError("COMPOSITION.normalize.match: " ^ toString r)

(* ==================================================================================================================
 * Checking conjunctive and sequential combinators:
 * checkStar: (ty * ty) -> context -> expr -> (ty * context)
 * checkSeq:  (ty * ty) -> context -> expr -> (ty * context)
 * ================================================================================================================== *)
val isFoldS = ref false;

fun (* first-order composition: is well-typed if output of the 1st rule is type-unifiable with the premise of the 2nd *)
    checkStar (TyRule(a,b as TyTerm _), r2 as TyRule(c,d as TyTerm _)) e p
      = let
            val e2 = unify (b, [c], e, p) (* on success, b and c are type-unifiable *)
            val ad = TyRule(applySubst e2 a, applySubst e2 d)
        in
            (ad, e2)
        end

    (* heterogeneous composition: first-order rule is on the left *)
  | checkStar (TyRule(a,b as TyTerm _), TyRule(c,d)) e p
      = let
            val e2 = unify (b, [c], e, p)
        in
            (TyRule(applySubst e2 a, TySum (applySubst e2 b,applySubst e2 d)), e2)
            (* first- and higher-order results are combined with TySum *)
        end
    (* heterogeneous composition: first-order rule is on the right *)
  | checkStar (TyRule(a,b), TyRule(c,d as TyTerm _)) e p
      = let
            val e2 = unify (a, [c], e, p)
        in
            (TyRule(applySubst e2 a, TySum (applySubst e2 b,applySubst e2 d)), e2)
        end

    (* higher-order composition: is well-typed if premises of the rules are type-unifiable *)
  | checkStar (TyRule(a,b), TyRule(c,d)) e p
      = let
            val e2 = unify (a, [c], e, p)
            val rhs = case b of
                        TyRule _  => TyList [b,d]
                      | TyList bs => TyList (bs@[d])
                      | TyInf     => TyList [b,d]
                      | arg       => raise TypeError("COMPOSITION.checkStar.rule-rule.match: " ^ pp arg)
            val (a2, rhs2) = (applySubst e2 a, mapTy (applySubst e2) rhs)
            val combTy = TyRule (a2, rhs2)
        in
            if not (!isFoldS)
            then (combTy, e2)
            else (isFoldS := false; (TyRule (a2, TyList[rhs2,alphaRename combTy]), e2) )
        end

  (* one or both of the operands are choice-based compositions *)
  | checkStar (a as TyRule _ , bc as TySum(b,c)) e p     (* a(b+c)=>ab+ac *)
      = let
            val ((ab, e1), abOk) = (checkStar (a            , b) e p, true) handle TypeError _ => ((b,e), false)
            val ((ac, e2), acOk) = (checkStar (alphaRename a, c) e p, true) handle TypeError _ => ((c,e), false)
        in
            if abOk andalso acOk then (TySum(ab,ac), e)
            else if abOk then (ab, e1)
            else if acOk then (ac, e2)
            else raiseCompositionError a bc p "there does not exist a valid path through the composition"
        end
  | checkStar (ab as TySum(a,b), c as TyRule _ ) e p
      = let
            val ((ac, e1), acOk) = (checkStar (a, c            ) e p, true) handle TypeError _ => ((a,e), false)
            val ((bc, e2), bcOk) = (checkStar (b, alphaRename c) e p, true) handle TypeError _ => ((b,e), false)
        in
            if acOk andalso bcOk then (TySum(ac,bc), e)
            else if acOk then (ac, e1)
            else if bcOk then (bc, e2)
            else raiseCompositionError ab c p "there does not exist a valid path through the composition"
        end
  | checkStar (ab as TySum(a,b), cd as TySum(c,d)) e p         (* (a+b)(c+d)=>(ac+ad)+(bc+bd) *)
      = let
            val ((ac, e1), acOk) = (checkStar (a            , c            ) e p, 0) handle TypeError _ => ((a,e), 1)
            val ((ad, e2), adOk) = (checkStar (alphaRename a, d            ) e p, 0) handle TypeError _ => ((d,e), 1)
            val ((bc, e3), bcOk) = (checkStar (b            , alphaRename c) e p, 0) handle TypeError _ => ((b,e), 1)
            val ((bd, e4), bdOk) = (checkStar (alphaRename b, alphaRename d) e p, 0) handle TypeError _ => ((d,e), 1)
        in
            case (acOk, adOk, bcOk, bdOk) of
              (0,0,0,0) => (TySum(TySum(ac,ad), TySum(bc,bd)), e)
            | (0,0,0,1) => (TySum(TySum(ac,ad), bc), e)
            | (0,0,1,0) => (TySum(TySum(ac,ad), bd), e)
            | (0,0,1,1) => (TySum(ac,ad), e)
            | (0,1,0,0) => (TySum(ac, TySum(bc,bd)), e)
            | (0,1,0,1) => (TySum(ac, bc), e)
            | (0,1,1,0) => (TySum(ac, bd), e)
            | (0,1,1,1) => (ac, e1)
            | (1,0,0,0) => (TySum(ad, TySum(bc,bd)), e)
            | (1,0,0,1) => (TySum(ad, bc), e)
            | (1,0,1,0) => (TySum(ad, bd), e)
            | (1,0,1,1) => (ad, e2)
            | (1,1,0,0) => (TySum(bc,bd), e)
            | (1,1,0,1) => (bc, e3)
            | (1,1,1,0) => (bd, e4)
            | (1,1,1,1) => raiseCompositionError ab cd p "there does not exist a valid path through the composition"
            | (_,_,_,_) => raise TypeError ("COMPOSITION.checkStar.match.sum-sum.nonexhaustive")
        end

  (* composition with map iterators *)
  | checkStar (TyRule(a,b), m as TyMap _) e p
      = let
            val (ty2, e2) = reduce(m, b, e) p
        in
            (TyRule(a,ty2), e2)
        end
  | checkStar (m as TyMap _, r2 as TyRule(c as TyTerm(cRoot, cKids), d) ) e p
      = let
            val _ = debug ("checkStar: input: " ^ pp m ^ " | " ^ pp r2) 1
            (* since this is conjunction, incoming term's root must be the same as cRoot *)
            val a = TyTerm(cRoot, [nextVar()])
            val (b, e1) = reduce(m, a, e) p
            val a2 = applySubst e1 a
            val r1 = TyRule(a2, b)
            (* primitive types may produce identity rewrites; eliminate them since this is conjunctive composition *)
            val b2 = case b of
                       (TySum (x,y)) =>
                         if      a2 = x then y
                         else if a2 = y then x
                         else b
                     | _ => b
            (* check that the premise of r2 does not have terms applicable for the premise of r1 *)
            val _ = case a2 of
                      TyTerm(_,[TySome aKid]) =>
                        if List.exists (fn cKid => cKid = aKid) cKids
                        then raiseCompositionError r1 r2 p
                               "application of the first operand produces a term incompatible with the second" 
                        else ()
                    | _ => ()
            (* infer structure of the incoming term through inverse rewriting of c *)
            val a3 = TyTerm(cRoot,
                       map (fn cKid => case b2 of
                                         TyTerm(_,[TySome bKid]) =>
                                           if bKid = cKid (* found a match *)
                                           then case a2 of
                                                  (* replace existential quantifier by a concrete term *)
                                                  TyTerm(_,[TySome aKid]) => aKid
                                                | _ => cKid
                                           else cKid
                            | _ => cKid) cKids)
            (* if the right operand's structure's unknown, the left operand's structure should remain as before *)
            val a4 = case cKids of
                       [TyVar _] => a2
                     | _         => a3
            val eF = unify (b2, [c], e, p)
            val tyF = TyRule(applySubst eF a4, applySubst eF d)
            val _ = debug ("checkStar: output: " ^ pp tyF) ~1
        in
            (tyF, eF)
        end

  (* one of the operands is of unknown type: perform type-inferencing *)
  | checkStar (x as TyVar _, y as TyRule(a,_)) e p = (y, unify(x, [TyRule(a,a)], e, p))
  | checkStar (x as TyRule(_,a), y as TyVar _) e p = (x, unify(y, [TyRule(a,a)], e, p))
  | checkStar (a as TyVar _, TySum(b,c)) e p
      = let
            val (ab, e1) = checkStar (a,b) e p
            val (ac, e2) = checkStar (a,c) e p
        in
            (TySum(ab,ac), intersect(e1, e2))
        end
  | checkStar (TySum(a,b), c as TyVar _) e p
      = let
            val (ac, e1) = checkStar (a,c) e p
            val (bc, e2) = checkStar (b,c) e p
        in
            (TySum(ac,bc), intersect(e1, e2))
        end

  | checkStar (TyInf, _) e p = (TyInf, e)
  | checkStar (_, TyInf) e p = (TyInf, e)
  
  (* otherwise raise a type error *)
  | checkStar (ty1,ty2) _ p = raiseCompositionError ty1 ty2 p "unexpected operands in conjunctive composition"

(* ============================================================================================= *)
fun (* first-order composition *)
    checkSeq (r1 as TyRule(a,b as TyTerm _), r2 as TyRule(c,d as TyTerm _)) e p
      = let
            val _ = debug("checkSeq(first-order): " ^ pp r1 ^ " and " ^ pp r2) 1
            val (unifiable, e2) = (true, unify (c, [b], e, p)) handle TypeError _ => (false, e)
            val ad = TyRule(applySubst e2 a, applySubst e2 d)
            val (tyOut, envOut)
                   = if unifiable
                     then if hasVarPremise r2 orelse (isPrecise b andalso isPrecise c) (* r2 is guaranteed to apply *)
                          then if ad = r2
                               then (ad, e2)
                               else (TySum(ad, (*alphaRename*) r2), e2)
                          else (TySum(ad, TySum(alphaRename r1, (*alphaRename*) r2)), e2)
                     else (* log an info notice: the seq combinator can be replaced by a cond combinator *)
                          let
                              val isSubtypeBC = subtype b c
                              val isSubtypeCB = subtype c b
                              val isCondBetter
                                    = not unifiable (* output of the first rule is not compatible with the input of the second *)
                                      andalso not (isSubtypeBC orelse isSubtypeCB) (* both rules' premises are mutually-exclusive *)
                              (*val _ = if isCondBetter
                                        then info("Info: Sequential comp can be replaced by conditional comp" ^ crlf ^
                                                  "  left operand:  " ^ pp r1 ^ crlf ^
                                                  "  right operand: " ^ pp r2 ^ crlf ^
                                                  "  in expression: " ^ exprToString p ^ crlf)
                                        else ()*)
                          in
                              (TySum(r1, r2), e) (* todo: check if r2 is reachable *)
                          end
            val _ = debug("checkSeq result: " ^ pp tyOut) ~1
        in
            (tyOut, envOut)
        end

    (* heterogeneous composition: first-order rule is on the left *)
  | checkSeq (r1 as TyRule(a,b as TyTerm _), r2 as TyRule(c,d)) e p
      = let
            val (unifiable, e2) = (true, unify (c, [b], e, p)) handle TypeError _ => (false, e)
            val combTy = TyRule(a, TySum(applySubst e2 b,applySubst e2 d))
        in
            if unifiable
            then if hasVarPremise r2 orelse (isPrecise b andalso isPrecise c) (* r2 is guaranteed to apply *)
                 then (TySum(combTy, alphaRename r2), e2)
                 else (TySum(combTy, TySum(alphaRename r1, alphaRename r2)), e2)
            else (TySum(r1, r2), e)
        end
    (* heterogeneous composition: first-order rule is on the right *)
  | checkSeq (r1 as TyRule(a,b), r2 as TyRule(c,d as TyTerm _)) e p
      = let
            val (unifiable, e2) = (true, unify (c, [a], e, p)) handle TypeError _ => (false, e)
            val combTy = TyRule(applySubst e2 a, TySum(applySubst e2 b,applySubst e2 d))
            val r1Alpha = alphaRename r1
            val r2Alpha = alphaRename r2
        in
            if unifiable
            then if (isPrecise r1 andalso isPrecise r2) orelse
                    (hasVarPremise r1 andalso hasVarPremise r2) (* both rules are guaranteed to fire *)
                 then (combTy, e2)
                 else if hasVarPremise r1   (* r2 is prim or precise *)
                      then (TySum(r1Alpha, combTy), e)
                      else if hasVarPremise r2
                           then (TySum(combTy, r2Alpha), e)
                           else (TySum(combTy, TySum (r1Alpha, r2Alpha)), e)
            else (TySum (r1,r2), e)
        end

    (* higher-order composition *)
  | checkSeq (r1 as TyRule(a,b), r2 as TyRule(c,d)) e p
      = let
            val (unifiable, e2) = (true, unify (c, [a], e, p)) handle TypeError _ => (false, e)
            val rhs = case b of
                        TyRule _  => TyList [b,d]
                      | TyList bs => TyList (bs@[d])
                      | TyInf     => TyList [b,d]
                      | arg       => raise TypeError("COMPOSITION.checkSeq.hirule-hirule.match: " ^ pp arg)
            val (a2, rhs2) = (applySubst e2 a, mapTy (applySubst e2) rhs)
            val combTy = TyRule (a2, rhs2)
            val r1Alpha = alphaRename r1
            val r2Alpha = alphaRename r2

            val isHetero = !isFoldS
            val _ = isFoldS := false
            val combTyHetero = TyRule (a2, TyList[rhs2,alphaRename combTy])
            val r1Hetero = TyRule(a, TyList[b,r1Alpha])
            val r2Hetero = TyRule(c, TyList[d,r2Alpha])
        in
            if not isHetero
            then if unifiable
                 then if (isPrecise r1 andalso isPrecise r2) orelse
                         (hasVarPremise r1 andalso hasVarPremise r2) (* both rules are guaranteed to fire *)
                      then (combTy, e2)
                      else if hasVarPremise r1   (* r2 is prim or precise *)
                           then (TySum(r1Alpha, combTy), e)
                           else if hasVarPremise r2
                                then (TySum(combTy, r2Alpha), e)
                                else (TySum(combTy, TySum (r1Alpha, r2Alpha)), e)
                 else (TySum (r1,r2), e)
            else if unifiable
                 then if (isPrecise r1 andalso isPrecise r2) orelse
                         (hasVarPremise r1 andalso hasVarPremise r2) (* both rules are guaranteed to fire *)
                      then (combTyHetero, e2)
                      else if hasVarPremise r1   (* r2 is prim or precise *)
                           then (TySum(r1Hetero, combTyHetero), e)
                           else if hasVarPremise r2
                                then (TySum(combTyHetero, r2Hetero), e)
                                else (TySum(combTyHetero, TySum (r1Hetero, r2Hetero)), e)
                 else (TySum (r1Hetero,r2Hetero), e)
        end

  (* one or both of the operands are choice-based compositions; should unreachable paths be flagged as in checkStar? *)
  | checkSeq (a as TyRule _ , TySum(b,c)) e p      (* a(b+c)=>ab+ac *)
      = let
            val (ab, _) = checkSeq (a,b) e p
            val (ac, _) = checkSeq (alphaRename a,c) e p
            (* simplification: if a(b+c)=>(a+b)+(a+c), then a(b+c)=>a+(b+c) *)
            val f = case ab of
                      TySum(a1,b1) => a1 = a andalso b1 = b andalso
                                      (case #1(checkSeq (a,c) e p) of
                                              TySum(a2,c1)  => a2 = a andalso c1 = c
                                            | _ => false)
                    | _ => false
            val tyOut = if f then TySum(a,TySum(b,c)) else TySum(ab,ac) 
        in
            (tyOut, e)
        end
  | checkSeq (TySum(a,b), c as TyRule _ ) e p (* (a+b)c=>ac+bc *)
      = let
            val (ac, _) = checkSeq (a,c) e p
            val (bc, _) = checkSeq (b,alphaRename c) e p
            (* simplification: if (a+b)+c=>(a+c)+(b+c), then (a+b)c=>(a+b)+c *)
            val f = case ac of
                      TySum(a1,c1) => a1 = a andalso c1 = c andalso
                                      (case #1(checkSeq (b,c) e p) of
                                              TySum(b1,c2)  => b1 = b andalso c2 = c
                                            | _ => false)
                    | _ => false
            val tyOut = if f then TySum(TySum(a,b),c) else TySum(ac,bc) 
        in
            (tyOut, e)
        end
  | checkSeq (TySum(a,b), TySum(c,d)) e p          (* (a+b)(c+d)=(ac+ad)+(bc+bd) *)
      = let
            val (ac, _) = checkSeq (a,            c            ) e p
            val (ad, _) = checkSeq (alphaRename a,d            ) e p
            val (bc, _) = checkSeq (b,            alphaRename c) e p
            val (bd, _) = checkSeq (alphaRename b,alphaRename d) e p
        in
            (TySum(TySum(ac,ad), TySum(bc,bd)), e)
        end

  (* composition with map iterators *)
  | checkSeq (TyRule(a,b), m as TyMap s) e p
      = let
            val (ty2, _) = reduce(m, b, e) p
            val case1 = normalize e (TyRule(a,ty2))
            
            val c = TyTerm("'term",[nextVar()]) (* generic node with variable children *)
            fun reduceToList (s as TyMap(TySum(a,b))) t e p
              = let
                  val (illTyped1, rhs1) = (false, reduceToList (TyMap a) t e p) handle TypeError _ => (true, [(t, e)])
                  val (illTyped2, rhs2) = (false, reduceToList (TyMap b) t e p) handle TypeError _ => (true, [(t, e)])
                in
                  if illTyped1 andalso illTyped2 then raiseAppError s t p "unexpected arguments in strategy application"
                  else if illTyped1 then rhs2
                  else if illTyped2 then rhs1
                  else rhs1@rhs2
                end
              | reduceToList s t e p = [reduce(s,t,e) p]
            val tuples = reduceToList m c e p
            val cases = map (fn (d,ctx) => TyRule(applySubst ctx c, d) ) tuples
            val cases2 = map (normalize e) cases
            val case2 = foldl (fn (term,acc) => TySum(acc,term)) (hd cases2) (tl cases2)
        in
            (TySum(case1,case2), e)
        end
  | checkSeq (m as TyMap _, r2 as TyRule(c as TyTerm(lhs,lhsKids),d) ) e p
      = let
            val _ = debug ("checkSeq: analyzing " ^ pp m ^ " <; " ^ pp r2) 1
            (* case 1: only mapL applies *)
            val term1 = TyTerm("'term", [nextVar()])
            val (out1, ctx1) = reduce(m, term1, e) p
            val rule1 = TyRule(applySubst ctx1 term1, out1)
            val _ = debug ("checkSeq: if only the left operand applies: " ^ pp rule1) 0
            (* case 2: only r2 applies *)
            val _ = debug ("checkSeq: if only the right operand applies: " ^ pp r2) 0
            (* case 3: both operands apply *)
            val (rule3, _) = checkStar (m, r2) e p
            val _ = debug ("checkSeq: if both operands apply: " ^ pp rule3) 0
            val composition = TySum(rule3, TySum(rule1, r2))
            val _ = debug ("checkSeq: result is " ^ pp composition) ~1
        in
            (composition, e)
        end

  (* one of the operands is of unknown type: perform type-inferencing *)
  | checkSeq (x as TyVar _, y as TyRule(a,_)) e p = (y, unify(x, [TyRule(a,a)], e, p))
  | checkSeq (x as TyRule(_,a), y as TyVar _) e p = (x, unify(y, [TyRule(a,a)], e, p))
  | checkSeq (a as TyVar _, TySum(b,c)) e p
      = let
            val (ab, e1) = checkSeq (a,b) e p
            val (ac, e2) = checkSeq (a,c) e p
        in
            (TySum(ab,ac), intersect(e1, e2))
        end
  | checkSeq (TySum(a,b), c as TyVar _) e p
      = let
            val (ac, e1) = checkSeq (a,c) e p
            val (bc, e2) = checkSeq (b,c) e p
        in
            (TySum(ac,bc), intersect(e1, e2))
        end
  
  | checkSeq (TyInf, _) e _ = (TyInf, e)
  | checkSeq (_, TyInf) e _ = (TyInf, e)

  (* otherwise raise a type error *)
  | checkSeq (ty1,ty2) _ p = raiseCompositionError ty1 ty2 p "unexpected operands in sequential composition"

(* =================================================================================================================
 * Composes strategies x and y using combinator F.
 * createComp: string -> ty -> ty -> context -> expr -> ty
 * ================================================================================================================= *)
fun createComp F x y e p = case F of
                               "<+>" => (TySum (x,y), e)
                             | "<+"  => (TySum (x,y), e)
                             | "+>"  => (TySum (y,x), e)
                             | "<;"  => checkSeq (x,y) e p
                             | ";>"  => checkSeq (y,x) e p
                             | "<*"  => checkStar(x,y) e p
                             | _     => checkStar(y,x) e p

(* =================================================================================================================
 * Folds a list of dynamic rules into a single strategy.
 * foldRules: string -> expr -> (ty * context) -> (ty * context)
 * foldSRules: string -> expr -> (ty * context) -> (ty * context)
 * ================================================================================================================= *)
fun foldRules F _ (TyRule(a, b as TyRule _  ), e) = (TyRule (a, b), e) (* nothing to fold *)
  | foldRules F p (TyRule(a, TyList (x::xs) ), e)
    = let
          val (ty1,e1) = foldl (fn (z,acc) => createComp F (#1 acc) z (#2 acc) p) (x,e) xs
      in
          (TyRule (applySubst e1 a, ty1), e1)
      end
  | foldRules F p (TySum (a,b), e)
    = let
          val (tyA, _) = foldRules F p (a,e)
          val (tyB, _) = foldRules F p (b,e)
      in
          (TySum(tyA, tyB), e)
      end
  | foldRules _ _ (TyInf, e) = (TyInf, e)
  | foldRules _ _ (ty1,_) = raise TypeError("COMPOSITION.foldRules.match: " ^ pp ty1)

fun foldSRules F p (r1 as TyRule(a, b as TyRule _ ), e) = foldRules F p (TyRule(a, TyList [b, alphaRename r1]), e)
  | foldSRules F p (r1 as TyRule(a, TyList (x::xs)), e)
    = let
          val (ty1,e1) = case x of
                             TyList (d::ds) => foldl (fn (z,acc) => createComp F (#1 acc) z (#2 acc) p) (d,e) ds
                           | _              => (x,e) (* nothing to pre-fold *)
      in
          foldRules F p (TyRule(a, TyList (ty1::xs)), e1)
      end
  | foldSRules F p (TySum (a,b), e)
    = let
          val (tyA, _) = foldSRules F p (a,e)
          val (tyB, _) = foldSRules F p (b,e)
      in
          (TySum(tyA, tyB), e)
      end
  | foldSRules _ p (ty1,_)
      = raise TypeError(ninfostring p ^
                        "Type error: foldS operator's argument is not a higher-order strategy" ^ crlf ^
                        "  strategy:      " ^ pp ty1 ^ crlf ^
                        "  in expression: " ^ exprToString p)

end
