(* ============================================================================================= *)
signature TYPECHECK_SIG =
sig
    val typeCheck: ABSTRACT_REPRESENTATION.EXPR -> ABSTRACT_REPRESENTATION.EXPR ->
                    Grammar_AbstractSyntax.grammar -> UTIL.configuration -> ABSTRACT_REPRESENTATION.EXPR
    val typeOf   : ABSTRACT_REPRESENTATION.EXPR * ENV.context -> ENV.ty * ENV.context

end;
(* ============================================================================================= *)

(* ============================================================================================= *)
structure TYPECHECK : TYPECHECK_SIG = struct
open COMPOSITION
(* =============================================================================================
 * Contexts are threaded through the analysis of combinators. To avoid naming conflicts, a variable
 * is associated with a scope token defining where that variable was implicitly declared. *)
val ruleScope = ref 0
fun newScope() = ruleScope := !ruleScope + 1
fun look2(e, id, scope)
  = if scope = ~1
    then NONE
    else case look(e, id ^ Int.toString(scope)) of
           NONE    => look2(e, id, scope - 1)
         | option1 => option1

(* Records implicitly declared match vars: for each new <t>_x records a mapping <t>_x -> t[ 'a ].
 * updateEnv: EXPR -> context -> context *)
fun updateEnv expr env
    = foldExpr
        (fn (_, e) => e)
        (foldTerm (fn (imatch_var(sym, id1, _), e) => if inDomain(e, sym^id1^Int.toString(!ruleScope))
                                                      then e
                                                      else enter(e, sym^id1^Int.toString(!ruleScope), nextVar())
                    | (_,e) => e
                  )
        )
        (expr, env)

(* =============================================================================================
 * =============================================================================================
 * =============================================================================================
 * typeOf: EXPR * context -> ty * context *)
fun
  (* --------------------------------- Iterators ----------------------------------------------- *)
    typeOf(p as ITERATOR  (IDENTIFIER (id,_), [s], _), e)
      = let
            val (ty1, e1) = typeOf(s, e)
        in
            if !precision < 5 then (TyInf, e)
            else (TyIter (id,ty1), e1)
        end

  | typeOf(p as ITERATOR  (IDENTIFIER (id,_), xs, ninfo), _)
      = raise TypeError(ninfoToString ninfo ^
                        "Assertion: semantics of multiple strategy arguments for an iterator has not yet been specified" ^ crlf ^
                        "  in expression: " ^ exprToString p)

  (* --------------------------------- Non-rec iterators --------------------------------------- *)
  | typeOf(p as MAPL (expr,_), e)
      = let
            val (ty1, e1) = typeOf(expr, e)
        in
            if !precision < 4 then (TyInf, e)
            else (TyMap ty1, e1)
            (* if a la ML: TyRule( TyTerm('a, 'b list), TyTerm('a, 'c list) ) *)
        end

  | typeOf(p as MAPR (expr,_), e)
      = let
            val (ty1, e1) = typeOf(expr, e)
        in
            if !precision < 4 then (TyInf, e)
            else (TyMap ty1, e1)
        end

  | typeOf(p as MAPB (expr,_), e)
      = let
            val (ty1, e1) = typeOf(expr, e)
        in
            if !precision < 4 then (TyInf, e)
            else (TyMap ty1, e1)
        end

  (* --------------------------------- Heterogeneous FOLD -------------------------------------- *)
  | typeOf(p as FOLDS_CHOICE  (expr,_), e)
      = let
            val (ty1, e1) = (isFoldS := true; typeOf(expr, e))
        in
            if !precision < 5 then (TyInf, e)
            else foldSRules "<+>" p (ty1, e1)
        end
  | typeOf(p as FOLDS_LCHOICE (expr,_), e)
      = let
            val (ty1, e1) = (isFoldS := true; typeOf(expr, e))
        in
            if !precision < 5 then (TyInf, e)
            else foldSRules "<+" p (ty1, e1)
        end
  | typeOf(p as FOLDS_RCHOICE (expr,_), e)
      = let
            val (ty1, e1) = (isFoldS := true; typeOf(expr, e))
        in
            if !precision < 5 then (TyInf, e)
            else foldSRules "+>" p (ty1, e1)
        end
  | typeOf(p as FOLDS_LSEQ    (expr,_), e)
      = let
            val (ty1, e1) = (isFoldS := true; typeOf(expr, e))
        in
            if !precision < 5 then (TyInf, e)
            else foldSRules "<;" p (ty1, e1)
        end
  | typeOf(p as FOLDS_RSEQ    (expr,_), e)
      = let
            val (ty1, e1) = (isFoldS := true; typeOf(expr, e))
        in
            if !precision < 5 then (TyInf, e)
            else foldSRules ";>" p (ty1, e1)
        end
  | typeOf(p as FOLDS_LSTAR   (expr,_), e)
      = let
            val (ty1, e1) = (isFoldS := true; typeOf(expr, e))
        in
            if !precision < 5 then (TyInf, e)
            else foldSRules "<*" p (ty1, e1)
        end
  | typeOf(p as FOLDS_RSTAR   (expr,_), e)
      = let
            val (ty1, e1) = (isFoldS := true; typeOf(expr, e))
        in
            if !precision < 5 then (TyInf, e)
            else foldSRules "*>" p (ty1, e1)
        end

  (* --------------------------------- Homogeneous FOLD ---------------------------------------- *)
  | typeOf(p as FOLD_CHOICE   (expr,_), e)
      = let
            val (ty1, e1) = typeOf(expr, e)
        in
            if !precision < 3 then (TyInf, e)
            else foldRules "<+>" p (ty1, e1)
        end
  | typeOf(p as FOLD_LCHOICE  (expr,_), e)
      = let
            val (ty1, e1) = typeOf(expr, e)
        in
            if !precision < 3 then (TyInf, e)
            else foldRules "<+" p (ty1, e1)
        end
  | typeOf(p as FOLD_RCHOICE  (expr,_), e)
      = let
            val (ty1, e1) = typeOf(expr, e)
        in
            if !precision < 3 then (TyInf, e)
            else foldRules "+>" p (ty1, e1)
        end
  | typeOf(p as FOLD_LSEQ     (expr,_), e)
      = let
            val (ty1, e1) = typeOf(expr, e)
        in
            if !precision < 3 then (TyInf, e)
            else foldRules "<;" p (ty1, e1)
        end
  | typeOf(p as FOLD_RSEQ     (expr,_), e)
      = let
            val (ty1, e1) = typeOf(expr, e)
        in
            if !precision < 3 then (TyInf, e)
            else foldRules ";>" p (ty1, e1)
        end
  | typeOf(p as FOLD_LSTAR    (expr,_), e)
      = let
            val (ty1, e1) = typeOf(expr, e)
        in
            if !precision < 3 then (TyInf, e)
            else foldRules "<*" p (ty1, e1)
        end
  | typeOf(p as FOLD_RSTAR    (expr,_), e)
      = let
            val (ty1, e1) = typeOf(expr, e)
        in
            if !precision < 3 then (TyInf, e)
            else foldRules "*>" p (ty1, e1)
        end

  (* --------------------------------- Binary combinators -------------------------------------- *)
  | typeOf(p as CHOICE  (a, b, _), e)
      = let
            val (ty1, _) = typeOf(a, e)
            val (ty2, _) = typeOf(b, e)
            val _ = checkOrder (ty1,ty2) p
            val _ = case a of
                      (ID _) => raiseCompositionError ty1 ty2 p "right operand is unreachable due to ID on the left"
                    | _      => ()
        in
            if !precision < 2 then (TyInf, e)
            else (TySum (ty1,ty2), e)
        end

  | typeOf(p as LCHOICE (a, b, _), e)
      = let
            val (ty1, _) = typeOf(a, e)
            val (ty2, _) = typeOf(b, e)
            val _ = checkOrder (ty1,ty2) p
            val _ = case a of
                      (ID _) => raiseCompositionError ty1 ty2 p "right operand is unreachable due to ID on the left"
                    | _      => ()
        in
            if !precision < 2 then (TyInf, e)
            else (TySum (ty1,ty2), e)
        end

  | typeOf(p as RCHOICE (a, b, _), e)
      = let
            val (ty1, _) = typeOf(b, e)
            val (ty2, _) = typeOf(a, e)
            val _ = checkOrder (ty1,ty2) p
            val _ = case b of
                      (ID _) => raiseCompositionError ty1 ty2 p "left operand is unreachable due to ID on the right"
                    | _      => ()
        in
            if !precision < 2 then (TyInf, e)
            else (TySum (ty1,ty2), e)
        end

  | typeOf(p as LSEQ    (left,right,_), e)
      = let
            val _ = newScope()
            val (ty1, e1) = typeOf(left, e )
            val _ = newScope()
            val (ty2, e2) = typeOf(right,e1)
            val _ = checkOrder (ty1,ty2) p
        in
            if !precision < 2 then (TyInf, e)
            else checkSeq (ty1,ty2) e2 p
        end

  | typeOf(p as RSEQ    (left,right,_), e)
      = let
            val _ = newScope()
            val (ty1, e1) = typeOf(right,e )
            val _ = newScope()
            val (ty2, e2) = typeOf(left, e1)
            val _ = checkOrder (ty1,ty2) p
        in
            if !precision < 2 then (TyInf, e)
            else checkSeq (ty1,ty2) e2 p
        end

  | typeOf(p as LSTAR   (left,right,_), e)
      = let
            val _ = newScope()
            val (ty1, e1) = typeOf(left, e ) (* <id>_1 -> id[:] x [:] <* <id>_1 -> id[:] y [:] is id[ 'a ] -> id[ y ] *)
            val _ = newScope()
            val (ty2, e2) = typeOf(right,e1) (* and not id[ x ] -> id[ y ]. Cannot carry e1 into typing of r2.  *)
            val _ = checkOrder (ty1,ty2) p
        in
            if !precision < 2 then (TyInf, e)
            else checkStar (ty1,ty2) e2 p
        end

  | typeOf(p as RSTAR   (left,right,_), e)
      = let
            val _ = newScope()
            val (ty1, e1) = typeOf(right,e )
            val _ = newScope()
            val (ty2, e2) = typeOf(left, e1)
            val _ = checkOrder (ty1,ty2) p
        in
            if !precision < 2 then (TyInf, e)
            else checkStar (ty1,ty2) e2 p
        end

  (* --------------------------------- Unary combinators --------------------------------------- *)
  (* Assertion: these combinators do not modify the type of their argument strategy. *)
  | typeOf(p as TRANSIENT (expr,_), e) = typeOf(expr, e)
  | typeOf(p as OPAQUE    (expr,_), e) = typeOf(expr, e)
  | typeOf(p as RAISE     (expr,_), e) = typeOf(expr, e)
  | typeOf(p as HIDE      (expr,_), e) = typeOf(expr, e)
  | typeOf(p as LIFT      (expr,_), e) = typeOf(expr, e)

  (* --------------------------------- Rewrite rules ------------------------------------------- *)
  | typeOf(p as RULE      (left,right,_), e)
      = let
            val _ = fine("typeOf.rule.raw-input: " ^ exprToString p) 2
            val e0 = updateEnv left e         (* bind schema vars on the left *)
            val (ty1, e1) = typeOf(left,  e0) (* infer types *)
            val (ty2, e2) = typeOf(right, e1)
            val r1 = TyRule (ty1, ty2)
            val _ = debug("typeOf.rule.input: " ^ toString r1) 1
            val r2 = applySubst e2 r1 (* propagate any inferred type substitutions *)
            val _ = debug("typeOf.rule.post-substitutions: " ^ toString r2) 0
            val tyOut = normalize e2 r2
            val _ = debug("typeOf.rule.output: " ^ toString tyOut) ~1
        in
            (tyOut, e2)
        end

  | typeOf(p as COND_RULE (left, right, cond, ninfo), e)
      = let
            val _ = fine("typeOf.ruleCond.raw-input: " ^ exprToString p) 2
            val e0 = updateEnv left e
            val (tyc, ec) = typeOf(cond, e0)
            val tyc2 = case cond of
                         (m as APP (ID _,_,_))   => raiseTautologyError m p
                       | (m as APP (SKIP _,_,_)) => raiseTautologyError m p
                       | APP (_,_,_)             => TyBool
                       | _                       => tyc
            val _    = case tyc2 of
                         TyVar _ => TyBool (* if cond is a call to an undeclared sml fun *)
                       | TyBool  => TyBool
                       | _       => raise TypeError(ninfoToString ninfo ^
                                        "Type error: rule condition's type is not boolean:" ^ crlf ^
                                        "  found:         " ^ pp tyc2                       ^ crlf ^
                                        "  in expression: " ^ exprToString p)
            val (ty1, e1) = typeOf(left,  ec)
            val (ty2, e2) = typeOf(right, e1)
            val r1 = TyRule (ty1, ty2)
            val _ = debug("typeOf.ruleCond.input: " ^ toString r1) 1
            val r2 = applySubst e2 r1
            val _ = debug("typeOf.ruleCond.post-substitutions: " ^ toString r2) 0
            val tyOut = normalize e2 r2
            val _ = debug("typeOf.ruleCond.output: " ^ toString tyOut) ~1
        in
            (tyOut, e2)
        end

  | typeOf(ID _,   e) = let
                            val a = nextVar()
                        in
                            (TyRule(a, a), e)
                        end
  | typeOf(SKIP _, e) = let
                            val a = nextVar()
                        in
                            (TyRule(a, a), e)
                        end
  (*--------------------------------------------------------------------------------------------------------*)

  (*--------------------------------- Application ----------------------------------------------------------*)
  | typeOf(p as APP     (expr1, expr2, _), e)
    = let
        val (ty1, e1) = typeOf(expr1, e )
        val (ty2, e2) = typeOf(expr2, e1)
      in
          reduce(ty1, ty2, e2) p
      end
  (*--------------------------------------------------------------------------------------------------------*)

  (*--------------------------------------------------------------------------------------------------------*)
  | typeOf(p as TERM (aTree,ninfo), e)
      = let
            fun getTermType (itree (inode(name, _), [])) = TyTerm (name, [])
              | getTermType (itree (imatch_var (sym,id1, _), []))
                  = (case look2(e, sym^id1, !ruleScope) of
                       SOME (TyTerm x) => TyTerm x
                     | SOME primTy => TyTerm(sym, [primTy])
                     | NONE        => raise TypeError(ninfoToString ninfo ^
                                                      "Type error: unbound/free pattern variable " ^
                                                      "<" ^ sym ^ ">" ^ id1 ^ crlf ^
                                                      "  in expression: " ^ exprToString p))
              | getTermType (itree (inode(name,_), xs)) = TyTerm (name, map getTermType xs)
              | getTermType (itree (imatch_var _,_)) = raise TypeError "Impossible: match vars cannot have subterms"

            val ty1 = getTermType aTree
            (* val _ = C.fullPrintTree crlf aTree     *)
        in
            (ty1, e)
        end
  (*--------------------------------------------------------------------------------------------------------*)

  (*--------------------------------- Conditions -----------------------------------------------------------*)
  (* BIND is replaced by REF after type-checking, so there is no need to type-check REF constructors  *)
  | typeOf(p as BIND    (IDENTIFIER (id,_), expr1, _), e)
      = let
            val _ = debug("typeOf:(bind) analyzing " ^ id) 1
            val (ty1, e1) = typeOf(expr1, enter(e, id, nextVar()))
            val tyOut = applySubst e1 ty1
            val _ = debug("typeOf:(bind) result is " ^ toString tyOut) ~1
        in
            (TyBool, enter(e1, id, tyOut))
        end

  | typeOf(p as MATCH   (expr1, expr2, ninfo), e)
      = let
            fun try (a, b, e) = let
                                    val e0 = updateEnv a e
                                    val (tyA, e1) = typeOf(a, e0)
                                    val (tyB, e2) = typeOf(b, e1)
                                in
                                    (tyA, tyB, e2)
                                end
            val (ty1, ty2, e2) = try (expr1, expr2, e) handle
                                   TypeError _ => (* switch lhs and rhs *)
                                     (inputTree := A.bottom_up
                                                     (fn (MATCH (i, j, xinfo)) => if i = expr1 andalso j = expr2
                                                                                  then MATCH (j, i, xinfo)
                                                                                  else MATCH (i, j, xinfo)
                                                         | x => x)
                                                     (fn x => x)
                                                     (!inputTree);
                                      try (expr2, expr1, e) )

            val _ = fine("typeOf.match. input: " ^ toString ty1 ^ " | " ^ toString ty2) 1
            fun match (TyInf, _) env = env
              | match (_, TyInf) env = env
              | match (a, TySum (b,c)) env
                  = let
                        val env1 = match (a,b) env handle TypeError _ => match (a,c) env
                        val env2 = match (a,c) env handle TypeError _ => env1
                    in
                        intersect (env1,env2)
                    end
              | match (ty1 as TySum _     , ty2                ) env = match (ty2,ty1) env
              | match (TyTerm("id",_)     , TyTerm("wild_id",_)) env = env
              | match (TyTerm("wild_id",_), TyTerm("id",_)     ) env = env
              | match (ty1                , ty2                ) env = unify (ty1, [ty2], env, p)
            val e3 = match (ty1,ty2) e2
            val _ = fine("typeOf.match.post-match: pre-substitutions") 0
            val (ty1A, ty2A) = (applySubst e3 ty1, applySubst e3 ty2)
            val _ = fine("typeOf.match.post-match: " ^ toString ty1A ^ " | " ^ toString ty2A) 0
            fun ckMatch (TyInf, _) = TyBool
              | ckMatch (_, TyInf) = TyBool
              | ckMatch (TyTerm ("id",_),      TyTerm ("wild_id",_)) = TyBool
              | ckMatch (TyTerm ("wild_id",_), TyTerm ("id",_)     ) = TyBool
              | ckMatch (_,                    TySum _             ) = TyBool
              | ckMatch (TySum _             , _                   ) = TyBool
              | ckMatch (ty1, ty2)
                = if toString ty1 = toString ty2 then TyBool
                  else if toString (convertLeafsToPrims ty1) = toString (convertLeafsToPrims ty2) then TyBool
                  else raiseOpEqError (ty1,ty2,p)
            val tyOut = ckMatch (ty1A, ty2A)
            val _ = fine("typeOf.match.output: " ^ toString tyOut) ~1
        in
            (tyOut, e3)
        end

  | typeOf(p as ANDALSO (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val ty1b = skipNonBoolExpr expr1 ty1 p
            val ty2b = skipNonBoolExpr expr2 ty2 p
            val e3 = unify (TySum (ty1b,ty2b), [TySum (TyBool,TyBool)], e2, p)
        in
            (applySubst e3 ty1b, e3)
        end

  | typeOf(p as ORELSE  (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e)
            val (ty2, e2) = typeOf(expr2, e) (* forget bindings of the left branch *)
            fun skipThrows (LIBRARY_CALL_0 _) _ _  e2 = e2
              | skipThrows (LIBRARY_CALL   _) _ _  e2 = e2
              | skipThrows _ (LIBRARY_CALL_0 _) e1 _  = e1
              | skipThrows _ (LIBRARY_CALL   _) e1 _  = e1
              | skipThrows _ _                  e1 e2 = intersect (e1,e2)
            val e12 = skipThrows expr1 expr2 e1 e2
            val ty1b = skipNonBoolExpr expr1 ty1 p
            val ty2b = skipNonBoolExpr expr2 ty2 p
            val e3 = unify (TySum (ty1b,ty2b), [TySum (TyBool,TyBool)], e12, p)
        in
            (applySubst e3 ty1b, e3)
        end

  | typeOf(p as NOT     (expr1, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e)
            val ty1b = skipNonBoolExpr expr1 ty1 p
            val e3 = unify (ty1b, [TyBool], e1, p)
        in
            (applySubst e3 ty1b, e) (* forget all new bindings *)
        end
  (*--------------------------------------------------------------------------------------------------------*)

  (*--------------------------------- SML function calls ---------------------------------------------------*)
  | typeOf(p as LIBRARY_CALL_0 (IDENTIFIER (id,_), ninfo), e)
      = (case look(e, id) of
           NONE => let (* perform type-inferencing *)
                       val tyOut = nextVar()
                   in
                       (tyOut, enter(e, id, TyRule (TyUnit, tyOut)))
                   end
         | SOME (TyRule (TyUnit, tyOut)) => (tyOut, e)
         | SOME anyOther => raise TypeError(ninfoToString ninfo ^
                                          "Type error: SML function's type does not match declared type" ^ crlf ^
                                          "  function call: " ^ id ^ "()"   ^ crlf ^
                                          "  function type: " ^ pp anyOther ^ crlf ^
                                          "  in expression: " ^ exprToString p) )
  | typeOf(p as LIBRARY_CALL   (IDENTIFIER (id,_), args, ninfo), e)
      = let
            val (ty1, e1) = case look(e, id) of
                               NONE       => let (* perform type-inferencing *)
                                                 val type1 = TyRule (nextVar(), nextVar())
                                             in
                                                 (type1, enter(e, id, type1))
                                             end
                             | SOME type1 => (type1, e)

            val _ = debug("typeOf.libraryCall.funTy: " ^ toString ty1) 1
            fun zip ([], _) _ = raiseTypeError p "Match failure in TYPECHECK.zip on args: ([], _)"
              | zip (a::[], tyB) e = let
                                         val (tyA, e1) = typeOf(a, e)
                                     in
                                         unify(tyA, [tyB], e1, p)
                                     end
              | zip (a::rest, TySum(tyB,tyRest)) e
                                   = let
                                         val (tyA, e1) = typeOf(a, e)
                                         val e2 = unify(tyA, [tyB], e1, p)
                                     in
                                         zip (rest, tyRest) e2
                                     end
              | zip (_, tyB) _ = raiseTypeError p ("Type error: unexpected sml function arity:" ^ crlf ^
                                                   "  expected: " ^ toString tyB)

            fun check params (r as TyRule (TyVar _, tyOut)) e (* type-inferencing *)
                  = let
                        (* create as many type-vars as there are actual parameters *)
                        fun inflate []         = raiseTypeError p "Match failure in TYPECHECK.inflate on arg: []"
                          | inflate (_::[])    = nextVar()
                          | inflate (_::y::zs) = TySum (nextVar(), inflate(y::zs))
                        val e2 = zip (params, inflate params) e
                    in
                        (applySubst e2 tyOut, e2)
                    end
              | check params (TyRule (tyIn, tyOut)) e    (* type-checking *)
                  = let
                        val e2 = zip (params, tyIn) e
                    in
                        (applySubst e2 tyOut, e2)
                    end
              | check _ funTy _
                  = raiseTypeError p ("Type error: SML function's type does not match declared type" ^ crlf ^
                                      "  function:      " ^ id                                       ^ crlf ^
                                      "  function type: " ^ toString funTy)
            val (tyF, eF) = check args ty1 e1
            val _ = debug("typeOf.libraryCall.output: " ^ toString tyF) ~1
        in
            (tyF, eF)
        end
  (*--------------------------------------------------------------------------------------------------------*)

  (*--------------------------------- Boolean Ops ----------------------------------------------------------*)
  | typeOf(p as B_OR    (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2), [TySum (TyBool,TyBool)], e2, p)
        in
            (replaceLeaf [TyBool] (pickATree (applySubst e3 ty1, applySubst e3 ty2)), e3)
        end

  | typeOf(p as B_AND   (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2), [TySum (TyBool,TyBool)], e2, p)
        in
            (replaceLeaf [TyBool] (pickATree (applySubst e3 ty1, applySubst e3 ty2)), e3)
        end

  | typeOf(p as BANG    (expr1, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e)
            val e3 = unify (ty1, [TyBool], e1, p)
        in
            (replaceLeaf [TyBool] (applySubst e3 ty1), e3)
        end
  (*--------------------------------------------------------------------------------------------------------*)

  (*--------------------------------- Relational Ops -------------------------------------------------------*)
  | typeOf(p as EQ      (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1) (* In TL, reals can be checked for equality *)
            val e3 = unify (TySum (ty1,ty2),
              [TySum(TyBool,TyBool), TySum(TyInt,TyInt), TySum(TyReal,TyReal), TySum(TyString,TyString)], e2, p)
        in
            (TyBool, e3)
        end

  | typeOf(p as NEQ     (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum(ty1,ty2),
              [TySum(TyBool,TyBool), TySum(TyInt,TyInt), TySum(TyReal,TyReal), TySum(TyString,TyString)], e2, p)
        in
            (TyBool, e3)
        end

  | typeOf(p as LEQ     (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2),
                           [TySum(TyInt,TyInt), TySum(TyReal,TyReal), TySum(TyString,TyString)], e2, p)
        in
            (TyBool, e3)
        end

  | typeOf(p as LT      (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2),
                           [TySum(TyInt,TyInt), TySum(TyReal,TyReal), TySum(TyString,TyString)], e2, p)
        in
            (TyBool, e3)
        end

  | typeOf(p as GEQ     (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2),
                           [TySum(TyInt,TyInt), TySum(TyReal,TyReal), TySum(TyString,TyString)], e2, p)
        in
            (TyBool, e3)
        end

  | typeOf(p as GT      (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2),
                           [TySum(TyInt,TyInt), TySum(TyReal,TyReal), TySum(TyString,TyString)], e2, p)
        in
            (TyBool, e3)
        end
  (*--------------------------------------------------------------------------------------------------------*)

  (*--------------------------------- Math Ops -------------------------------------------------------------*)
  | typeOf(p as CONCAT  (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2), [TySum (TyString,TyString)], e2, p)
        in
            (replaceLeaf [TyString] (pickATree (applySubst e3 ty1, applySubst e3 ty2)), e3)
        end

  | typeOf(p as PLUS    (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2), [TySum (TyInt,TyInt), TySum (TyReal,TyReal)], e2, p)
        in
            (replaceLeaf [TyInt,TyReal] (pickATree (applySubst e3 ty1, applySubst e3 ty2)), e3)
        end

  | typeOf(p as MINUS   (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2), [TySum (TyInt,TyInt), TySum (TyReal,TyReal)], e2, p)
        in
            (replaceLeaf [TyInt,TyReal] (pickATree (applySubst e3 ty1, applySubst e3 ty2)), e3)
        end

  | typeOf(p as TIMES   (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2), [TySum (TyInt,TyInt), TySum (TyReal,TyReal)], e2, p)
        in
            (replaceLeaf [TyInt,TyReal] (pickATree (applySubst e3 ty1, applySubst e3 ty2)), e3)
        end

  | typeOf(p as DIVIDE  (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2), [TySum (TyReal,TyReal)], e2, p)
        in
            (replaceLeaf [TyReal] (pickATree (applySubst e3 ty1, applySubst e3 ty2)), e3)
        end

  | typeOf(p as DIV     (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2), [TySum (TyInt,TyInt)], e2, p)
        in
            (replaceLeaf [TyInt] (pickATree (applySubst e3 ty1, applySubst e3 ty2)), e3)
        end

  | typeOf(p as MOD     (expr1, expr2, _), e)
      = let
            val (ty1, e1) = typeOf(expr1, e )
            val (ty2, e2) = typeOf(expr2, e1)
            val e3 = unify (TySum (ty1,ty2), [TySum (TyInt,TyInt)], e2, p)
        in
            (replaceLeaf [TyInt] (pickATree (applySubst e3 ty1, applySubst e3 ty2)), e3)
        end

  | typeOf(p as TILDE   (expr1,_), e)
      = let
            val (ty1, e1) = typeOf(expr1, e)
            val e3 = unify (ty1, [TyInt, TyReal], e1, p)
        in
            (* type of a leaf is the leaf literally, unless the term is part of an arithmetic expression *)
            (replaceLeaf [TyInt, TyReal] (applySubst e3 ty1), e3)
        end
  (*--------------------------------------------------------------------------------------------------------*)

  (*--------------------------------- Primitive Values -----------------------------------------------------*)
  | typeOf(BOOL   _, e) = (  TyBool, e)
  | typeOf(INT    _, e) = (   TyInt, e)
  | typeOf(REAL   _, e) = (  TyReal, e)
  | typeOf(STRING _, e) = (TyString, e)
  | typeOf(IDENTIFIER (id, ninfo), e) = (case look(e, id) of
                                           SOME (TyVar i) => (TyVar i, e)
                                         | SOME type1 => (fine("typeOf.id: " ^ id ^ " | " ^ toString type1) 2;
                                                          (alphaRename type1, e))
                                         | NONE       => raise TypeError(ninfoToString ninfo ^
                                                                "Type error: undefined variable: " ^ id) )
  | typeOf(p, _) = raise TypeError("TYPECHECK.typeOf.match: " ^ exprToString p)
  (*--------------------------------------------------------------------------------------------------------*)



(* ===================================================================================================================
 * Records type declarations of SML functions in a typing context.
 * getSmlSignatures: EXPR list -> context -> context
 * ================================================================================================================= *)
fun getSmlSignatures [] e = e
  | getSmlSignatures (LIST (IDENTIFIER (funId,_)::funBody,_)::rest) e
      = let
            fun getTermType nonTermSym = let
                                            fun split1(x, []   ) = raise TypeError "Match failure in TYPECHECK.split1"
                                              | split1(x, y::ys) = if x = y then ys else split1(x,ys)
                                            fun split2(x, [])    = []
                                              | split2(x, y::ys) = if x = y then [] else y::split2(x,ys);
                                            val s0 = explode nonTermSym
                                            val s1 = split1(#"<",s0)
                                            val s2 = split2(#">",s1)
                                         in
                                            implode s2
                                         end
            fun getType (IDENTIFIER ("bool",   _)) = TyBool
              | getType (IDENTIFIER ("int",    _)) = TyInt
              | getType (IDENTIFIER ("real",   _)) = TyReal
              | getType (IDENTIFIER ("string", _)) = TyString
              | getType (IDENTIFIER ("unit",   _)) = TyUnit
              | getType (IDENTIFIER ("control",_)) = TyBool
              | getType (IDENTIFIER (other,    _)) = TyTerm (getTermType other, [nextVar()] )
              | getType t = raise TypeError("Incorrect SML function declaration type: " ^ exprToString t)

            fun aux []      = raise TypeError("Incorrect SML function type for: " ^ funId)
              | aux (x::[]) = getType x
              | aux (x::xs) = TySum (getType x, aux xs)
            val smlBody  = rev (funBody)
            val returnTy = getType (hd smlBody)
            val argsTy   = aux (rev (tl smlBody))
            val eNew = enter(e, funId, TyRule (argsTy, returnTy))
        in
            getSmlSignatures rest eNew
        end
  | getSmlSignatures (nonList::_) _
      = raise TypeError("SML function declarations can only contain function signatures: " ^ exprToString nonList)

(* ===================================================================================================================
 * Aux functions for regression-testing of the type-checker.
 * ================================================================================================================= *)
(* Type error counter and a corresponding incrementer function *)
val errors = ref 0
fun incErrors() = errors := !errors + 1 

(* Convert a list of strings that may contain variables into a list of strings where variables are replaced
 *   by their numeric indexes starting from 0 at the beginning of the list. If a variable is encountered that
 *   hasn't been seen before, bump the index up by 1, replace the variable by the index in the accumulated
 *   list of strings and continue processing the rest of the list.
 * normalizeVars: string list -> string list -> string list *)
fun normalizeVars []      acc _ = List.rev acc
  | normalizeVars (x::xs) acc seenVars
      = if String.isPrefix "'" x
        then let
                 (* get the index of a given string in a list of strings *)
                 fun getIndex str []      index = index
                   | getIndex str (v::vs) index = if str = v then index else getIndex str vs (index + 1)

                 val index = getIndex x seenVars 0
                 val seenVars2 = if index > (List.length seenVars - 1) then seenVars@[x] else seenVars
             in
                 normalizeVars xs (Int.toString index::acc) seenVars2
             end
        else normalizeVars xs (x::acc) seenVars

(* Check that two strings representing types are equal to each other modulo any type variables of the form 'a.
 * equals: (string * string) -> bool *)
fun equals(ruleStr1, ruleStr2)
      = let
            fun isSep #" "  = true
              | isSep #"\t" = true
              | isSep #"\r" = true
              | isSep #"\n" = true
              | isSep #"("  = true (* to remove opening parenthesis: e.g. ('a expr ...) *)
              | isSep #")"  = true
              | isSep #","  = true
              | isSep _     = false

            (* tokenize a string into a list of strings *)
            val tokens1 = String.tokens isSep ruleStr1
            val tokens2 = String.tokens isSep ruleStr2
            val tokens3 = normalizeVars tokens1 [] []
            val tokens4 = normalizeVars tokens2 [] []
        in
            tokens3 = tokens4
        end

(* For regression tests of the type-checker itself.
 * Compares an asserted type of a declaration to the actual/computed type.
 * checkAssertions: context -> EXPR -> context *)
fun checkAssertions e (PROG (declList,_) ) = foldl (fn (x,ctx) => checkAssertions ctx x) e declList
  | checkAssertions e (NON_RECURSIVE (IDENTIFIER (id,_), STRING (assertion,_), ninfo))
      = if not (String.isPrefix "assert_" id) then e
        else let
                 val ruleId = substring(id, 7, String.size id - 7)
             in
                 case look(e, ruleId) of
                   SOME type1 => if equals(assertion, toString type1) then e
                                 else (error("***" ^ crlf ^ ninfoToString ninfo ^
                                             "Regression test error: expected type <> actual type" ^ crlf ^
                                             "  expected type: " ^ assertion      ^ crlf ^
                                             "  actual type:   " ^ toString type1 ^ crlf ^
                                             "  rule id:       " ^ ruleId         ^ crlf) 0;
                                       incErrors();
                                       e)
                 | NONE       =>      (error("***" ^ crlf ^ ninfoToString ninfo ^
                                             "Regression test error: type assertion for non-existent rule" ^ crlf ^
                                             "  expected type: " ^ assertion ^ crlf ^
                                             "  actual type: unknown "       ^ crlf ^
                                             "  rule id:       " ^ ruleId    ^ crlf) 0;
                                       incErrors();
                                       e)
             end
  | checkAssertions e _ = e

(* ================================================================================================================== *)
(* Checks recursive and non-recursive declarations.
 * tyCheck: context -> EXPR -> context *)
fun tyCheck e (PROG (declList,_) ) = foldl (fn (x,ctx) => tyCheck ctx x) e declList
  | tyCheck e (p as NON_RECURSIVE (IDENTIFIER (id,_), expr, ninfo))
    = if String.isPrefix "assert_" id then e
      else
        let
            val _ = debug("tyCheck: analyzing body of " ^ id) 1
            val (ty1, _) = typeOf(expr, e) handle
              TypeError msg => (if !inTestingMode then ()(* ignore error messages in regression tests *)
                                else (error("***" ^ crlf ^ msg ^ crlf) 0; incErrors());
                                (TyError, e))
            val _ = debug("tyCheck: computed type is " ^ toString ty1) 0
            (*  Simplification rules:
             * (a + b) + (c + b) = (a + c) + b
             * (a + b) + b = a + b
             * (a + a) = a *)
            fun simplify (s as TySum(TySum(a,b), TySum(x,y))) = if toString b = toString y then (TySum(TySum(a,x),y)) else s
              | simplify (x as TySum(y as TySum(a,b),c)) = if toString b = toString c then y else x
              | simplify (TySum(a,b)) = if toString a = toString b then a else TySum(a,b)
              | simplify anyOther     = anyOther
            val exprType = mapTy simplify ty1
            val _ = debug("tyCheck: recording (simplified) type " ^ toString exprType) ~1
        in
           enter(e, id, exprType)
        end
  | tyCheck e (RECURSIVE (IDENTIFIER (id,_), args, expr, _)) = enter(e, id, TyInf)
  | tyCheck _ expr = raise TypeError("TYPECHECK.tyCheck.match: " ^ exprToString expr)

(* ================================================================================================================== *)
fun logDuplicateError p msg
    = (error("***" ^ crlf ^ ninfostring p ^ msg ^ crlf ^
             "  in expression: " ^ exprToString p ^ crlf) 0;
       incErrors())
(* Checks for and removes duplicate declarations
 * ckDuplicates: EXPR -> EXPR *)
fun ckDuplicates (PROG (declList,xinfo) )
    = let
          fun compare id (NON_RECURSIVE (IDENTIFIER (x,_), _, _)) = x = id
            | compare id (RECURSIVE (IDENTIFIER (x,_), _, _, _)) = x = id
            | compare _ _ = false
          fun aux acc (p as NON_RECURSIVE (IDENTIFIER (id,_), _, _))
              = if not (List.exists (compare id) acc)
                then p::acc
                else if !inTestingMode
                     then acc
                     else (logDuplicateError p "Type error: detected a duplicate rule; removing it from the program"; acc)
            | aux acc (p as RECURSIVE (IDENTIFIER (id,_), _, _, _))
              = if not (List.exists (compare id) acc)
                then p::acc
                else if !inTestingMode
                     then acc
                     else (logDuplicateError p "Type error: detected a duplicate recursive definition; removing it from the program"; acc)
            | aux acc p = (logDuplicateError p "Type error: unexpected declaration"; acc)
      in
          PROG (List.rev(foldl (fn (x,acc) => aux acc x) [] declList), xinfo)
      end
  | ckDuplicates p = (logDuplicateError p "Type error: unexpected program structure"; p)

(* ================================================================================================================== *)
structure StringSet = RedBlackSetFn (struct
                                         type ord_key = string
                                         val  compare = String.compare
                                     end)

(* ================================================================================================================== *)
(* Reorders non-recursive rule labels such that all calls are to labels defined earlier in the lexical ordering.
 * reorder: EXPR -> EXPR *)
fun removeFwdRefs (PROG (declList,xinfo) )
    = let
          val references = ref []
          fun getReferences body
              = (references := [];
                 A.bottom_up (fn (p as IDENTIFIER (x,_)) => (references := x::(!references); p)
                                 | x => x)
                             (fn x => x)
                             body;
                 !references)
          fun isDefinedEarlier id (NON_RECURSIVE (IDENTIFIER (x,_), _, _)::xs) = x = id orelse isDefinedEarlier id xs
            | isDefinedEarlier id (RECURSIVE  (IDENTIFIER (x,_), _, _, _)::xs) = x = id orelse isDefinedEarlier id xs
            | isDefinedEarlier id (_::xs) = isDefinedEarlier id xs
            | isDefinedEarlier id [] = false
          exception notFound
          fun getDef id ((p as NON_RECURSIVE (IDENTIFIER (x,_), _, _))::xs) = if x = id then p else getDef id xs
            | getDef id ((p as RECURSIVE  (IDENTIFIER (x,_), _, _, _))::xs) = if x = id then p else getDef id xs
            | getDef id (_::xs) = getDef id xs
            | getDef id [] = raise notFound
          fun aux acc ((p as NON_RECURSIVE (IDENTIFIER _, expr, _))::xs)
              = let
                  val referencedLabels = getReferences expr (* get id's of all calls/references *)
                  val refLabelsSet = StringSet.listItems(StringSet.addList(StringSet.empty, referencedLabels)) (* remove duplicates *)
                  val definedLaterIds = List.filter (fn x => not (isDefinedEarlier x acc)) refLabelsSet
                  val definedLaterBodies = map (fn id => getDef id xs handle notFound => FALSE) definedLaterIds
                  val definedLaterCleaned = List.filter (fn x => x <> FALSE) definedLaterBodies
                  val acc2 = definedLaterCleaned@acc (* put bodies of all rules defined later in front *)
                  val xs2 = List.filter (fn x => not (List.exists (fn b => b = x) definedLaterBodies) ) xs
                in
                  aux (p::acc2) xs2
                end
            | aux acc (x::xs) = aux (x::acc) xs
            | aux acc [] = List.rev acc
          fun fix rules = let val newRules = aux [] rules
                          in  if rules = newRules then newRules else fix newRules
                          end
      in
          PROG (fix declList,xinfo)
      end
  | removeFwdRefs x = x

(* Dependencies: environment -> util -> unification -> grammar -> reduce -> composition -> typecheck *)
(* ===================================================================================================================
 * Given
 *   - smlDecls: declarations of types of SML functions
 *   - program: TL program as an abstract syntax tree
 *   - grammar: extended-BNF grammar of a term language
 *   - configuration parameters defining type-checker's precision and verbosity levels
 * compute types of rewrite rules and recursive definitions and determine if the TL program is well-typed.
 * If the program is well-typed, return program', where all match equations are
 *   re-arranged to have free variables on the lhs and ground terms on the rhs of an equation.
 * Otherwise, raise a General.Fail error.
 * typeCheck: EXPR -> EXPR -> grammar -> {precision: int, verbosity: int} -> EXPR
 * ================================================================================================================= *)
fun typeCheck smlDecls program (G.GRAMMAR {precassoc_rules, production_list}) {precision, verbosity}
  = if precision = 0 then program else
    let
        val _ = init precision verbosity
        val _ = info "[starting type analysis]" 0
        val program1 = ckDuplicates program
        val program2 = removeFwdRefs program1
        val _ = inputTree := program2
        val _ = tgtGrammar := crop production_list (!tgtGrammar)
        
        val env1 = case smlDecls of
                     SIGNATURE (LIST (expr,_), _) => getSmlSignatures expr initialEnv
                   | _                            => initialEnv
        val env2 = tyCheck env1 program2
                     handle x => (error(exnName x ^ " " ^ exnMessage x) 0; env1)

        val _ = if !inTestingMode
                then checkAssertions env2 program2
                else env2
        val _ = info(envToString env2) 0
        val _ = fine("output program tree is " ^ exprToString (!inputTree)) 0
    in
        if !errors = 0
        then (info "[type analysis completed successfully]" 0; !inputTree)
        else (error("!***" ^ crlf ^
                    "    Type analysis failed with " ^ Int.toString (!errors) ^ " errors. See error messages above." ^ crlf ^
                    "***!" ^ crlf ^
                    "[type analysis completed with errors]") 0;
              !inputTree (*; raise General.Fail "Type error" *) )
    end
end; (* structure *)
