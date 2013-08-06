structure UNIFICATION = struct
structure A = ABSTRACT
open UTIL

exception UNIFY;

(* app: (int * ty) list -> int -> ty *)
fun app ((i,t)::rest) x = if x = i then t else app rest x
  | app [] x = raise TypeError("UNIFICATION.app.match: [] " ^ Int.toString x)

(* lift: (int * ty) list -> ty -> ty *)
fun lift s = mapTy (fn (t as TyTerm(r,[TyVar x])) => if List.exists (fn (i,_) => x = i) s
                                                     then let
                                                              val newTy = app s x
                                                          in
                                                              case newTy of
                                                                TyTerm _ => newTy
                                                              | baseTy => TyTerm(r,[baseTy])
                                                          end
                                                     else t
                       | otherTy => otherTy )

(* solve: (ty * ty) list * env -> env *)
fun solve [] e = e
  | solve ((TyVar i,     ty2        )::xs) e = elim [(i,ty2)] xs e
  | solve ((ty1,         TyVar i    )::xs) e = elim [(i,ty1)] xs e
  | solve ((TySum (a,b), TySum (c,d))::xs) e = solve ((a,c)::(b,d)::xs) e
  | solve ((TyRule(a,b), TyRule(c,d))::xs) e = solve ((a,c)::(b,d)::xs) e
  | solve ((a as TyTerm (x,xs),
            b as TyTerm (y,ys))::rest) e
      = (fine("solve.term.input: " ^ toString a ^ " | " ^ toString b) 2;
        if x <> y andalso
           x <> "'term" andalso y <> "'term" (* neither term's root is generic *)
        then raise UNIFY
        else let
                 fun zip [] [] = []
                   | zip [] _  = raise UNIFY
                   | zip _  [] = raise UNIFY
                   | zip (b::bs) (c::cs) = (b,c)::(zip bs cs)
                 fun existsChoice kids (TySum(a,b)) = (existsChoice kids a handle UNIFY => existsChoice kids b)
                   | existsChoice kids anyOther
                     = let
                           fun getFirstMatch (t::ts) ty1
                               = let
                                     val (unified, env) = (true, solve [(t,ty1)] e) handle UNIFY => (false, e)
                                 in
                                     if unified
                                     then env
                                     else getFirstMatch ts ty1
                                 end
                             | getFirstMatch [] _ = raise UNIFY
                       in
                           getFirstMatch kids anyOther
                       end
             in
                 case xs of 
                   [TyVar i] => (case ys of
                                   [TyVar j]  => elim [(j,TyVar i)] rest e
                                 | [TySome s] => elim [(i,TySome s)] rest e
                                 | _          => elim [(i,b)] rest e)
                 | [TySome s] => (case ys of
                                    [TyVar j]   => elim [(j,TySome s)] rest e
                                  | [TySome s2] => solve ((s,s2)::rest) e
                                  | _ => if List.exists (fn i => i = s) ys
                                         then solve rest e
                                         else existsChoice ys s)
                 | _ => case ys of
                          [TyVar j]  => elim [(j,a)] rest e
                        | [TySome s] => if List.exists (fn i => i = s) xs
                                        then solve rest e
                                        else existsChoice xs s
                 | _ => solve ((zip xs ys) @ rest) e
             end)
  | solve ((TyTerm _,        TySum  _        )::xs) e = raise UNIFY
  | solve ((TySum  _,        TyTerm _        )::xs) e = raise UNIFY
  | solve ((TyTerm _,        TyRule _        )::xs) e = raise UNIFY
  | solve ((TyRule _,        TyTerm _        )::xs) e = raise UNIFY
  | solve ((TyTerm(_,[ty1]), ty2             )::xs) e = solve ((ty1,ty2)::xs) e (* linear term and a base type *)
  | solve (( ty1,            TyTerm (_,[ty2]))::xs) e = solve ((ty1,ty2)::xs) e

  | solve ((a as TyTerm(x,[]),ty2            )::xs) e = (case inferPrimType a of
                                                           TyTerm(x,[]) => if a = ty2 then solve xs e
                                                                           else raise UNIFY
                                                         | z => solve ((z, ty2)::xs) e) (* leaf and prim type *)
  | solve ((ty1,             TyTerm(y,[])    )::xs) e = solve ((TyTerm(y,[]), ty1)::xs) e

  | solve ((r as TyRule _,   TySum(a,b)      )::xs) e = (solve ((r,a)::xs) e handle UNIFY =>
                                                         solve ((r,b)::xs) e)

  | solve (( ty1,            ty2             )::xs) e = if ty1 = ty2 then solve xs e else raise UNIFY

(* elim: (int * ty) list -> (ty * ty) list -> env -> env *)
and elim []          tts e = solve tts e
  | elim ((x,t)::xs) tts e = let
                                 val xt = lift [(x,t)]
                                 val tts2 = map (fn (tyA,tyB) => (xt tyA, xt tyB)) tts
                                 val e2 = S.insert(e, x, t)
                                 val oldBindings: (int * ty) list = S.listItemsi e2
                                 (*fun update ((key,TyVar oldVar)::rest) e = if oldVar = x
                                                                           then update rest (S.insert(e,key,t))
                                                                           else update rest e
                                   | update ( _                ::rest) e = update rest e
                                   | update [] e = e*)
                                 fun update ((key,ty1)::rest) e = update rest (S.insert(e,key,applySubst e ty1))
                                   | update [] e = e
                                 val e3 = update oldBindings e2
                             in
                                 elim xs tts2 e3
                             end

(* Unifies a type with a list of expected types. The first successful unification returns an updated context.
 * unify: (ty * ty list * context * expr) -> context *)
fun unify (givenTy, [expectedTy], env, expr)
      = ((solve [(givenTy,expectedTy)] env) handle UNIFY => raiseOperandError expectedTy givenTy expr "operator and operand don't agree")
  | unify (givenTy, expectedTypes, env, expr)
      = let
            fun polyUnify  []           = raisePolyOpError (givenTy, expr)
              | polyUnify (expTy::rest) = (solve [(givenTy,expTy)] env) handle UNIFY => polyUnify rest

        in
            polyUnify expectedTypes
        end
end