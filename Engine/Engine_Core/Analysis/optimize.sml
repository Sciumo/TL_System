(* ------------------------------------------------------------------------------------------- *)
signature OPTIMIZE_SIG =
sig
	val optimize:     int * int * Grammar_AbstractSyntax.grammar * ABSTRACT_REPRESENTATION.EXPR -> ABSTRACT_REPRESENTATION.EXPR
end;
(* ------------------------------------------------------------------------------------------- *)

(* ------------------------------------------------------------------------------------------- *)
structure OPTIMIZE : OPTIMIZE_SIG =
struct

open CONCRETE_REPRESENTATION;
open ABSTRACT_REPRESENTATION;
open Grammar_AbstractSyntax;

fun identity x    = x;
val unique_symbol = #"#"
val counter       = ref 0;
val env           = ref [] : (string * string) list ref;

(* ------------------------------------------------------------------------------------------- *)
val address = ref 0;
fun newAddress() = (
                     address := !address + 1;
                     SOME( !address )
                   )

(* ------------------------------------------------------------------------------------------- *)
fun generate_unique_id name =
    let
        fun trim (symbol,[])    = [] (* symbol was not in the input list *)
          | trim (symbol,x::xs) = if (x = symbol)
                                  then (* found split point *)
                                       []

                                  else (* keep looking      *)
                                       x::trim(symbol,xs);

        val trimmed_name = String.implode( trim (unique_symbol, String.explode(name) ) )
        val unique_name  = trimmed_name ^ Char.toString(unique_symbol) ^ Int.toString(!counter)
    in
        counter := !counter + 1;
        unique_name
    end

(* ------------------------------------------------------------------------------------------- *)
fun insert name = let
                      val new_name = generate_unique_id name
                  in
                      env := (name,new_name)::(!env)
                  end
(* ------------------------------------------------------------------------------------------- *)
fun find (name,(old_name,new_name)::rest) = if old_name = name then new_name
                                                               else find(name, rest)
  | find (name, [] ) = name
(* ------------------------------------------------------------------------------------------- *)
fun find_insert (name,(old_name,new_name)::rest) = if old_name = name then new_name
                                                                      else find_insert(name, rest)
  | find_insert (name, [] ) = let
                                 val new_name = generate_unique_id name
                              in
                                 env := (name,new_name)::(!env);
                                 new_name
                              end

(* ------------------------------------------------------------------------------------------- *)
fun rename_match_var (itree(imatch_var (symbol_type, symbol_id, x), []) ) =
																let
																	val new_symbol_id = find_insert( symbol_id, (!env) )
																in
																	itree(imatch_var(symbol_type, new_symbol_id, x), [])
																end

  | rename_match_var ignore = ignore

(* ------------------------------------------------------------------------------------------- *)
fun rename_identifier (IDENTIFIER (name, x_info)) = 	let
															val new_name = find( name, (!env) )
														in
															(IDENTIFIER (new_name, x_info))
														end

  | rename_identifier ignore = ignore

(* ------------------------------------------------------------------------------------------- *)
fun alpha_rename_defs ( PROG (expr_list, x_info_prog) ) =
	let
	    fun focus_on( RECURSIVE(id,arg_list,body, x_info) ) = 	let
																	fun process_arg( IDENTIFIER (arg,_) ) = insert arg
																	  | process_arg _ = raise General.Fail("Error in OPTIMIZE.aplha_rename_defs.process_arg.\n")

																	val _        = ( env := []; () )
																	val _        = map process_arg arg_list

																	val new_arg_list = map (ABSTRACT.bottom_up rename_identifier identity)  arg_list
																	val new_body     = ABSTRACT.bottom_up rename_identifier identity  body
																in
																	RECURSIVE(id, new_arg_list, new_body, x_info)
																end

              | focus_on ignore_expr                  = ignore_expr

            val new_expr_list = map (ABSTRACT.bottom_up focus_on identity) expr_list
	in
	    PROG (new_expr_list, x_info_prog)
	end

  | alpha_rename_defs _ = raise General.Fail("Error in OPTIMIZE.alpha_rename_defs: Unexpected term structured.\n");

(* ------------------------------------------------------------------------------------------- *)
fun alpha_rename expr =
		let
			val _        = ( env := []; () )
			val new_expr = ABSTRACT.bottom_up  identity rename_match_var expr
		in
			new_expr
		end

(* ------------------------------------------------------------------------------------------- *)
fun unfold (label, body) term  = let
                                      fun subst (IDENTIFIER (label_name, x1_info), body)  (IDENTIFIER (use_name, x2_info) ) =
													if use_name = label_name then body
												                              else IDENTIFIER (use_name, x2_info)
                                        | subst _ expr = expr

                                      val new_term = ABSTRACT.bottom_up (subst(label,body)) identity term
                                 in
                                      new_term
                                 end

(* ------------------------------------------------------------------------------------------- *)
fun inline_non_rec (PROG (expr_list, x_info_prog )) =
		let
			fun isMain( IDENTIFIER ("main", _) ) = true
              | isMain _                         = false

			exception acyclic

			fun occurs (IDENTIFIER (label_name, x1_info)) (IDENTIFIER (use_name, x2_info)) = if label_name = use_name then raise acyclic else IDENTIFIER (use_name, x2_info)
              | occurs _ expr = expr

			fun isAcyclic(label, body) = (ABSTRACT.bottom_up (occurs label) identity body; true ) handle acyclic => false

			fun inline ( (NON_RECURSIVE (label, body, x_info))::rest, acc_list ) =
									let
										fun getStr( IDENTIFIER (name_str, _) ) = name_str
										  | getStr _                           = raise General.Fail("Error: in OPTIMIZE.inline_non_rec.inline.getStr -- expected id \n")

										val renamed_body = alpha_rename body
										val new_acc_list = map (unfold (label, renamed_body) ) acc_list
										val new_rest     = map (unfold (label, renamed_body) ) rest

	                                in
										if isAcyclic(label,body) then
												if isMain(label) then inline( new_rest, (NON_RECURSIVE(label,body, x_info))::new_acc_list )
												else                  inline( new_rest, new_acc_list )
										else raise General.Fail("Error 1: in OPTIMIZE.inline_non_rec.inline: recursive cycle detected involving " ^ getStr(label) ^ "\n")
									end

	          | inline( (RECURSIVE( label, args, body, x_info ) )::rest, acc_list ) = inline(rest, (RECURSIVE( label, args, body, x_info ))::acc_list)
	          | inline( [], acc_list ) = acc_list
	          | inline _ = raise General.Fail("Error 2: in OPTIMIZE.inline_non_rec.inline: unexpected term structure.\n")

			val inlined_expr_list = inline( expr_list, [] )
		in
			PROG( inlined_expr_list, x_info_prog )
		end

  | inline_non_rec _ = raise General.Fail("Error 3 in OPTIMIZE.inline_non_rec: Improper term structure.\n")

(* ------------------------------------------------------------------------------------------- *)
fun beta_reduction_in_match prog_expr =
	let
		fun beta_reduce( MATCH(pattern,APP(RULE(lhs,rhs, x_info_rule),term, x_info_app), x_info_match) ) =
				let
					val (lhs', rhs') = case alpha_rename (RULE(lhs,rhs, x_info_rule)) of
                                         RULE(renamed_lhs,renamed_rhs, x_info_rule) => (renamed_lhs,renamed_rhs)
                                        |_ => raise General.Fail("Error in OPTIMIZE.beta_reduction_in_match.\n")
				in
                    ORELSE(
                            ANDALSO( MATCH(lhs',term, x_info_rule), MATCH(pattern,rhs', x_info_rule), x_info_rule ) ,
                            MATCH(pattern, term, x_info_app),
							x_info_match
                          )
				end

	      | beta_reduce( expr ) = expr

	in
		ABSTRACT.bottom_up beta_reduce identity prog_expr
	end

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*

   References are pointers to strategic values. A reference permits a strategic value to be
   applied multiple times. For example, let s denote a reference to a strategic value v. Then
   the strategic expression

           (s <; s) t

   will have the following behavior:


   The mapL and mapR combinators are also mechanisms that can apply a strategic value
   multiple times.

   There are two mechanisms by which a reference can be bound to a strategic value.

    1. Explicit binding. An explicit binding can be specified within the conditional
       portion of a rule. This binding makes use of the operator ":=".

           lhs -> rhs if { .... s := value ... }

    2. Parameter passing. An implicit binding when a strategic value is passed as an argument
       either to:

        a. The combinator mapL
        b. The combinator mapR
        c. A recursively defined combinator (e.g., TDL).


*)
(* ------------------------------------------------------------------------------------------- *)
fun createRefs prog_expr =
	let
            val id_ref_list = ref [] : (string * ABSTRACT_REPRESENTATION.EXPR) list ref;

            (* ------------------------------------------------------------------------------------------- *)
            fun collectRef context  (t as BIND( IDENTIFIER (id, x_info), expr, _) ) =
																					let
																						val addr      = newAddress()
																						val ref_term  = ABSTRACT.makeRef(context, id, addr, x_info)
																					in
																						id_ref_list := (id, ref_term) :: !id_ref_list;
																						t
																					end

              | collectRef _  expr = expr

            (* ------------------------------------------------------------------------------------------- *)
            fun convertToRef id_ref_list (IDENTIFIER (id, x_info) ) =
																	let
																		fun replace( (id1,ref1)::rest) = if id = id1 then ref1 else replace(rest)
																		  | replace( []              ) = IDENTIFIER (id, x_info)
																	in
																		replace(id_ref_list)
																	end
              | convertToRef _ expr = expr

            (* ------------------------------------------------------------------------------------------- *)
			fun processDec( NON_RECURSIVE( IDENTIFIER (id, x_info_id), body, x_info_non_rec ) ) =
																	let
																		val _        = id_ref_list := [];
																		val _        = ABSTRACT.bottom_up (collectRef id) identity body;
																		val new_body = ABSTRACT.bottom_up (convertToRef (!id_ref_list)) identity body
																	in
																		NON_RECURSIVE(IDENTIFIER (id, x_info_id), new_body, x_info_non_rec)
																	end
(*
              | processDec( RECURSIVE(IDENTIFIER id, arg_list, body) =
*)
              | processDec expr            = expr

            (* ------------------------------------------------------------------------------------------- *)
	in
		ABSTRACT.bottom_up processDec identity prog_expr
	end

(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*

    0.a. Free variables (i.e., match variables) are not permitted. For example, if we have the
         declaration

            r: some_term

         then "some_term" must be a ground term. So a better choice for the label r in this declaration
         might be something like:

            my_constant: some_term


    0.b. A match should be understood as a generalized form of assignment as well as an operation
         capable of performing an equality check between ground terms. Furthermore, the right-hand
         side of a match should always be an expression whose evaluation yields a ground term.
         match variables, when present, may only occur on the left-hand side of the match operator.

         As a result, in any given scope a match variable may be bound only once. For example,
         assuming that <x>_1 is initially free then (in the expression below) the first occurrence
         of <x>_1 (a def) denotes a binding while the second (a use) denotes an equality comparison.

		<x>_1 = some andalso <x>_1 = other


         This forms the basis of the following kind of optimization:

		<x>_1 = some andalso <x>_1 = other
		==>
		<x>_1 = some andalso some = other


    0.c. The boolean operator "orelse" has special properties with respect to scope and matching.
         In particular, an orelse can be used to specificy multiple binding possibilities. In general,
         the question of which binding to use can only be answered at runtime.

         The following rewrite is possible:


         ((<pattern>_1 = expr1) orelse (<pattern>_1 = expr2)) andalso stuff
         ==>
         ((<pattern>_1 = expr1 andalso stuff) orelse (<pattern>_1 = expr2 andalso stuff))


          However, one must keep in mind that this rewrite could lead to an exponential increase in
          the size of the resulting condition. However, in practice, I believe that this
          rewrite could represent an optimization (under certain circumstances), since it
          paves the way for other optimizations (e.g., copy propagation). In practice, our
          group rarely uses orelse. However, some of the optimizations below introduce orelse
          expressions into the internal form, so it is unclear that the use of the above rewrite
          is practical (i.e., is practical to scale the concept to large expressions).


    0.d. (<pattern>_1 = expr1 andalso stuff) orelse other
         ==>
         sigma(stuff) orelse other

         assuming static_match(<pattern>_1,expr1) = sigma



    0.e. In the optimizations given below, when referencing the components of conditional rewrite rules,
         we will use primed versions of components to refer to the alpha-renamed versions of those
         components. For example:

         original: lhs -> rhs if cond
         original components: lhs, rhs, cond

         alpha_renamed: lhs' -> rhs' if cond'
         alpha_renamed components: lhs', rhs', cond'

(* ------------------------------------------------------------------------------------------- *)
    1. Inlining (non-recursive) label references with the strategies they are bound to does not
       require alpha conversion. The reason for this is that (conditional) rewrite rules
       define scope boundaries (much in the way that lambda abstractions define scope
       boundaries).


    2.a. General beta reduction (case 1: basic rewrite rule).

         ( <x>_1 = (lhs -> rhs)(t) )
         ==>
         ( (lhs' = t) andalso (<x>_1 = rhs') )
         orelse
         (<x>_1 = t)

    2.b. General beta reduction (case 2: conditional rewrite rule).

         ( <x>_1 = (lhs -> rhs if cond)(t) )
         ==>
         ( (lhs' = t) andalso cond' andalso (<x>_1 = rhs') )
         orelse
         (<x>_1 = t)


    2.c. Specialized beta reduction. A special case (leading to further optimization)
         arises when the term t contains at least as much information as lhs' (e.g., the match
         variable <expr>_lhs is matched with expr[:] <expr>_1 + 0 [:], but not the other way around)
         and it can be determined that the static_match lhs' = t will succeed. In this case, it becomes
         possible to substitute all parts of lhs' with corresponding parts of t. So we get something like:

         ( <pattern>_1 = (lhs -> rhs)(t) )
         ==>
         (<pattern>_1 = sigma(rhs'))  where sigma is the substitution resulting from: lhs' = t.



     3. Copy Propagation. Whenever a match can be (statically) performed, the given match can be removed
        and the resulting substitution can be applied to rest of the condition. However, care must be
        given to handling scoping issues (e.g., orelse) correctly.


        (expr_free = expr ...)
	==>
        sigma(...)   where static_match(expr_free,expr) = sigma

        Note that since this matching occurs during the (static) optimization phase, situations can arise
        in which match variables can (syntactically) appear both in expr_free and in expr. However, in reality
        (i.e., during runtime) the match variables in expr will be bound. For this reason, the static_match
        algorithm is slightly different than the runtime match algorithm.


     4. If static_match(<pattern>_1,expr1) = sigma, then

         (<pattern>_1 = expr1 andalso stuff) orelse other
         ==>
         sigma(stuff) orelse other




     5. Binary combinators

        (s1 op s2) op s3
        ==>
        s1 op (s2 op s3)


     5. <pattern>_1 = (unary(s1) op s2)(t)   where unary != hide  (Note that hide is extra-logical.)
        ==>
        <pattern>_1 = (s1 op s2)(t)



     6.a.1. <pattern>_1 = ((lhs -> rhs) <; s2)(t)
            ==>
            ((lhs' = t) andalso (<pattern>_1 = s2(rhs')))
            orelse
            (<pattern>_1 = s2(t))


     6.a.2. <pattern>_1 = ((lhs -> rhs if cond) <; s2)(t)
            ==>
            ((lhs' = t) andalso cond' andalso (<pattern>_1 = s2(rhs')))
            orelse
            (<pattern>_1 = s2(t))


     6.b.1. <pattern>_1 = ((lhs -> rhs) <+ s2)(t)
            ==>
            ((lhs' = t) andalso (<pattern>_1 = rhs'))
            orelse
            (<pattern>_1 = s2(t))


     6.b.2. <pattern>_1 = ((lhs -> rhs if cond) <+ s2)(t)
            ==>
            ((lhs' = t) andalso cond' andalso (<pattern>_1 = rhs'))
            orelse
            (<pattern>_1 = s2(t))




*)
(* ------------------------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------------------------- *)
(*

    form_1 = The identifiers in the formal parameter list of recursive definitions are
             uniquely renamed (from a global perspective) and recursive definitions are
             rewritten in a corresponding fashion. At this time, it is assumed (though not checked)
             that formal parameters in recursive definitions are linear.

    form_2 = All ref identifiers are converted into an internal format of the form:

               REF(
                     id
                     {STRATEGIC_CONTEXT = strategic_context, INDEX = index}
                  )

               where strategic_context is the name of the entity (e.g., non_recursive/recursive definition)
               in which the id occurs and INDEX


    form_3 = all non-recursive definitions are inlined. The resulting program should consist of
             the following:

                a. One non-recursive definition whose label is "main"
                b. Zero or more recursive definitions.


    form_4 = Iterator term structures are created. For example, suppose the arity of myTDL is known to be 1,
             then we have the following:

             APP( IDENTIFIER myTDL, s )
             ==>
             ITERATOR( IDENTIFIER myTDL, [s]  )

             On the other hand, if we know the arity of myIterator to be, say 2, then we have the following:

             APP( APP( IDENTIFIER myIterator, s1 ), s2 )
             ==>
             ITERATOR( IDENTIFIER myIterator, [s1,s2]  )



    form_5 = A simple beta reduction is performed on applications but only within the context
             of a match -- which only occurs within a condition. The basic idea is:

                 expr1 = (lhs -> rhs)(t)

                 ==>

                 ( (lhs' = t) andalso expr1 = rhs') orelse (expr1 = t)

	     where (lhs', rhs') is an alpha-renamed form of (lhs,rhs). Clearly, this idea can
             be extended.

*)
(* ------------------------------------------------------------------------------------------- *)
fun extractUserDefinedLibrarySignature (PROG (decl_list, x_info) ) =
	let
		fun auxFind( SIGNATURE data :: rest) 		= (SIGNATURE data, rest)
		  | auxFind( RECURSIVE data :: rest) 		= 	let
															val (sig_term, term_list) = auxFind(rest)
														in
															(sig_term, RECURSIVE data :: term_list)
														end
		  | auxFind( NON_RECURSIVE data :: rest)	= 	let
															val (sig_term, term_list) = auxFind(rest)
														in
															(sig_term, NON_RECURSIVE data :: term_list)
														end
		  | auxFind [] 								= (FALSE, [])
		  | auxFind _ = raise General.Fail("Error: OPTIMIZE.extractUserDefinedLibrarySignature.auxFind\n\n")

		val (library_sig, decl_list2) =	auxFind decl_list
	in
		(library_sig, PROG( decl_list2, x_info ) )
	end
  | extractUserDefinedLibrarySignature _ = raise General.Fail("Error: OPTIMIZE.extractUserDefinedLibrarySignature\n\n")

(* ------------------------------------------------------------------------------------------- *)
(* datatype is Grammar_AbstractSyntax.grammar; *)

fun printNonterminals( GRAMMAR {precassoc_rules = precassoc_rule_list, production_list = production_rule_list} ) =
	let
		fun aux( {name = name, filepos = filepos, regex = regular_expression, precsymb_opt = symbol_option} :: rest ) = (print(name ^ "\n"); aux rest)
		  | aux [] = ()
	in
		aux production_rule_list
	end

(* ------------------------------------------------------------------------------------------- *)
fun optimize ( x_precision, x_verbosity, grammar, expr ) =
					let
						val _ = print("\nPerfoming static analysis and optimization....\n");
						val (lib, expr_0) = extractUserDefinedLibrarySignature expr

                        val form_0 = TYPECHECK.typeCheck lib expr_0 grammar {precision=x_precision, verbosity=x_verbosity}
                        (*val form_0 = expr_0*)

                        val form_1 = case alpha_rename_defs form_0 of
                                          (PROG (expr_list_renamed, x_info) ) => (PROG (expr_list_renamed, x_info))
                                        | _                                   => raise General.Fail("Error 1 in OPTIMIZE.optimize.\n")
                        val form_2 = createRefs form_1
                        val form_3 = inline_non_rec form_2
                        val form_4 = form_3
                        val form_5 = beta_reduction_in_match form_4
                        val _      = print("Completed optimization.\n")	
                    in
                        form_4
                    end

end; (* structure *)
(* ------------------------------------------------------------------------------------------- *)
