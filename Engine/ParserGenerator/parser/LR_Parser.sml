val ## = Vector.fromList; (* SML/NJ shorthand hack *)

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   filename      : LR_Parser.sml
   programmer    : Gary Fuehrer
   last modified : 06/25/2002

   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)


signature TOKEN =
  sig
    type token
    val toAtom : token -> Atom.atom
    val lexer : (int -> string) -> unit -> token
  end

signature PARSE_TREE =
  sig
    type token
    type parse_tree
    val terminalNode : token -> parse_tree
    val nonterminalNode : {symbkey:Atom.atom, trees:parse_tree list} -> parse_tree
  end

signature PARSE_EVENTS =
  sig
    type token
    type parse_tree
    type parse_result
    val initialParseResult : unit -> parse_result
    val parseSuccessEventHandler : parse_tree * parse_result -> parse_result
    val tokenNotFoundEventHandler : {token:token, expected:Atom.atom list} * parse_result -> parse_result
  end

functor LR_ParserFn
  (
    structure Token : TOKEN
    structure ParseTree : PARSE_TREE
    structure ParseEvents : PARSE_EVENTS

    sharing type ParseEvents.token = ParseTree.token = Token.token
    sharing type ParseEvents.parse_tree = ParseTree.parse_tree
  )
  :> PARSER where type parse_result = ParseEvents.parse_result =
  
  (* ----------------------------------------------------------------------------------------------------------------------- *)
  struct
  
    structure LookaheadSet = BitVectorSetFn(AtomMap)

    structure WordMap = RedBlackMapFn(struct type ord_key = word val compare = Word.compare end)
    structure WordSet = RedBlackSetFn(struct type ord_key = word val compare = Word.compare end)

    structure DfaStateSet = RedBlackSetFn(struct type ord_key = WordSet.set val compare = WordSet.compare end)

    structure DfaStateMap = RedBlackMapFn(struct type ord_key = WordSet.set val compare = WordSet.compare end)

    structure State1Set = RedBlackSetFn(struct type ord_key = LookaheadSet.set WordMap.map val compare = WordMap.collate(LookaheadSet.compareU) end)

    structure State1Map = RedBlackMapFn(struct type ord_key = LookaheadSet.set WordMap.map val compare = WordMap.collate(LookaheadSet.compareU) end)

    fun makeMultiMapAddFun(find, insert, union)(set)(key, map) =
        insert(map, key, case find(map, key) of SOME set' => union(set', set) | _ => set)

    fun makeGetElementFromSetFun(find, delete)(set) =
        case find(fn _ => true)(set) of
          SOME item => SOME(item, delete(set, item))
        | _ => NONE

    fun makeGetElementFromMapFun(firsti, remove)(map) =
        case firsti(map) of
          SOME(item as (key, _)) => let val (map', _) = remove(map, key) in SOME(item, map') end
        | _ => NONE

    fun makeClosureFun(getElement, empty_container, processElement)(initial_container) =
      let
        fun closure'(finished_container, working_container) =
          case getElement(working_container) of
            NONE => finished_container
          | SOME element__working_container' =>
            closure'(processElement(finished_container, element__working_container'))
       in
          closure'(empty_container, initial_container)
      end

(* VLW
	(* ----------------------------------------------------------------------------------------------------------------------- *)
    structure Grammar_AbstractSyntax =
      struct
        type filepos = {left:word, right:word}
        type symbol = {name : string, delim_opt : char option, filepos : filepos}

        datatype
          regular_expression =
            SYMBOL of symbol
          | SEQUENCE of regular_expression list
          | CHOICE of regular_expression * regular_expression
          | REPETITION of regular_expression

        datatype
          precassoc_rule =
            NON_ASSOCIATIVE of symbol list
          | LEFT_ASSOCIATIVE of symbol list
          | RIGHT_ASSOCIATIVE of symbol list

        type production = {name : string, filepos : filepos, regex : regular_expression, precsymb_opt : symbol option}

        datatype grammar = GRAMMAR of {precassoc_rules : precassoc_rule list, production_list : production list}
      end
	(* ----------------------------------------------------------------------------------------------------------------------- *)
*)
    type grammar = Grammar_AbstractSyntax.grammar

    structure GrammarParser = GrammarParserFn(structure AST = Grammar_AbstractSyntax)

    val nonterminalDecoration = "\^A"
    val literalTermDecoration = ""

    fun makeDecorateSymbKey(isNonterminalTest) = fn {name, delim_opt, filepos=_} => Atom.atom( (case delim_opt of SOME #"<" => nonterminalDecoration | SOME #"\"" => literalTermDecoration | _ => if isNonterminalTest(name) then nonterminalDecoration else "") ^ name )

    fun undecorateNonterminal(symbkey) = String.extract(Atom.toString symbkey, String.size nonterminalDecoration, NONE)

	(* ----------------------------------------------------------------------------------------------------------------------- *)	
    fun processProductions(prodlist) =
      let
        fun processProduction(nonterminals) =
        let
          val decorateSymbKey = makeDecorateSymbKey(fn name => AtomSet.member(nonterminals, Atom.atom(nonterminalDecoration^name)))
         in
          fn ({name, filepos=prodpos as {left=prodleft, right=prodright}, regex, precsymb_opt}, {grammar, pass1}) =>
          let
            val prodinfo = {prodkey=Atom.atom(nonterminalDecoration^name), prodpos=prodleft}

            open Grammar_AbstractSyntax

            val addWordSetToWordMultiMap = makeMultiMapAddFun(WordMap.find, WordMap.insert, WordSet.union)
            fun
              process_regex(SYMBOL(symb as {filepos as {left=leftpos, right=rightpos}, ...}), {symbols, posinfo, nextpos, prevpos}) =
              let
                val symbkey = decorateSymbKey(symb)
               in
                {
                  synthesize =
                  {
                    epsilon = false,
                    firstpos = WordSet.singleton(leftpos),
                    lastpos = WordSet.singleton(leftpos),
                    filepos = filepos
                  },

                  accumulate =
                  {
                    symbols = if name = "" then symbols else AtomSet.add(symbols, symbkey),
                    posinfo = WordMap.insert(posinfo, leftpos, {symbol=symbkey, prodinfo=prodinfo}),
                    nextpos = WordMap.insert(nextpos, leftpos, WordSet.empty),
                    prevpos = WordMap.insert(prevpos, leftpos, WordSet.empty)
                  }
                }
              end

            | process_regex(SEQUENCE nil, accumulate) =
                {
                  synthesize =
                  {
                    epsilon = true,
                    firstpos = WordSet.empty,
                    lastpos = WordSet.empty,
                    filepos = {left=Word.fromInt(~1), right=0w0}
                  },

                  accumulate = accumulate
                }

            | process_regex(SEQUENCE(regex::regex_list), accumulate) =
              let
                val {synthesize={epsilon=epsilon1, firstpos=firstpos1, lastpos=lastpos1, filepos={left=leftpos1, right=rightpos1}}, accumulate}
                  = process_regex(regex, accumulate)

                val {synthesize={epsilon=epsilon2, firstpos=firstpos2, lastpos=lastpos2, filepos={left=leftpos2, right=rightpos2}}, accumulate as {symbols, posinfo, nextpos, prevpos}}
                  = process_regex(SEQUENCE regex_list, accumulate)
               in
                {
                  synthesize =
                  {
                    epsilon = epsilon1 andalso epsilon2,
                    firstpos = WordSet.union(firstpos1, if epsilon1 then firstpos2 else WordSet.empty),
                    lastpos = WordSet.union(if epsilon2 then lastpos1 else WordSet.empty, lastpos2),
                    filepos = {left=Word.min(leftpos1, leftpos2), right=Word.max(rightpos1, rightpos2)}
                  },

                  accumulate =
                  {
                    symbols = symbols,
                    posinfo = posinfo,
                    nextpos = WordSet.foldl (addWordSetToWordMultiMap firstpos2) nextpos lastpos1,
                    prevpos = WordSet.foldl (addWordSetToWordMultiMap lastpos1) prevpos firstpos2
                  }
                }
              end

            | process_regex(CHOICE(regex_a, regex_b), accumulate) =
              let
                val {synthesize={epsilon=epsilon_a, firstpos=firstpos_a, lastpos=lastpos_a, filepos={left=leftpos_a, right=rightpos_a}}, accumulate}
                  = process_regex(regex_a, accumulate)

                val {synthesize={epsilon=epsilon_b, firstpos=firstpos_b, lastpos=lastpos_b, filepos={left=leftpos_b, right=rightpos_b}}, accumulate}
                  = process_regex(regex_b, accumulate)
               in
                {
                  synthesize =
                  {
                    epsilon = epsilon_a orelse epsilon_b,
                    firstpos = WordSet.union(firstpos_a, firstpos_b),
                    lastpos = WordSet.union(lastpos_a, lastpos_b),
                    filepos = {left=Word.min(leftpos_a, leftpos_b), right=Word.max(rightpos_a, rightpos_b)}
                  },

                  accumulate = accumulate
                }
              end

            | process_regex(REPETITION(regex), accumulate) =
              let
                val {synthesize as {firstpos, lastpos, filepos, ...}, accumulate={symbols, posinfo, nextpos, prevpos}}
                  = process_regex(regex, accumulate)
               in
                {
                  synthesize =
                  {
                    epsilon = true,
                    firstpos = firstpos,
                    lastpos = lastpos,
                    filepos = filepos
                  },

                  accumulate =
                  {
                    symbols = symbols,
                    posinfo = posinfo,
                    nextpos = WordSet.foldl (addWordSetToWordMultiMap firstpos) nextpos lastpos,
                    prevpos = WordSet.foldl (addWordSetToWordMultiMap lastpos) prevpos firstpos
                  }
                }
              end

            val leftmarker = SYMBOL{name="", delim_opt=SOME #"\"", filepos={left=prodleft, right=prodleft}}

            val rightmarker = SYMBOL{name="", delim_opt=SOME #"\"", filepos={left=prodright + 0w1, right=prodright + 0w1}}

            val precsymbkey_opt = case precsymb_opt of SOME symb => SOME(decorateSymbKey symb) | _ => NONE
           in
            {
              grammar = AtomMap.insert(grammar, #prodkey prodinfo, {filepos=prodpos, regex=regex, precsymbkey_opt=precsymbkey_opt}::
                (case AtomMap.find(grammar, #prodkey prodinfo) of SOME l => l | _ => [])),

              pass1 = #accumulate(process_regex(SEQUENCE[leftmarker, regex, rightmarker], pass1))
            }
          end
        end

        val lhs_symbols = AtomSet.addList(AtomSet.empty, List.map (Atom.atom o (fn s=>nonterminalDecoration^s) o #name) prodlist)

        val empty_pass1 = {symbols=lhs_symbols, posinfo=WordMap.empty, nextpos=WordMap.empty, prevpos=WordMap.empty}

        val {grammar, pass1=pass1 as {symbols, posinfo, nextpos, prevpos}} = foldl (processProduction lhs_symbols) {grammar=AtomMap.empty, pass1=empty_pass1} prodlist

        fun createSchemaProductions(symbkey, {prodlist, lastpos}) =
          let
            val regex = Grammar_AbstractSyntax.SYMBOL{name="!#schema_variable_" ^ (undecorateNonterminal symbkey), delim_opt=SOME #"\"", filepos={left=lastpos-0w2, right=lastpos-0w1}}
           in
            {prodlist={name=undecorateNonterminal symbkey, filepos={left=lastpos-0w5, right=lastpos-0w4}, regex=regex, precsymb_opt=NONE}::prodlist,
             lastpos=lastpos-0w6}
          end

        fun extractSchemaVariable symbkey = Atom.atom(nonterminalDecoration ^ String.extract(Atom.toString symbkey, String.size "!#schema_variable_", NONE))

        val schemavars = AtomSet.map extractSchemaVariable (AtomSet.filter ((String.isPrefix "!#schema_variable_") o Atom.toString) symbols)

        val nonterminals = AtomSet.filter ((String.isPrefix nonterminalDecoration) o Atom.toString) symbols

        val {prodlist, lastpos} = AtomSet.foldr createSchemaProductions {prodlist=nil, lastpos=0w0} (AtomSet.difference(nonterminals, schemavars))

        val {grammar, pass1={symbols, posinfo, nextpos, prevpos}} = foldl (processProduction nonterminals) {grammar=grammar, pass1=pass1} prodlist

        val terminals = AtomSet.difference(symbols, nonterminals)
       in
        {
          grammar=grammar,
          symbols=symbols,
          terminals = terminals,
          nonterminals = nonterminals,
          posinfo = posinfo,
          nextpos = nextpos,
          prevpos = prevpos
        }
      end
	(* ----------------------------------------------------------------------------------------------------------------------- *)
	
    fun processPrecAssocRules(nonterminals)(precassoc_rules) =
      let
        val decorateSymbKey = makeDecorateSymbKey(fn name => AtomSet.member(nonterminals, Atom.atom(nonterminalDecoration^name)))

	    
        fun processPrecAssocRule(precassoc_rule, {symbprec, precassoc}) =
          let
            fun processAssocSymbol{prec, assoc}(symb, symbprec) =
              let
                val symbkey = decorateSymbKey(symb)
               in
                case AtomMap.find(symbprec, symbkey) of
                  SOME _ => raise General.Fail("processPrecAssocRules: the prec/assoc of '" ^ (Atom.toString symbkey) ^ "' is specified more than once.")
                | _ => AtomMap.insert(symbprec, symbkey, prec)
              end

            val {assoc, symb_list} = case precassoc_rule of
              Grammar_AbstractSyntax.NON_ASSOCIATIVE symb_list => {assoc=NONE, symb_list=symb_list}
            | Grammar_AbstractSyntax.LEFT_ASSOCIATIVE symb_list => {assoc=SOME false, symb_list=symb_list}
            | Grammar_AbstractSyntax.RIGHT_ASSOCIATIVE symb_list => {assoc=SOME true, symb_list=symb_list}
           in
            {symbprec=foldl (processAssocSymbol{prec=Word.fromInt(Vector.length precassoc), assoc=assoc}) symbprec symb_list, precassoc=Vector.concat[precassoc, ##[assoc]]}
          end
       in
        foldl processPrecAssocRule {symbprec=AtomMap.empty, precassoc= ##[NONE]} precassoc_rules
      end

    fun processEpsilons{grammar, nonterminals} =
      let
        val getAtomFromSet = makeGetElementFromSetFun(AtomSet.find, AtomSet.delete)

        val decorateSymbKey = makeDecorateSymbKey(fn name => AtomSet.member(nonterminals, Atom.atom(nonterminalDecoration^name)))

        fun process_epsilon({finished_epsilons, unknown_epsilons}, (prodkey, working_epsilons)) =
          let
            open Grammar_AbstractSyntax

            fun
              regexHasEpsilon(SYMBOL(symb as {name, filepos={left=leftpos, right=_}, ...})) = let
                val symbkey = decorateSymbKey(symb)
               in
                if leftpos = 0w0 then SOME false
                else if name = "" then SOME true
                else case AtomMap.find(grammar, symbkey) of
                  NONE => SOME false
                | _ => AtomMap.find(finished_epsilons, symbkey)
              end
            | regexHasEpsilon(SEQUENCE nil) =
                SOME true

            | regexHasEpsilon(SEQUENCE(regex::regex_list)) =
              (
                case regexHasEpsilon(regex) of
                  SOME true => regexHasEpsilon(SEQUENCE regex_list)
                | x => x
              )
            | regexHasEpsilon(CHOICE(regex_a, regex_b)) =
              (
                case (regexHasEpsilon(regex_a), regexHasEpsilon(regex_b)) of
                  (SOME true, _) => SOME true
                | (_, SOME true) => SOME true
                | (SOME false, SOME false) => SOME false
                | _ => NONE
               )
            | regexHasEpsilon(REPETITION _) =
                SOME true
           in
            case AtomMap.find(grammar, prodkey) of
              SOME prodlist =>
              let
                fun choiceify({regex, filepos=_, precsymbkey_opt=_}, accum_regex) = CHOICE(regex, accum_regex)

                val initial_regex = SYMBOL{name="", delim_opt=SOME #"\"", filepos={left=0w0, right=0w0}}
               in
                case regexHasEpsilon(foldl choiceify initial_regex prodlist) of
                  SOME boolean => ({finished_epsilons=AtomMap.insert(finished_epsilons, prodkey, boolean), unknown_epsilons=AtomSet.empty}, AtomSet.union(working_epsilons, unknown_epsilons))
                | _ => ({finished_epsilons=finished_epsilons, unknown_epsilons=AtomSet.add(unknown_epsilons, prodkey)}, working_epsilons)
              end
            | _ => raise General.Fail("productionHasEpsilon: prodkey not in grammar")
          end

        val epsilonClosure = makeClosureFun(getAtomFromSet, {finished_epsilons=AtomMap.empty, unknown_epsilons=AtomSet.empty}, process_epsilon)

        val {finished_epsilons, unknown_epsilons} = epsilonClosure(nonterminals)
       in
        AtomSet.foldl (fn (key, map) => AtomMap.insert(map, key, false)) finished_epsilons unknown_epsilons
      end

    fun findInfo{grammar}({prodinfo={prodkey, prodpos}, symbol}) =
      let
        val prodlist = case AtomMap.find(grammar, prodkey) of SOME thing => thing
            | _ => raise General.Fail("BUG: findInfo got a key not found in grammar")
        fun find_prod_in_list{filepos={left=leftpos, right=_}, regex=_, precsymbkey_opt=_} = prodpos = leftpos
        val {filepos, regex, precsymbkey_opt} = case List.find find_prod_in_list prodlist of SOME thing => thing
            | _ => raise General.Fail("BUG: findInfo given a pos not found in prodlist")
       in
        {prodkey=prodkey, symbol=symbol, filepos=filepos, regex=regex, precsymbkey_opt=precsymbkey_opt}
      end

    fun findPosInfo{grammar, posinfo}(pos) =
      (
        case WordMap.find(posinfo, pos) of SOME infopos => findInfo{grammar=grammar}(infopos)
        | _ => raise General.Fail("BUG: findPosInfo given a pos not found in posinfo")
      )

    val addWordSetToAtomMultiMap = makeMultiMapAddFun(AtomMap.find, AtomMap.insert, WordSet.union)

    fun processDFAs{grammar, posinfo, prevpos} =
      let
        fun addGotoOfPosToActions(pos, actions) =
          let
            val {symbol, filepos, ...} = findPosInfo{grammar=grammar, posinfo=posinfo}(pos)

            val posgoto = case WordMap.find(prevpos, pos) of SOME thing => thing
            | _ => raise General.Fail("BUG: addGotoOfPosToActions: No such pos in nextset")
           in
            if pos = #left filepos then actions else
            addWordSetToAtomMultiMap(posgoto)(symbol, actions)
          end

        fun dfaStateProcess(finished_states, (kernel, working_states)) =
          (
            if DfaStateMap.inDomain(finished_states, kernel) then (finished_states, working_states)
            else
              let
                val next_id = Word.fromInt(DfaStateMap.numItems(finished_states))

                val actions = WordSet.foldl addGotoOfPosToActions AtomMap.empty kernel

                val working_states' = AtomMap.foldl DfaStateSet.add' working_states actions
               in
                (DfaStateMap.insert(finished_states, kernel, {id=next_id, actions=actions}), working_states')
              end
          )

        val getDfaStateFromSet = makeGetElementFromSetFun(DfaStateSet.find, DfaStateSet.delete)

        val dfaStateClosure = makeClosureFun(getDfaStateFromSet, DfaStateMap.empty, dfaStateProcess)

        fun processDFA({filepos={left=_, right=rightpos}, regex=_, precsymbkey_opt=_}, DFAs) =
          let
            val prevset = case WordMap.find(prevpos, rightpos + 0w1) of SOME thing => thing
            | _ => raise General.Fail("BUG: processDFA: No such pos in prevpos")
           in
            WordMap.insert(DFAs, rightpos + 0w1, dfaStateClosure(DfaStateSet.singleton(prevset)))
          end
       in
        fn (prodkey, prodlist, DFAs) => foldl processDFA DFAs prodlist
      end

    val getWordFromSet = makeGetElementFromSetFun(WordSet.find, WordSet.delete)

    fun processFollowPos{grammar, terminals, posinfo, nextpos, epsilons} =
      let
        fun firstProcess(finished_firsts, (pos, working_firsts)) =
          (
            if WordSet.member(finished_firsts, pos) then (finished_firsts, working_firsts)
            else
              (
                WordSet.add(finished_firsts, pos),

                case WordMap.find(posinfo, pos) of
                  SOME {symbol, prodinfo=_} =>
                  (
                    case AtomMap.find(grammar, symbol) of
                      SOME prodlist =>
                      let
                        fun add_first_pos({filepos={left=startpos, right=_}, regex=_, precsymbkey_opt=_}, set) =
                            WordSet.union(set,
                                case WordMap.find(nextpos, startpos) of SOME nextset => nextset
                                | _ => raise General.Fail("BUG: addFirstPos: No such startpos")
                              )

                        val working_firsts' = foldl add_first_pos working_firsts prodlist
                       in
                        case AtomMap.find(epsilons, symbol) of
                          SOME false => working_firsts'
                        | SOME true =>
                          let
                            val next_firsts = case WordMap.find(nextpos, pos) of SOME thing => thing
                            | _ => raise General.Fail("BUG: firstProcess given a pos not found in nextpos")
                           in
                            WordSet.union(working_firsts', next_firsts)
                          end
                        | _ => raise General.Fail("BUG: firstProcess found a nonterminal symbol not found in epsilons")
                      end
                    | _ => working_firsts
                  )
                | _ => raise General.Fail("BUG: firstProcess given a pos not found in posinfo")
              )
          )

        val firstClosure = makeClosureFun(getWordFromSet, WordSet.empty, firstProcess)

        fun addFirstClosureTerminalsOfNextPos(pos, infopos, followpos) =
          let
            val nextset = case WordMap.find(nextpos, pos) of SOME nextset => nextset
                | _ => raise General.Fail("BUG: addFirstClosureOfNextPos given a pos not found in nextpos")

            val firstNextPos = firstClosure(nextset)

            fun add_terminals_of_pos(pos, set) =
              (
                case WordMap.find(posinfo, pos) of
                  SOME {symbol, prodinfo=_} =>
                    if AtomSet.member(terminals, symbol)
                    then LookaheadSet.add(set, symbol) else set
                | _ => raise General.Fail("BUG: addFirstClosureOfNextPos: found a pos not in posinfo")
              )

            val {filepos, ...} = findInfo{grammar=grammar}(infopos)

            val firstNextTerms = WordSet.foldl add_terminals_of_pos LookaheadSet.empty firstNextPos

            val firstNextTermsFun = if WordSet.member(firstNextPos, (#right filepos) + 0w1)
                then fn propigated => LookaheadSet.union(firstNextTerms, propigated)
                else fn _ => firstNextTerms
           in
            WordMap.insert(followpos, pos, firstNextTermsFun)
          end
       in
        WordMap.foldli addFirstClosureTerminalsOfNextPos WordMap.empty posinfo
      end

    val addLookaheadSetToWordMap = makeMultiMapAddFun(WordMap.find, WordMap.insert, LookaheadSet.union)

    fun addFirstPosToKernel1{nextpos, lookaheads}({filepos={left=startpos, right=_}, regex=_, precsymbkey_opt=_}, kernel1) =
        case WordMap.find(nextpos, startpos) of SOME nextset =>
          WordSet.foldl (addLookaheadSetToWordMap lookaheads) kernel1 nextset
        | _ => raise General.Fail("BUG: addFirstPosToKernel1: No such startpos")

    fun getStartState{nextpos}(prodlist) =
        foldl (addFirstPosToKernel1{nextpos=nextpos, lookaheads=LookaheadSet.singleton(Atom.atom(""))}) WordMap.empty prodlist

    fun processPDA{precass={symbprec, precassoc}, grammar, posinfo, nextpos, followpos} =
      let
        fun item1Process(finished_items, ((item0, lookaheads), working_items)) =
          let
            val finished_lookaheads = case WordMap.find(finished_items, item0) of SOME thing => thing | _ => LookaheadSet.empty

            val new_lookaheads = LookaheadSet.difference(lookaheads, finished_lookaheads)
           in
            if LookaheadSet.isEmpty(new_lookaheads) then (finished_items, working_items)
            else
              (
                WordMap.insert(finished_items, item0, LookaheadSet.union(finished_lookaheads, new_lookaheads)),

                case WordMap.find(posinfo, item0) of
                  SOME {symbol, prodinfo=_} =>
                  (
                    case AtomMap.find(grammar, symbol) of
                      SOME prodlist =>
                      (
                        case WordMap.find(followpos, item0) of
                          SOME followpos_fun => foldl (addFirstPosToKernel1{nextpos=nextpos, lookaheads=followpos_fun new_lookaheads}) working_items prodlist
                        | _ => raise General.Fail("BUG: item1Process found an item0 not found in followpos")
                      )
                    | _ => working_items
                  )
                | _ => raise General.Fail("BUG: item1Process given a pos not found in posinfo")
              )
          end

        val getItem1FromMap = makeGetElementFromMapFun(WordMap.firsti, WordMap.remove)

        val item1Closure = makeClosureFun(getItem1FromMap, WordMap.empty, item1Process)

        fun addGotoOfItem1ToActions(item0, lookaheads, {shift_items, reduce_items}) =
          let
            val {symbol, filepos, ...} = findPosInfo{grammar=grammar, posinfo=posinfo}(item0)
           in
            if item0 = (#right filepos) + 0w1
            then
              {
                shift_items=shift_items,

                reduce_items=LookaheadSet.foldU (addWordSetToAtomMultiMap(WordSet.singleton item0)) reduce_items lookaheads
              }
            else
              let
                val kernel = case AtomMap.find(shift_items, symbol) of SOME thing => thing | _ => WordMap.empty

                val kernel' = case WordMap.find(nextpos, item0) of SOME nextset =>
                  WordSet.foldl (addLookaheadSetToWordMap lookaheads) kernel nextset
                | _ => raise General.Fail("BUG: addGotoOfItem1ToActions: No such item0 in nextset")
               in
                {shift_items=AtomMap.insert(shift_items, symbol, kernel'), reduce_items=reduce_items}
              end
          end

        fun addStateIndex(state_fun)(symbkey, fun_arg, (names, {state_to_index, index_to_state, working_states})) =
          let
            val state = state_fun(fun_arg)

            val {istate, state_to_index, index_to_state} = case State1Map.find(state_to_index, state) of
              SOME istate => {istate=istate, state_to_index=state_to_index, index_to_state=index_to_state}
            | _ =>
              let
                val istate = Word.fromInt(Vector.length(index_to_state))
               in
                {
                  istate = istate,
                  state_to_index = State1Map.insert(state_to_index, state, istate),
                  index_to_state = Vector.concat[index_to_state, ##[state]]
                }
              end
           in
            (
              AtomMap.insert(names, symbkey, istate),

              {
                state_to_index = state_to_index,
                index_to_state = index_to_state,
                working_states = WordSet.add(working_states, istate)
              }
            )
          end

        fun state1Process(finished_states, (ikernel, working_stuff)) =
          (
            if WordMap.inDomain(finished_states, ikernel) then (finished_states, working_stuff)
            else
              let
                fun applyPrecAssocRules(symbkey, _, actions as {shift_items, reduce_items}) =
                  case AtomMap.find(symbprec, symbkey) of
                    SOME shift_prec =>
                      let
                        fun reductionPrecedence{default}(item0) =
                          let
                            val {prodkey, precsymbkey_opt, ...} = findPosInfo{grammar=grammar, posinfo=posinfo}(item0)

                            val prec_opt = case precsymbkey_opt of
                              SOME precsymbkey => AtomMap.find(symbprec, precsymbkey)
                            | _ => NONE
                           in
                            case prec_opt of
                              SOME prec => prec
                            | _ =>
                              case AtomMap.find(symbprec, prodkey) of
                                SOME prec => prec
                              | _ => default
                          end
                       in
                        case AtomMap.find(reduce_items, symbkey) of
                          SOME item0set => let
                            val minreduce_prec = WordSet.foldl Word.min (0w0-0w1) (WordSet.map (reductionPrecedence{default=0w0}) item0set)
                            val maxreduce_prec = WordSet.foldl Word.max (0w0) (WordSet.map (reductionPrecedence{default=0w0-0w1}) item0set)
                           in
                            if shift_prec < minreduce_prec then
                              {shift_items= #1(AtomMap.remove(shift_items, symbkey)), reduce_items=reduce_items}
                            else if shift_prec > maxreduce_prec then
                              {shift_items=shift_items, reduce_items= #1(AtomMap.remove(reduce_items, symbkey))}
                            else case Vector.sub(precassoc, Word.toInt shift_prec) of
                              SOME false => if shift_prec = minreduce_prec then
                                  {shift_items= #1(AtomMap.remove(shift_items, symbkey)), reduce_items=reduce_items}
                                else actions
                            | SOME true => if shift_prec = maxreduce_prec then
                                  {shift_items=shift_items, reduce_items= #1(AtomMap.remove(reduce_items, symbkey))}
                                else actions
                            | _ => actions
                          end
                        | _ => actions
                      end
                  | _ => actions

                val closure = item1Closure(Vector.sub(#index_to_state working_stuff, Word.toInt ikernel))

                val {shift_items, reduce_items} = WordMap.foldli addGotoOfItem1ToActions {shift_items=AtomMap.empty, reduce_items=AtomMap.empty} closure

                val (shift_items', working_stuff') = AtomMap.foldli (addStateIndex(fn state => state)) (AtomMap.empty, working_stuff) shift_items

                val actions = AtomMap.foldli applyPrecAssocRules {shift_items=shift_items', reduce_items=reduce_items} shift_items'
               in
                (WordMap.insert(finished_states, ikernel, actions), working_stuff')
              end
          )

        fun getStateIndexFromWorkingStuff{state_to_index, index_to_state, working_states} =
          (
            case getWordFromSet(working_states) of
              SOME(istate, working_states') => SOME(istate, {state_to_index=state_to_index, index_to_state=index_to_state, working_states=working_states'})
            | _ => NONE
          )

        val state1Closure = makeClosureFun(getStateIndexFromWorkingStuff, WordMap.empty, state1Process)

        val initial_work = (AtomMap.empty, {state_to_index=State1Map.empty, index_to_state= ##[], working_states=WordSet.empty})

        val (shift_items', working_set') = AtomMap.foldli (addStateIndex(getStartState{nextpos=nextpos})) initial_work grammar
       in
        {pda_start=shift_items', PDA=state1Closure(working_set')}
      end

    fun parse{precass, grammar, posinfo, nextpos, prevpos, DFAs, PDA, pda_start}{start_symbol} =
      let
        datatype parse_value = T of ParseTree.token | N of ParseTree.parse_tree list

        val start_symbkey = Atom.atom(nonterminalDecoration^start_symbol)

        val eof_symbkey = Atom.atom ""

        val stack_bottom =
          {
            symbval= {symbkey=eof_symbkey, value=N nil},

            pda_state= case AtomMap.find(pda_start, start_symbkey) of SOME istate => istate
                       | _ => raise General.Fail("Error: No such start symbol '" ^ start_symbol ^ "'")
          }

        fun
          pop_stack(nil) = (stack_bottom, nil)
        | pop_stack(h::t) = (h, t)

        fun
          pop_input{tokens, push=NONE} =
          let
            val (token, tokens') = Stream.get(tokens)
           in
            ({symbkey=Token.toAtom(token), value=T token}, {tokens=tokens', push=NONE}, false)
          end
        | pop_input{tokens, push=SOME(symbval as {symbkey, value=_})} = (symbval, {tokens=tokens, push=NONE}, Atom.sameAtom(symbkey, start_symbkey) andalso
          let
            val (token, _) = Stream.get(tokens)
           in
            Atom.sameAtom(Token.toAtom(token), eof_symbkey)
          end)

        fun
          push_input({tokens, push=NONE}, symbval) = {tokens=tokens, push=SOME symbval}
        | push_input _ = raise General.Fail("BUG: push_input: already something pushed")

        fun
          make_value{symbkey=_, value=T token} = ParseTree.terminalNode(token)
        | make_value{symbkey, value=N trees} = ParseTree.nonterminalNode{symbkey=Atom.atom(undecorateNonterminal symbkey), trees=trees}

        fun
          runPDA{stack, input, result} =
          let
            val ({symbval=_, pda_state}, stack') = pop_stack(stack)

            val (symbval as {symbkey, value}, input', accept) = pop_input(input)
           in
            case WordMap.find(PDA, pda_state) of
              SOME {shift_items, reduce_items} =>
              let
                val result = if accept andalso length(stack) <= 0
                  then ParseEvents.parseSuccessEventHandler(make_value symbval, result)
                  else case AtomMap.find(shift_items, symbkey) of
                    SOME pda_state' => runPDA{stack={symbval=symbval, pda_state=pda_state'}::stack, input=input', result=result}
                  | _ => case value of N _ => result | T token =>
                    ParseEvents.tokenNotFoundEventHandler({token=token, expected=AtomMap.listKeys shift_items}, result)
               in
                case value of N _ => result | T token =>
                case AtomMap.find(reduce_items, symbkey) of
                  SOME set => WordSet.foldl (reduce{input=input, stack=stack}) result set
                | _ => ParseEvents.tokenNotFoundEventHandler({token=token, expected=AtomMap.listKeys reduce_items}, result)
              end
            | _ => raise General.Fail("BUG: runPDA: pda_state not found in PDA")
          end

        and
          reduce{input, stack} = fn (item0, result) =>
          let
            val DFA = case WordMap.find(DFAs, item0) of
                SOME thing => thing
            | _ => raise General.Fail("BUG: pos_reduce: item0 not found in DFAs")

            val {prodinfo={prodkey, prodpos=endpos}, symbol=_}
                = case WordMap.find(posinfo, item0) of SOME thing => thing
                | _ => raise General.Fail("BUG: reduce: given a pos not found in posinfo")

            fun runDFA{dfa_state, stack, trees, result} =
              let
                val ({symbval, pda_state=_}, stack') = pop_stack(stack)

                val {actions, id=_} = case DfaStateMap.find(DFA, dfa_state) of
                    SOME thing => thing
                | _ => raise General.Fail("BUG: runDFA: state not found in DFA")

                val result = case AtomMap.find(actions, #symbkey symbval) of
                    SOME dfa_state' => runDFA{dfa_state=dfa_state', stack=stack', trees=(make_value symbval)::trees, result=result}
                | _ => result
              in
                if WordSet.member(dfa_state, endpos)
                    then runPDA{stack=stack, input=push_input(input, {symbkey=prodkey, value=N trees}), result=result}
                    else result
              end

            val dfa_start = case WordMap.find(prevpos, item0) of
                SOME thing => thing
            | _ => raise General.Fail("BUG: pos_reduce: item0 not found in posprev")
          in
            runDFA{dfa_state=dfa_start, stack=stack, trees=nil, result=result}
          end
       in
        fn inputN =>
          let
            val tokens = Stream.streamify(Token.lexer(inputN))
           in
            runPDA{stack=nil, input={tokens=tokens, push=NONE}, result=ParseEvents.initialParseResult()}
          end
      end

    fun
      rule(00) = "grammar ::= precassoc_rules production_list"
    | rule(01) = "production_list ::= production"
    | rule(02) = "production_list ::= production production_list"
    | rule(03) = "production ::= ID EQUALS choice_regexp precsymb_opt END_PRODUCTION"
    | rule(04) = "choice_regexp ::= sequence_regexp"
    | rule(05) = "choice_regexp ::= choice_regexp VBAR choice_regexp"
    | rule(06) = "sequence_regexp ::= EPSILON"
    | rule(07) = "sequence_regexp ::= atomic_regexp sequence_regexp"
    | rule(08) = "atomic_regexp ::= symbol"
    | rule(09) = "atomic_regexp ::= atomic_regexp PLUS"
    | rule(10) = "atomic_regexp ::= atomic_regexp QUESTION"
    | rule(11) = "atomic_regexp ::= atomic_regexp ASTERISK"
    | rule(12) = "atomic_regexp ::= LPAREN choice_regexp RPAREN"
    | rule(13) = "atomic_regexp ::= LBRACK choice_regexp RBRACK"
    | rule(14) = "atomic_regexp ::= LBRACE choice_regexp RBRACE"
    | rule(15) = "precassoc_rules ::= EPSILON"
    | rule(16) = "precassoc_rules ::= precassoc_rule precassoc_rules"
    | rule(17) = "precassoc_rule ::= NON_ASSOC symbol_list END_PRODUCTION"
    | rule(18) = "precassoc_rule ::= LEFT_ASSOC symbol_list END_PRODUCTION"
    | rule(19) = "precassoc_rule ::= RIGHT_ASSOC symbol_list END_PRODUCTION"
    | rule(20) = "precsymb_opt ::= EPSILON"
    | rule(21) = "precsymb_opt ::= PREC symbol"
    | rule(22) = "symbol_list ::= symbol"
    | rule(23) = "symbol_list ::= symbol symbol_list"
    | rule(24) = "symbol ::= ID"
    | rule(25) = "symbol ::= TID"
    | rule(26) = "symbol ::= LID"
    | rule _ = raise General.Fail("rule(> 26)")

    local
        open Grammar_AbstractSyntax
      in
        fun
          regexToString(SYMBOL{name, delim_opt, filepos={left=leftpos, ...}}, pos_opt) =
          let
            fun leftDelim(delim_opt) = (case delim_opt of SOME delim => Char.toString delim | _ => "")

            fun rightDelim(delim_opt) = (case delim_opt of SOME delim => Char.toString(if delim = #"<" then #">" else delim) | _ => "")

            val (prefix, suffix) = if leftpos = getOpt(pos_opt, 0w0) then ("[", "]") else ("", "")
           in
            prefix ^ (leftDelim delim_opt) ^ name ^ (rightDelim delim_opt) ^ suffix
          end
        | regexToString(SEQUENCE regex_list, pos_opt) =
          (
            foldl (fn (regex, s) => s ^ " " ^ regexToString(regex, pos_opt)) "" regex_list
          )
        | regexToString(CHOICE(SEQUENCE[], REPETITION regex), pos_opt) =
          (
            "(" ^ regexToString(regex, pos_opt) ^ ")*"
          )
        | regexToString(CHOICE(SEQUENCE[], regex), pos_opt) =
          (
            "(" ^ regexToString(regex, pos_opt) ^ ")?"
          )
        | regexToString(CHOICE(regex1, regex2), pos_opt) =
          (
            "(" ^ regexToString(regex1, pos_opt) ^ " | " ^ regexToString(regex2, pos_opt) ^ ")"
          )
        | regexToString(REPETITION regex, pos_opt) =
          (
            "(" ^ regexToString(regex, pos_opt) ^ ")+"
          )

    end

    fun lookaheadSetToString(set) =
        LookaheadSet.foldl (fn (key, s) => s ^ Atom.toString(key) ^ " ") "" set

    fun productionToString(pos_opt, prodkey)({filepos={left=leftpos, right=rightpos}, regex, precsymbkey_opt}, s) =
      let
        fun precoptToString(precsymbkey_opt) = case precsymbkey_opt of SOME precsymbkey => " %PREC " ^ (Atom.toString precsymbkey) | _ => ""
        val prefix = if pos_opt = SOME leftpos then "[]" else ""
        val suffix = if pos_opt = SOME(rightpos + 0w1) then "[]" else ""
       in
        s ^ Atom.toString(prodkey) ^ " = " ^ prefix ^ regexToString(regex, pos_opt) ^ suffix ^ (precoptToString precsymbkey_opt) ^ "\n"
      end

    fun productionListToString(pos_opt)(prodkey, prodlist, s) =
        foldl (productionToString(pos_opt, prodkey)) s prodlist

    fun posToString{grammar, posinfo}(pos, s) =
      let
        val {prodkey, symbol=_, filepos, regex, precsymbkey_opt} = findPosInfo{grammar=grammar, posinfo=posinfo}(pos)
       in
        productionToString(SOME pos, prodkey)({filepos=filepos, regex=regex, precsymbkey_opt=precsymbkey_opt}, s)
      end

    fun posSetToString(G_info)(prefix)(posset) = WordSet.foldl (fn (pos, s) => posToString(G_info)(pos, s ^ prefix)) "" posset

    fun dfaStatePrint(G_info)(kernel, {id, actions}) =
      (
        print("  state " ^ Word.toString(id) ^ ":\n");
        AtomMap.foldli (fn (symbkey, items, _) => print("    " ^ Atom.toString(symbkey) ^ " goto ->\n" ^ posSetToString(G_info)("      ")(items))) () actions;
        print("\n")
      )

    fun dfaPrint(G_info)(prodpos, DFA, _) =
      (
        print(posToString(G_info)(prodpos, "DFA for "));
        DfaStateMap.foldli (fn (kernel, state, _) => dfaStatePrint(G_info)(kernel, state)) () DFA
      )

    fun item1ToString(G_info)(item0, lookaheads, s) =
        posToString(G_info)(item0, s) ^ " {" ^ lookaheadSetToString(lookaheads) ^ "}\n"

    fun state1Print(G_info)(state_id, {shift_items, reduce_items}) =
      (
        print("state " ^ Word.toString(state_id) ^ ":\n");
        AtomMap.foldli (fn (symbkey, state_id, _) => print(Atom.toString(symbkey) ^ " shift and goto state " ^ (Word.toString state_id) ^ "\n")) () shift_items;
        AtomMap.foldli (fn (symbkey, items, _) => print(Atom.toString(symbkey) ^ " reduce by:\n" ^ (WordSet.foldl (posToString G_info) "      " items))) () reduce_items;
        print("\n")
      )

    fun readGrammar(istream, {stream_name}) =
      let
        val grammar_parser = GrammarParser.makeParser{name=stream_name, inputn=fn n => TextIO.inputN(istream, n)}
        fun print_rule(n) = () (* print(rule(n) ^ "\n") *)
       in
        grammar_parser(print_rule)
      end

    type parser =
      {
        precass:
          {
            symbprec:word AtomMap.map,
            precassoc:bool option Vector.vector
          },

        grammar:
          {
            filepos:{left:word, right:word},
            regex:Grammar_AbstractSyntax.regular_expression,
            precsymbkey_opt:Atom.atom option
          } list AtomMap.map,

        posinfo:
          {
            prodinfo:{prodkey:Atom.atom, prodpos:word},
            symbol:Atom.atom
          } WordMap.map,

        nextpos:WordSet.set WordMap.map,

        prevpos:WordSet.set WordMap.map,

        DFAs:
          {
            actions:WordSet.set AtomMap.map,
            id:word
          } DfaStateMap.map WordMap.map,

        PDA:
          {
            reduce_items:WordSet.set AtomMap.map,
            shift_items:word AtomMap.map
          } WordMap.map,

        pda_start:word AtomMap.map
      }

    type parse_result = ParseEvents.parse_result

    fun makeParser(Grammar_AbstractSyntax.GRAMMAR{precassoc_rules, production_list=prodlist}) =
      let
        val {grammar, symbols, terminals, nonterminals, posinfo, nextpos, prevpos} = processProductions(prodlist)

        val precass = processPrecAssocRules(nonterminals)(precassoc_rules)

        val epsilons = processEpsilons{grammar=grammar, nonterminals=nonterminals}

        val followpos = processFollowPos{grammar=grammar, terminals=terminals, posinfo=posinfo, nextpos=nextpos, epsilons=epsilons}

        val DFAs = AtomMap.foldli (processDFAs{grammar=grammar, posinfo=posinfo, prevpos=prevpos}) WordMap.empty grammar

        val {PDA, pda_start} = processPDA{precass=precass, grammar=grammar, posinfo=posinfo, nextpos=nextpos, followpos=followpos}

        val G_info = {grammar=grammar, posinfo=posinfo}
        val _ = print("\nTerminals:\n")
        val _ = AtomSet.foldl (fn (symbkey, _) => print(Atom.toString(symbkey) ^ "\n")) () terminals
        val _ = print("\nProductions:\n")
        val _ = AtomMap.foldli (fn (prodkey, prodlist, _) => print(productionListToString(NONE)(prodkey, prodlist, ""))) () grammar
(*
        val _ = print("\nPositions Next:\n")
        val _ = WordMap.foldli (fn (key, posnext, _) => print(posToString{grammar=grammar, posinfo=posinfo}(key, "") ^ posSetToString(G_info)(" -> ")(posnext))) () nextpos
        val _ = print("\nPositions Previous:\n")
        val _ = WordMap.foldli (fn (key, posprev, _) => print(posToString{grammar=grammar, posinfo=posinfo}(key, "") ^ posSetToString(G_info)(" <- ")(posprev))) () prevpos
        val _ = print("\nEpsilon Status:\n")
        val _ = AtomMap.foldli (fn (key, boolean, _) => print(Atom.toString(key) ^ " = " ^ Bool.toString(boolean) ^ "\n")) () epsilons
        val _ = print("\nDFA state machines:\n")
        val _ = WordMap.foldli (dfaPrint G_info) () DFAs
        val _ = print("\nFollowpos:\n")
        val _ = WordMap.foldli (fn (pos, setfun, _) => print(posToString{grammar=grammar, posinfo=posinfo}(pos, "") ^ ": {" ^ lookaheadSetToString(setfun(LookaheadSet.singleton(Atom.atom "#"))) ^ "}\n\n")) () followpos
        val _ = print("\nLR(1) States:\n")
        val _ = WordMap.foldli (fn (id, state, _) => state1Print(G_info)(id, state)) () PDA
*)
        val _ = print("\nNumber of States = " ^ Int.toString(WordMap.numItems PDA) ^ "\n")
       in
        {precass=precass, grammar=grammar, posinfo=posinfo, nextpos=nextpos, prevpos=prevpos, DFAs=DFAs, PDA=PDA, pda_start=pda_start}
      end

    fun writeParser(ostream, {precass, grammar, posinfo, nextpos, prevpos, DFAs, PDA, pda_start}) =
      let
        fun outputString(str) = (* output null terminated string *)
            BinIO.output(ostream, Word8Vector.fromList(map (fn x => Word8.fromInt (ord x)) (explode (str^implode [chr 0]))))
        fun outputAtom(a) =
            outputString(Atom.toString(a))
        fun outputBool(b) = (* 0 or 1 (8-bit) *)
            BinIO.output1(ostream, if b then 0wx1 else 0wx0)
        fun outputOpt f a = (* output (0) or (1 then valOf a) *)
            (
                outputBool(isSome a);
                if(isSome a) then f (valOf a)
                else ()                
            )
        (* assumes 31 or 32 bit word for now (using msb first (big endian)) *)
        fun outputWord(w) =
            let (* TODO - is there an SMLNJ way to do this? *)
                fun getIth i = Word8.fromLarge(Word.toLarge(Word.>>(w, Word.fromInt(8 * (3-i)))))
                val words = Word8Vector.tabulate(4, getIth)
            in
                BinIO.output(ostream, words)
            end
        fun outputInt(i) =
            outputWord(Word.fromInt(i))
            
        fun outputList f list = (* works like List.map but outputs length first *)
            (
                outputInt(List.length list);
                map f list
            )
        fun outputWordSet(set) =
                outputList outputWord (WordSet.listItems set)                
            
        (* *MapFns are for outputMap (only WordMaps, AtomMaps, and DfaStateMaps are used so far *)
        val wordMapFns = (WordMap.listKeys, WordMap.lookup, outputWord)
        val atomMapFns = (AtomMap.listKeys, AtomMap.lookup, outputAtom)
        val dfaStateMapFns = (DfaStateMap.listKeys, DfaStateMap.lookup, outputWordSet)
        (* write a map to ostream
           first tuple should use one of the *MapFns variables depending on type of map
           the number of elements in the map (32-bit) is output, then the key, then the value
           the value is output using dataFn *)
        fun outputMap (     
                            (listFn : 'm -> 'k list),
                            (lookupFn : 'm * 'k -> 'd),
                            (keyFn : 'k -> 'a)
                       )
                      (dataFn : 'd -> 'b)
                      (myMap : 'm) =
            let
                val keys = listFn(myMap)
                val _ = outputList (fn x => (keyFn x; dataFn (lookupFn(myMap, x)))) keys
            in
                ()
            end
        
        (* precedence is 32-bit, associativity  is 8-bit (0,1,2) *)
		fun writePrecass(ostream, {symbprec:word AtomMap.map, precassoc}) =
            let
                (* val _ = print("should be writing precedence/associativity!\n") *)
                val precassoc = Vector.foldr (fn (x,acc) => x::acc) [] precassoc
                fun precassocToWord8(x) : Word8.word =
                    (case x of SOME true => 0wx2 | SOME false => 0wx1 | NONE => 0wx0)
                val _ = outputMap atomMapFns outputWord symbprec
                val _ = outputList (fn x => BinIO.output1(ostream, precassocToWord8(x))) precassoc
            in
                ()
            end 
        (* after each key it prints the length of the list associated with the key
            then the actual list using writePart*)
        fun writeGrammar(ostream, grammar) =
           let
                open Grammar_AbstractSyntax
                (* val _ = print("should be writing grammar!\n") *)
                (* writes a regex (from Grammar_AbstractSyntax).
                    parts of a regex are preceded by their type (0-3) (8-bit)
                    In SEQUENCE, the regex list is preceded by its length (32 bit from 31 bit word) *)
                fun writeRegex(regex) =
                    let
                        fun writeType(x) = 
                            (
                                BinIO.output1(ostream, case x of 
                                    SYMBOL _ => 0wx0 
                                  | SEQUENCE _ => 0wx1
                                  | CHOICE _ => 0wx2
                                  | REPETITION _ => 0wx3)
                            )
                        fun writePart(SYMBOL {name, delim_opt, filepos={left,right}}) =
                            (
                                outputString(name);
                                outputOpt (fn x => BinIO.output1(ostream, Word8.fromInt(ord x))) delim_opt;
                                outputWord(left);
                                outputWord(right)
                            )
                          | writePart(SEQUENCE regexes) =
                            (
                                outputList writeRegex regexes;
                                ()
                            )
                          | writePart(CHOICE (regex1, regex2)) =
                            (
                                writeRegex(regex1);
                                writeRegex(regex2)
                            )
                          | writePart(REPETITION regex) =
                                writeRegex(regex)
                                
                        val _ = writeType(regex)
                    in
                        writePart(regex)
                    end
                (* writes the left/right file positions
                   then the regex associated with it (using writeRegex)
                   then a 0 or 1 (8-bit) depending on whether precsymbkey_opt exists
                   if precsymbkey_opt exists, it writes it, otherwise not *)   
                fun writePart({filepos={left,right}, regex, precsymbkey_opt}) =
                    (
                        outputWord(left);
                        outputWord(right);
                        writeRegex(regex);
                        outputOpt outputAtom precsymbkey_opt
                    )
            in
                outputMap atomMapFns (outputList writePart) grammar
            end
        fun writePosinfo(ostream, posinfo) =
            let
                (* val _ = print("should be writing posinfo!\n") *)
                fun writePart{prodinfo={prodkey,prodpos},symbol} = 
                    (
                        outputAtom(prodkey);
                        outputWord(prodpos);
                        outputAtom(symbol)
                    )
            in
                outputMap wordMapFns writePart posinfo
            end
        
        (* writes the set map as a list of lists with a length (32-bit) before each list *)
        fun writeAdjacentpos(ostream, possetmap) =
            let
                (* val _ = print("should be writing adjacent pos info!\n") *)
            in
                outputMap wordMapFns outputWordSet possetmap
            end
        fun writeDFAs(ostream, DFAs) =
            let
                (* val _ = print("should be writing dfas!\n") *)
                fun writePart{actions, id} = 
                    (
                        outputMap atomMapFns outputWordSet actions;
                        outputWord(id)
                    )
            in
                outputMap wordMapFns (outputMap dfaStateMapFns writePart) DFAs
            end
        fun writePDA(ostream, PDA) =
            let
                (* val _ = print("should be writing pdas!\n") *)
                fun writeState{reduce_items, shift_items} = 
                    (                 
                        outputMap atomMapFns outputWordSet reduce_items;
                        outputMap atomMapFns outputWord shift_items
                    )
            in
                outputMap wordMapFns writeState PDA
            end
        (*TODO - should this be written?*)
        fun writePDAStart(ostream, pdaStart) =
            let
                (* val _ = print("should be writing pdastart!\n") *)
            in
                outputMap atomMapFns outputWord pdaStart
            end
       in
        writePrecass(ostream, precass);
        writeGrammar(ostream, grammar);
        writePosinfo(ostream, posinfo);
        writeAdjacentpos(ostream, nextpos);
        writeAdjacentpos(ostream, prevpos);
        writeDFAs(ostream, DFAs);
        writePDA(ostream, PDA);
        writePDAStart(ostream, pda_start)
      end

    fun readParser(istream) =
       let 
        fun readString() = (* read null terminated string *)
            let
                fun aux(acc) = 
                    let
                        val SOME ch = BinIO.input1(istream)
                        val ch = Word8.toInt(ch)
                    in
                        if ch = 0 then rev acc
                        else aux((chr ch)::acc)
                    end
                val chars = aux []
            in
                implode chars
            end
        fun readAtom() =
                Atom.atom(readString())
        fun readBool() = (* 0 or nonzero (8-bit) *)
            let
                val SOME b = BinIO.input1(istream)
            in
                if b = 0wx0 then false 
                else true
            end                
        fun readOpt f = (* input gets (0) means NONE
                                    or (1) means SOME f(istream) *)
            if readBool() then SOME (f())
            else NONE
        (* assumes 31 or 32 bit word for now (using msb first (big endian)) *)
        fun readWord() =
            let
                val vec = BinIO.inputN(istream, 4)
            in
                Word8Vector.foldli (fn (i, x, acc) => (Word.<<(Word.fromLarge(Word8.toLarge(x)), Word.fromInt(8 * (3 - i)))) + acc) 0wx0 vec
            end
        fun readInt() =
            Word.toInt(readWord())
        fun readList f = (* reads length (32-bit), then that # of elements *)
            let
                val length = readInt()
                fun aux (acc, 0) = rev acc
                  | aux (acc, remaining) = aux((f())::acc, remaining - 1)
            in
                aux([], length)
            end
        fun readWordSet(istream) = WordSet.fromList(readList readWord)
             
        (* *MapFns are for readMap (only WordMaps, AtomMaps, and DfaStateMaps are used so far) *)
        val wordMapFns = (WordMap.empty, WordMap.insert, readWord)
        val atomMapFns = (AtomMap.empty, AtomMap.insert, readAtom)
        val dfaStateMapFns = (DfaStateMap.empty, DfaStateMap.insert, readWordSet)
        (* read a map fromo istream
           first tuple should use one of the *MapFns variables depending on type of map
           the number of elements in the map (32-bit) is read, then the key, then the value
           the value is read using dataFn *)
        fun readMap (
                            (empty : 'm),
                            (insertFn : 'm * 'k * 'd -> 'm),
                            (keyFn : unit -> 'k )
                      )
                      (dataFn : unit -> 'd) =
            let
                val size = readInt()
                fun aux(myMap, 0) = myMap
                  | aux(myMap, remaining) =
                        let
                            val key = keyFn()
                            val data = dataFn()
                        in
                            aux(insertFn(myMap, key, data), remaining - 1)
                        end
            in
                aux(empty, size)
            end
        
        (* read null terminated string, then the precedence(32-bit), then the associativity (0,1,2) (8-bit) *)
		fun readPrecass() = 
            let
                (* val _ = print("should be reading precedence/associativity!\n") *)
                fun precassocFromWord8(x : Word8.word) =
                    (case x of 0wx2 => SOME true | 0wx1 => SOME false | 0wx0 => NONE
                      | _ => raise General.Fail("Bad precedence/associativity in readParser()... try writeParsers again???" ^ Word8.toString(x)))
               
                val symbprec = readMap atomMapFns readWord
                val precassoc = readList (fn () => valOf(BinIO.input1(istream)))
                val precassoc = Vector.fromList(map precassocFromWord8 precassoc)
            in
               (* print ("symbprec: " ^ AtomMap.foldri (fn (k, v, acc) => Atom.toString(k) ^ "," ^ Int.toString(Word.toInt(v)) ^ "\n" ^ acc) "" symbprec); *)
                {symbprec=symbprec, precassoc=precassoc}
            end 
        fun readGrammar() =
           let
                open Grammar_AbstractSyntax
                (* val _ = print("should be reading grammar!\n") *)
                (* reads a regex (from Grammar_AbstractSyntax).
                    parts of a regex are preceded by their type (0-3) (8-bit)
                    In SEQUENCE, the regex list is preceded by its length (32 bit from 31 bit word) *)
                fun readRegex() =
                    let
                        fun readType() = 
                            case valOf(BinIO.input1(istream)) of
                                0wx0 => readSymbol()
                              | 0wx1 => readSequence()
                              | 0wx2 => readChoice()
                              | 0wx3 => readRepetition()
                              | x => raise General.Fail("Bad regex type in readParser()... try writeParsers again???" ^ Word8.toString(x))
                        and readSymbol() =
                            let
                                val name = readString()
                                val delim_opt = readOpt (fn () => chr (Word8.toInt(valOf(BinIO.input1(istream)))))
                                val left = readWord()
                                val right = readWord()
                            in
                                SYMBOL {name=name, delim_opt=delim_opt, filepos={left=left, right=right}}
                            end
                        and readSequence() =
                            SEQUENCE (readList readRegex)
                        and readChoice() =
                            let
                                val regex1 = readRegex()
                                val regex2 = readRegex()
                            in
                                CHOICE (regex1, regex2)
                            end
                        and readRepetition() =
                            REPETITION (readRegex())
                    in
                        readType()
                    end
                    
                fun readPart() =
                    let
                        val left = readWord()
                        val right = readWord()
                        val regex = readRegex()
                        val precsymbkey_opt = readOpt readAtom
                    in
                        {filepos={left=left,right=right}, regex=regex, precsymbkey_opt=precsymbkey_opt}
                    end
            in
                readMap atomMapFns (fn () => readList readPart) 
            end
        fun readPosinfo() =
            let
                (* val _ = print("should be reading posinfo!\n") *)
                fun readPart() =
                    let
                        val prodkey = readAtom()
                        val prodpos = readWord()
                        val symbol = readAtom()
                    in
                        {prodinfo={prodkey=prodkey,prodpos=prodpos},symbol=symbol}
                    end
            in
                readMap wordMapFns readPart
            end
        
        (* reads the set map as a list of lists with a length (32-bit) before each list *)
        fun readAdjacentpos() =
            readMap wordMapFns readWordSet
        fun readDFAs() =
            let
                (* val _ = print("should be reading dfas!\n") *)
                fun readPart() =
                    let
                        val actions = readMap atomMapFns readWordSet
                        val id = readWord()
                    in
                        {actions=actions, id=id}
                    end
            in
                readMap wordMapFns (fn () => readMap dfaStateMapFns readPart)
            end
        fun readPDA() =
            let
                (* val _ = print("should be reading pdas!\n") *)
                fun readState() =
                    let               
                        val reduce_items = readMap atomMapFns readWordSet
                        val shift_items = readMap atomMapFns readWord
                    in
                        {reduce_items=reduce_items, shift_items=shift_items}
                    end
            in
                readMap wordMapFns readState 
            end
        (*TODO - should this be read?*)
        fun readPDAStart() =
            let
                (* val _ = print("should be writing pdastart!\n") *)
            in
                readMap atomMapFns readWord
            end
            
      in
            {
                precass=readPrecass(),
                grammar=readGrammar(),
                posinfo=readPosinfo(),
                nextpos=readAdjacentpos(),
                prevpos=readAdjacentpos(),
                DFAs=readDFAs(),
                PDA=readPDA(),
                pda_start=readPDAStart()
            }
      end
      (* {precass={symbprec=AtomMap.empty, precassoc= ##[NONE]}, grammar=AtomMap.empty, posinfo=WordMap.empty, nextpos=WordMap.empty, prevpos=WordMap.empty, DFAs=WordMap.empty, PDA=WordMap.empty, pda_start=AtomMap.empty} : parser *)
	  
	  
	  
    (* ----------------------------------------------------------------------------------------------------------------------- *)
	fun getGrammar( g as Grammar_AbstractSyntax.GRAMMAR{precassoc_rules, production_list=prodlist} ) = g 
(*	
		let
		    fun bar(0) = 0
			  | bar(n) = bar(n-1)
			  
			fun aux(0) = (bar 1000000; print("hello\n"))
			  | aux(n) = (bar 1000000; print("hello\n"); aux(n-1))
	
(*	
	  type production = {name : string, filepos : filepos, regex : regular_expression, precsymb_opt : symbol option}
	  processProductions returns:
           {
          grammar=grammar,
          symbols=symbols,
          terminals = terminals,
          nonterminals = nonterminals,
          posinfo = posinfo,
          nextpos = nextpos,
          prevpos = prevpos
        }
  *) 
			val {grammar, symbols, terminals, nonterminals, posinfo, nextpos, prevpos} = processProductions(prodlist)
			val _ = print("\nTerminals:\n")
			val _ = AtomSet.foldl (fn (symbkey, _) => print(Atom.toString(symbkey) ^ "\n")) () terminals
			val _ = print("\nProductions:\n")
			val _ = AtomMap.foldli (fn (prodkey, prodlist, _) => print(productionListToString(NONE)(prodkey, prodlist, ""))) () grammar
			
			val terminal_list = AtomSet.foldl  (fn (symbkey, the_list) => Atom.toString(symbkey) :: the_list) [] terminals
			
			
			
		in
		
		print("\n++++++++++++++++++++++++++++++++++++++++++++++\n");
		map (fn x => print( x ^ "\n")) terminal_list;
			aux 10000
			       

		end 
*)	  
(* ----------------------------------------------------------------------------------------------------------------------- *)	  
  end
(* ----------------------------------------------------------------------------------------------------------------------- *)