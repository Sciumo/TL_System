val ## = Vector.fromList; (* SML/NJ shorthand hack *)

functor BitVectorSetFn (M : ORD_MAP)
:> sig
    include ORD_SET

    val listItemsU : set -> item list
        (* Return an unordered list of the items in the set *)

    val compareU : set * set -> order
        (* Return an unordered comparison of the two sets *)

    val appU : (item -> unit) -> set -> unit
        (* Apply a function to the entries of the set 
         * in no particular order
         *)

    val foldU : (item * 'b -> 'b) -> 'b -> set -> 'b
        (* Apply a folding function to the entries of the set 
         * in no particular order
         *)
   end where type Key.ord_key = M.Key.ord_key =
  struct
    structure Key = M.Key

    type item = Key.ord_key

    type set = BitArray.array

    local
        val m_ref = ref M.empty
        val v_ref = ref (##[])
      in
        fun index(e) =
          (
            case M.find(!m_ref, e) of
              SOME i => i
            | _ =>
              let
                val i = Vector.length(!v_ref)
               in
                (m_ref := M.insert(!m_ref, e, i); v_ref := Vector.concat[!v_ref, ##[e]]; i)
              end
          )

        fun get_key(i) = Vector.sub(!v_ref, i)
      end

    val empty = BitArray.array(0, false)

    fun singleton(e) =
      let
        val i = index e
        val s = BitArray.array(i + 1, false)
       in
        (BitArray.setBit(s, i); s)
      end

    fun add(s, e) =
      let
        val i = index e
        val len' = Int.max(BitArray.length s, i + 1)
        val s' = BitArray.orb(s, empty, len')
       in
        (BitArray.setBit(s', i); s')
      end
    fun add'(e, s) = add(s, e)

    fun addList(s, l) =
      let
        val l' = map index l
        val len' = Int.max(BitArray.length s, (foldl Int.max 0 l') + 1)
        val s' = BitArray.orb(s, empty, len')
       in
        (app (fn i => BitArray.setBit(s', i)) l'; s')
      end
	
	fun fromList(l) = addList(empty, l)

    fun delete(s, e) =
      let
        val i = index e
       in
        if i >= BitArray.length s then s else
          let
            val s' = BitArray.orb(s, empty, BitArray.length s)
           in
            (BitArray.clrBit(s', i); s')
          end
      end

    fun member(s, e) =
      let
        val i = index e
       in
        i < BitArray.length(s) andalso BitArray.sub(s, i)
      end

    val isEmpty = BitArray.isZero

    val equal = BitArray.eqBits

    fun compareU(sa, sb) = String.compare(BitArray.toString sa, BitArray.toString sb)

    fun to_ord_map s = foldl M.insert' M.empty (map (fn i => (get_key i, ())) (BitArray.getBits s))

    val M_compare = M.collate(fn (_:unit, _:unit) => EQUAL)

    fun compare(sa, sb) = M_compare(to_ord_map sa, to_ord_map sb)

    fun union(sa, sb) = BitArray.orb(sa, sb, Int.max(BitArray.length sa, BitArray.length sb))

    fun intersection(sa, sb) = BitArray.andb(sa, sb, Int.min(BitArray.length sa, BitArray.length sb))

    fun difference(sa, sb) = BitArray.andb(sa, BitArray.extend1(BitArray.notb sb, BitArray.length sa), BitArray.length sa)

    fun isSubset(sa, sb) = BitArray.eqBits(union(sa, sb), sb)

    val numItems = BitArray.length

    fun listItemsU s = map get_key (BitArray.getBits s)

    fun appU f s = List.app f (listItemsU s)

    fun foldU f i s = List.foldl f i (listItemsU s)

    val listItems = M.listKeys o to_ord_map

    fun map f s = addList(empty, List.map f (listItemsU s))

    fun app f s = List.app f (listItems s)

    fun foldl f i s = List.foldl f i (listItems s)

    fun foldr f i s = List.foldr f i (listItems s)

    fun filter f s = addList(empty, List.filter f (listItemsU s))
	
	fun partition f s = let
			val (pos, neg) = List.partition f (listItemsU s)
		in
			(addList(empty, pos), addList(empty, neg))
		end

    fun exists f s = List.exists f (listItemsU s)

    fun find f s = List.find f (listItemsU s)
  end
