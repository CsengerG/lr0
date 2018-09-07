exception InvalidInputException;

datatype Terminal = Id | Plus | Star | OpPar | ClPar | Eps
datatype NonTerminal = Start | E | Term | F

datatype GrammarSymbol = T  of Terminal | NT of NonTerminal | EndMarker | ItemDot
datatype ProductionRule = PR of NonTerminal * GrammarSymbol list

val prodrules = [
    PR(Start, [NT E]),

    PR(E, [NT E, T Plus, NT Term]),
    PR(E, [NT Term]),

    PR(Term, [NT Term, T Star, NT F]),
    PR(Term, [NT F]),

    PR(F, [T OpPar, NT E, T ClPar]),
    PR(F, [T Id])
]

datatype Item = I of NonTerminal * GrammarSymbol list

datatype 'a Set = S of 'a list

fun inSet(S [], _) = false
  | inSet(S (x::xs), y) = x=y orelse inSet(S xs, y)

fun inList([], _) = false
  | inList((x::xs), y) = x=y orelse inList(xs, y)

fun insert(S [], y) = S [y]
  | insert(S (x::xs), y) = 
      if x=y then S (x::xs) 
      else let val (S L) = insert(S xs, y) in S (x::L) end

fun isEmpty(S []) = true
  | isEmpty _ = false

fun union(S [], set) = set 
  | union(set, S []) = set
  | union(S s1, S s2) = foldl (fn (x,acc) => insert(acc,x)) (S s1) s2


fun unionWithout(leaveOut, S s1, S s2) = foldl (fn (x,acc) => 
                                       if x = leaveOut then acc
                                       else insert(acc, x)) (S s1) s2

fun filter _ [] = []
  | filter p (x::xs) = if p x then x :: filter p xs 
                       else filter p xs
fun diff(S l1, S l2) = S (filter (fn x => not (inSet(S l2, x))) l1)

fun all _ [] = true
  | all p (x::xs) = p x andalso all p xs

fun takeWhile _ [] = []
  | takeWhile p (x::xs) = if p x then x :: takeWhile p xs 
                          else [x]
                        
exception NoFirst

fun first [] = S []
  | first str =
      let
    fun getFirst _ EndMarker = raise NoFirst
      | getFirst _ (T t) = S [T t]
      | getFirst visited (NT nt) =
        let
          val prodrulesWithNt = filter (fn (PR(left, _)) => left = nt) prodrules
          val newvisited = insert(visited, NT nt)

          fun firstUtil [] = S []
            | firstUtil (PR(x,[])::ps) = S []
            | firstUtil (PR(x,(y::ys))::ps) = 
                let
                  val firstOfBeginning = getFirst newvisited y
                in 
                  union(firstOfBeginning, 
                        if inSet(firstOfBeginning, T Eps) 
                           then firstUtil (PR(x,ys)::ps)
                           else firstUtil ps)
                end
        in if inSet(visited, NT nt) then S [] else firstUtil prodrulesWithNt end
        val firstPerGS = (map (getFirst (S [])) str) @ [S [T Eps]]
        val withEps = takeWhile (fn s => inSet(s, T Eps)) firstPerGS
    in
        foldl (fn (x,acc) => union(x,acc)) (S []) withEps
    end

exception NoFollow
fun follow EndMarker = raise NoFollow
  | follow (T _) = S [T Eps]
  | follow (NT B) =
    let
      val prodRulesWithB = filter (fn (PR(_,symbols)) => inList(symbols, NT B)) prodrules

      fun getTailsAfterBs [] = []
        | getTailsAfterBs (x::xs) =
          if x = (NT B) then xs :: getTailsAfterBs xs
          else getTailsAfterBs xs

      fun processOneProdRule (PR(head,symbols)) =
        let
          val setlist = map first (getTailsAfterBs symbols)
          val bigunion = foldl (fn (x,acc) => union(x,acc)) (S []) setlist
        in
          bigunion
        end

      val sets = map processOneProdRule prodRulesWithB
    in
      foldl (fn (x,acc) => union(x,acc)) (S []) sets
    end

exception MaybeException

fun setmap f (S l) = S (map f l)
fun setfilter f (S l) = S (filter f l)

fun closure set =
  let
    fun closureUtil was (S []) = was
      | closureUtil was (S ((curr as (I(l,r)))::rest)) =
      let
        fun symbolafterdot [] = []
          | symbolafterdot [x] = []
          | symbolafterdot (ItemDot::x::_) = [x]
          | symbolafterdot (x::xs) = symbolafterdot xs

        fun productionsWith [] = []
          | productionsWith [x] = filter (fn (PR(l,_)) => NT l=x) prodrules 
          | productionsWith _ = raise MaybeException

        val symbolAfterDot = symbolafterdot r
        val prods = productionsWith symbolAfterDot
        val nexts = map (fn (PR(head, right)) => I(head, ItemDot :: right)) prods
        val (S newnexts) = diff(S nexts, was)
      in
        closureUtil (insert(was, curr)) (S (rest @ newnexts))
      end
  in closureUtil (S []) set end

val cl = closure (S [I(Start, [ItemDot, NT E])])
fun len [] = 0 | len (x::xs) = 1 + len xs
fun size (S l) = len l
exception NoDot
fun goto i x = 
  let
    fun dotbeforex [] = false
      | dotbeforex (ItemDot::s::ss) = s = x
      | dotbeforex (s::ss) = dotbeforex ss

    fun moveDotToRight [] = raise NoDot
      | moveDotToRight (ItemDot::s::ss) = s::ItemDot::ss
      | moveDotToRight (s::ss) = s :: moveDotToRight ss

    val withDotBeforeX = setfilter (fn I(_, r) => dotbeforex r) i
  in
    closure (setmap (fn (I(l,r)) => I(l, moveDotToRight r)) withDotBeforeX)
  end

val g = goto (S [I(Start, [NT E, ItemDot]), I(E, [NT E, ItemDot, T Plus, NT Term])]) (T Plus)
