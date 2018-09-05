exception InvalidInputException;

datatype Terminal = Number |
                 Plus |
                 Minus |
                 Star |
                 ExclMark |
                 Cos |
                 Exponent |
                 Point |
                 OpPar |
                 ClPar |
                 Eps

datatype NonTerminal = Start | expr | E | E1 | E2 | E3 | E4 | E5
datatype GrammarSymbol = T  of Terminal
                       | NT of NonTerminal
                       | EndMarker

datatype ProductionRule = PR of NonTerminal * GrammarSymbol list

val prodrules = [
    PR(Start, [NT expr]),

    PR(expr, [T Plus, NT expr]),
    PR(expr, [T Minus, NT expr]),
    PR(expr, [NT E]),

    PR(E, [NT E1, T Plus, NT E]),
    PR(E, [NT E1]),

    PR(E1, [NT E2, T Minus, NT E1]),
    PR(E1, [NT E2]),

    PR(E2, [NT E2, T Star, NT E3]),
    PR(E2, [NT E3]),

    PR(E3, [T Cos, NT E4]),
    PR(E3, [NT E4]),

    PR(E4, [NT E5, T ExclMark]),
    PR(E4, [NT E5]),

    PR(E5, [T Number]),
    PR(E5, [T OpPar, NT E, T ClPar])
]

datatype 'a Set = S of 'a list

fun inSet(S [], _) = false
  | inSet(S (x::xs), y) = x=y orelse inSet(S xs, y)

fun inList([], _) = false
  | inList((x::xs), y) = x=y orelse inList(xs, y)

fun insert(S [], y) = S [y]
  | insert(S (x::xs), y) = 
      if x=y then S (x::xs) 
      else let val (S L) = insert(S xs, y) in S (x::L) end

fun union(S [], set) = set 
  | union(set, S []) = set
  | union(S s1, S s2) = foldl (fn (x,acc) => insert(acc,x)) (S s1) s2

fun unionWithout(leaveOut, S s1, S s2) = foldl (fn (x,acc) => 
                                       if x = leaveOut then acc
                                       else insert(acc, x)) (S s1) s2

fun filter _ [] = []
  | filter p (x::xs) = if p x then x :: filter p xs 
                       else filter p xs

fun all _ [] = true
  | all p (x::xs) = p x andalso all p xs

fun takeWhile _ [] = []
  | takeWhile p (x::xs) = if p x then x :: takeWhile p xs 
                          else [x]
                        
fun getPairs [] = []
  | getPairs [x] = []
  | getPairs (x::y::ys) = (x,y) :: getPairs (y::ys)

exception EmptyProduction

fun first [] = S []
  | first str =
      let
    fun getFirst _ (T t) = S [T t]
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
