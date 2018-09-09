import qualified Data.Set as Set
import Data.Ord as Ord
import Data.Maybe as Maybe
import Data.Char as Char
import Debug.Trace

---------------------------------------------------------------------------------------------------
------------------------------------------- TYPES -------------------------------------------------
---------------------------------------------------------------------------------------------------

-- The Tokens the lexer can return with
data Token = NumberToken Float
           | PlusToken 
           | MinusToken 
           | StarToken 
           | ExclMarkToken
           | CosToken
           | OpParToken
           | ClParToken
             deriving (Show, Eq, Ord)

-- Make sure Terminal includes EndMarker and that NonTerminal includes Start and AugStart, where
data Terminal = EndMarker 
              | Plus 
              | Minus 
              | Star 
              | ExclMark 
              | Cos
              | OpPar 
              | ClPar 
              | Number
                deriving (Show, Eq, Ord)

-- Start is the start symbol of your grammar. You MUST NOT use AugStart when describing your grammar.
data NonTerminal = AugStart | Start 
                 | E 
                 | Term 
                 | CosTerm 
                 | FactorialTerm
                 | Factor
                   deriving (Show, Eq, Ord)

-- GrammarSymbol is used in production rules --
data GrammarSymbol = T Terminal | NT NonTerminal deriving (Show, Eq, Ord)

-- ItemSymbol is used to describe items --
data ItemSymbol = IS GrammarSymbol | ItemDot deriving (Show, Eq, Ord)

-- The format of production rules and items is almost the same --
data ProductionRule = PR (NonTerminal, [GrammarSymbol]) deriving (Show, Eq, Ord)
data Item = I (NonTerminal, [ItemSymbol]) deriving (Show, Eq, Ord)

-- Just a tree
data Tree a = Br (a, [Tree a]) | Lf a deriving Show

-- Describe your grammar here by listing the production rules
prodRules = [
  PR(Start, [NT E]),

  PR(E, [NT E, T Plus, NT E]),
  PR(E, [NT E, T Minus, NT E]),
  PR(E, [T Plus, NT E]),
  PR(E, [T Minus, NT E]),
  PR(E, [NT Term]),

  PR(Term, [NT Term, T Star, NT CosTerm]),
  PR(Term, [NT CosTerm]),

  PR(CosTerm, [T Cos, NT CosTerm]),
  PR(CosTerm, [NT FactorialTerm]),

  PR(FactorialTerm, [NT FactorialTerm, T ExclMark]),
  PR(FactorialTerm, [NT Factor]),

  PR(Factor, [T Number]),
  PR(Factor, [T OpPar, NT E, T ClPar])]

---------------------------------------------------------------------------------------------------
--------------------------------- UTILITY ---------------------------------------------------------
---------------------------------------------------------------------------------------------------

fact 0 = 1
fact n = n * fact (n-1)

closure :: (Ord a) => (a -> [a]) -> Set.Set a -> Set.Set a
-- Compute the closure of a Set.
closure arrows set =
  closureBFS (Set.fromList []) (Set.elems set)
    where
      closureBFS was [] = was
      closureBFS was (q:qs) = closureBFS newWas newQueue
        where
          newWas= Set.insert q was
          newQueue = qs ++ [x | x <- arrows q, Set.notMember x was]


itemArrows :: Item -> [Item]
-- Given an item, get the list of neighbouring items
itemArrows (I(_, symbols)) = (consWithDot . productionsWith . gsAfterDot) symbols
  where
    gsAfterDot :: [ItemSymbol] -> Maybe GrammarSymbol
    -- Get the GrammarSymbol after the Dot or nothing if not found.
    gsAfterDot [] = Nothing
    gsAfterDot (ItemDot:(IS gs):_) = Just gs 
    gsAfterDot (x:xs) = gsAfterDot xs

    productionsWith :: Maybe GrammarSymbol -> [ProductionRule]
    -- Gives all the productions for a GrammarSymbol.
    productionsWith Nothing = []
    productionsWith (Just symbol) = filter (\(PR(nt, _)) -> symbol == NT nt) prodRules

    consWithDot :: [ProductionRule] -> [Item]
    -- Create a new Item from each production rule by prepending it with a dot.
    consWithDot = map (\(PR(nt, gss)) -> I(nt, ItemDot:(toIS gss)))
      where toIS = map (\gs -> IS gs)


-- Define the function itemClosure as a partially applied closure function.
itemClosure = closure itemArrows


goto :: Set.Set Item -> GrammarSymbol -> Set.Set Item
-- GOTO function: compute it by the definition
goto i x = (itemClosure . moveDotRightToX . getItemsWithDotLeftToX) i
  where
    moveDotRightToX :: Set.Set Item -> Set.Set Item
    moveDotRightToX = Set.map (\(I(nt, iSymbols)) -> I(nt, moveDotRight iSymbols)) 
      where
        moveDotRight :: [ItemSymbol] -> [ItemSymbol]
        moveDotRight [] = []
        moveDotRight (ItemDot : y : ys) = y : ItemDot : ys
        moveDotRight (y:ys) = y : moveDotRight ys

    getItemsWithDotLeftToX :: Set.Set Item -> Set.Set Item
    getItemsWithDotLeftToX = Set.filter (\(I(_, is)) -> isDotLeftToX is)
      where 
        isDotLeftToX :: [ItemSymbol] -> Bool 
        isDotLeftToX [] = False
        isDotLeftToX (ItemDot:y:ys) = IS x == y
        isDotLeftToX (y:ys) = isDotLeftToX ys


-- The start state is always one with the item AugStart -> . Start
startState = itemClosure (Set.fromList [I(AugStart, [ItemDot, IS (NT Start)])])
emptySet = Set.fromList []

--------------------------------
---------- MATCH ---------------
--------------------------------

data Match = M(String, String) deriving Show

matchEps :: Match -> Match
matchEps = \rest -> rest

matchOptPm :: Match -> Match
matchOptPm (M(m, ('+':rest))) = M('+':m, rest)
matchOptPm (M(m, ('-':rest))) = M('-':m, rest)
matchOptPm rest = rest

matchDigit :: Match -> Match
matchDigit (M(m, [])) = error "Unexpected EOF"
matchDigit (M(m, (ch:rest))) =
  if isDigit ch then M(ch:m, rest)
  else error $ "Expected digit (0-9), but found " ++ show ch

matchDigits :: Match -> Match
matchDigits match = (digits . matchDigit) match
    where digits (M(m,r)) = M((reverse . (takeWhile isDigit)) r ++ m, dropWhile isDigit r)

matchOptDigits :: Match -> Match
matchOptDigits (match @ (M(m, []))) = match
matchOptDigits (match @ (M(m, (ch:chs)))) =
  if isDigit ch then matchDigits match
  else match

matchOptExp :: Match -> Match
matchOptExp (M(m, ('e':chs))) = (matchDigits . matchOptPm) (M('e':m, chs))
matchOptExp (M(m, ('E':chs))) = (matchDigits . matchOptPm) (M('E':m, chs))
matchOptExp match = match

matchOptDotOptDigits :: Match -> Match
matchOptDotOptDigits (M(m, ('.':chs))) = matchOptDigits (M('.':m, chs))
matchOptDotOptDigits match = match

matchMiddle :: Match -> Match
matchMiddle (M(m, ('.':chs))) = matchDigits (M('.':m, chs))
matchMiddle match = (matchOptDotOptDigits . matchDigits) match

matchFp :: String -> Match
matchFp str = (matchOptExp . matchMiddle . matchOptPm) (M([], str))

---------------------------------------------------------------------------------------------------
------------------------------------- LEXER -------------------------------------------------------
---------------------------------------------------------------------------------------------------

lexString :: [Char] -> [Token]
lexString = (lexUtil . filter (not . isSpace))
  where
    lexUtil :: [Char] -> [Token]
    lexUtil [] = []
    lexUtil ('+':chs) = PlusToken : lexUtil chs
    lexUtil ('-':chs) = MinusToken : lexUtil chs
    lexUtil ('*':chs) = StarToken : lexUtil chs
    lexUtil ('!':chs) = ExclMarkToken : lexUtil chs
    lexUtil ('(':chs) = OpParToken : lexUtil chs
    lexUtil (')':chs) = ClParToken : lexUtil chs
    lexUtil ('c':'o':'s':chs) = CosToken : lexUtil chs
    lexUtil chs = NumberToken num : lexUtil rest
      where 
        M(fp, rest) = matchFp chs
        num = read ('0':(reverse fp)) :: Float

---------------------------------------------------------------------------------------------------
------------------------------------- PARSER ------------------------------------------------------
---------------------------------------------------------------------------------------------------

parser :: [Terminal] -> Tree GrammarSymbol
-- The LR(0) parser's state can be defined by a stack and by the rest of the input symbols. For
-- convenience we also keep track of the symbols and the constructed parsetree.
parser input = parserUtil [startState] [T EndMarker] (map T input) []
  where
    parserUtil :: [Set.Set Item] -> [GrammarSymbol] -> [GrammarSymbol] 
                                 -> [Tree GrammarSymbol] -> Tree GrammarSymbol
    parserUtil _ [NT AugStart, T EndMarker] [T EndMarker] trees =
      -- At this point the list of the trees should be of length 1, so return the head if this is
      -- the case. Otherwise the input is invalid and we should throw an exception.
      head trees
    parserUtil (stack @ (currState:_)) symbols (input @ (nextSymbol:restOfInput)) trees =
      -- Shift or reduce based on GOTO. If an empty set is returned, that means there is no shift
      -- so we have to reduce.
        if nextState /= emptySet then -- shift
          parserUtil (nextState:stack) (nextSymbol:symbols) restOfInput ((Lf nextSymbol) : trees)
        else parserUtil newStack newSymbols input newTree -- reduce
          where 
            nextState = goto currState nextSymbol 

            -- The production rule used for the reduction.
            candidates = filter (\(I(_, is)) -> last is == ItemDot) (Set.toList currState) 
            (I (nt, beta)) = head candidates
            prodRuleLength = length beta - 1
              
            -- Determine the new state of the parser. Pop prodRuleLength states from the stack and
            -- use the new obtained symbol with GOTO to get the new state. Push the new state to
            -- the stack.
            droppedStack = drop prodRuleLength stack
            newState = goto (head droppedStack) (NT nt)

            newStack = newState : droppedStack
            newSymbols = (NT nt) : (drop prodRuleLength symbols) 
            
            -- Create a new node in the tree. The new node has to have prodRuleLength children, so
            -- take as many parse subtrees from the tree stack.
            newTree = Br(NT nt, reverse $ take prodRuleLength trees) : (drop prodRuleLength trees)


-- DEBUG: example = itemClosure (Set.fromList [I(Start, [ItemDot, IS (NT E)])])
-- DEBUG: example2 = goto startState (T Id)
-- DEBUG: example3 = parser [Id, Star, Id, EndMarker]


eval strExpr = fst $ evalUtil parsedTree values
  where
    lexedStr = lexString strExpr
    values = [x | NumberToken x <- lexedStr]
    
    parsedTree = parser $ (map toTerminal lexedStr) ++ [EndMarker]
      where
        toTerminal (NumberToken _) = Number
        toTerminal PlusToken = Plus
        toTerminal MinusToken = Minus
        toTerminal StarToken = Star
        toTerminal ExclMarkToken = ExclMark
        toTerminal CosToken = Cos
        toTerminal OpParToken = OpPar
        toTerminal ClParToken = ClPar

    -- Number --
    evalUtil (Lf _) (v:vs) =
      (v,vs)

    -- AugStart --
    evalUtil (Br (NT AugStart, [augStartTree])) vs =
      evalUtil augStartTree vs

    -- Start --
    evalUtil (Br (NT Start, [startTree])) vs =
      evalUtil startTree vs

    -- E --
    evalUtil (Br (NT E, [Lf (T Plus), exprTree])) vs =
      evalUtil exprTree vs
    evalUtil (Br (NT E, [Lf (T Minus), exprTree])) vs =
      (-1.0*ret, vState) where
        (ret, vState) = evalUtil exprTree vs 
    evalUtil (Br (NT E, [e1, Lf (T Plus), e2])) vs =
      (ret1+ret2, v2) where
        (ret1, v1) = evalUtil e1 vs
        (ret2, v2) = evalUtil e2 v1
    evalUtil (Br (NT E, [e1, Lf (T Minus), e2])) vs =
      (ret1-ret2, v2) where
        (ret1, v1) = evalUtil e1 vs
        (ret2, v2) = evalUtil e2 v1
    evalUtil (Br (NT E, [termTree])) vs = 
      evalUtil termTree vs

    -- term --
    evalUtil (Br (NT Term, [t, _, ct])) vs =
      (ret1*ret2, v2) where
        (ret1, v1) = evalUtil t vs
        (ret2, v2) = evalUtil ct v1
    evalUtil (Br (NT Term, [cosTermTree])) vs =
      evalUtil cosTermTree vs

    -- costerm --
    evalUtil (Br (NT CosTerm, [_, cosTermTree])) vs =
      (cos ret, vState) where
        (ret, vState) = evalUtil cosTermTree vs
    evalUtil (Br (NT CosTerm, [factorialTermTree])) vs =
      evalUtil factorialTermTree vs

    -- factorialterm --
    evalUtil (Br (NT FactorialTerm, [factorialTermTree, _])) vs =
      (fromInteger $ fact (floor ret), vState) where
        (ret, vState) = evalUtil factorialTermTree vs
    evalUtil (Br (NT FactorialTerm, [factorTree])) vs =
      evalUtil factorTree vs

    -- factor --
    evalUtil (Br (NT Factor, [number])) vs =
      evalUtil number vs
    evalUtil (Br (NT Factor, [_ , exprTree, _])) vs =
      evalUtil exprTree vs
 

tests = [
  (eval "1", 1.0),
  (eval ".1", 0.1),
  (eval "1+1", 2.0),
  (eval ".2e+2+-1.0e2*100.02", -9982.0),
  (eval "cos 12!", -0.76619765),
  (eval "(123)", 123.0),
  (eval "1000e-3", 1.0),
  (eval "-1000e-3", -1.0),
  (eval "1*2+3*4+5*6*7", 224.0),
  (eval "cos cos cos 3!!", 0.784951602),
  (eval "1+1-1+1-1+1-1", 1.0),
  (eval "1+++        ++++  +++1", 2.0),
  (eval "- - - -1 +-+-+ 1", 2.0)]
