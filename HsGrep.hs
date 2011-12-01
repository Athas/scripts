-- Haskell implementation of simple regular expressions, inspired by
-- Torben Mogensens textbook "Introduction to Compiler Design".
--
-- Character ranges are supported through translation to alternations.
-- Negative ranges are not supported.  A backslash causes the
-- following character to be read literally, even if it is normally
-- syntactically significant.  The full path from regular expressions
-- over NFAs to DFAs has been implemented, and several utility
-- functions for printing the state machines as graphs (in GraphViz
-- format) are also provided.
--
-- If compiled as an executable, the program acts as a very simple
-- `grep` clone.

module Main where
import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer
import Data.Char
import Data.Maybe
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import Text.Parsec hiding ((<|>), many)
import Text.Parsec.String

import System.Environment

-- | Simple regular expressions.  Note that there is no concept of
-- matching a string, only matching a single character, which can then
-- be combined by concatenation.
data Regexp = ReChar Char -- ^ A literal character.
            | ReEpsilon  -- ^ Nothing.
            | ReConcat Regexp Regexp -- ^ Two expressions following each other.
            | ReChoice Regexp Regexp -- ^ Either of the given expressions.
            | ReKleene Regexp -- ^ Zero or more instances of the expression.
              deriving (Show)

-- | This parser is somewhat nasty, but not very interesting.  Much of
-- the complexity stems from handling escaping.
regexp :: Parser Regexp
regexp = chainl simple (char '|' >> pure ReChoice) ReEpsilon <* eof
  where simple = chainl term (pure ReConcat) ReEpsilon
        term = kleene (between (char '(') (char ')') regexp)
               <|> kleene (between (char '[') (char ']') clss)
               <|> text
        clss = chainl1 (comp <|> chr) (pure ReChoice)
        comp = do (c1, c2) <- try $ pure (,) <*> clchr <*> (char '-' *> clchr)
                  case map ReChar [c1..c2] of
                    []     -> fail $ "Empty range " ++ [c1] ++ "-" ++ [c2]
                    (c:cs) -> return $ foldl ReChoice c cs
        text = chainl1 (kleene chr) (pure ReConcat)
        clchr = noneOf "[]" <|> char '\\' *> anyChar
        chr  = pure ReChar <*>
               (char '\\' *> anyChar <|> noneOf "()|*[]+")
        kleene p = do
          s <- p
          (char '*' >> return (ReKleene s))
             <|> (char '+' >> return (ReConcat s $ ReKleene s))
             <|> return s

parseRegexp :: SourceName -> String -> Either ParseError Regexp
parseRegexp = parse regexp

-- | An NFA state is uniquely identified by an integer.
type NFAState = Int
-- | A transition in an NFA is either by a concrete character or an epsilon.
data Symbol = Symbol Char
            | Epsilon
              deriving (Eq, Ord, Show)
-- | The transitions in an NFA are a mapping from symbols to sets of
-- states (as a single symbol may lead to one of several possible
-- states, hence the nondeterminism).
type NFATransitions = M.Map Symbol (S.Set NFAState)

data NFA = NFA { nfaStates      :: S.Set NFAState -- ^ The set of states in the NFA.
               , nfaStartState  :: NFAState -- ^ The unique starting state.
               , nfaTransitions :: M.Map NFAState NFATransitions
                                   -- ^ A mapping from a state to the transitions going out of it.
               , nfaAccepting   :: S.Set NFAState
               -- ^ The set of accepting states (can be empty,
               -- although such an NFA would not be very useful, and
               -- annot be constructed via regular expressions.)
               }
         deriving (Show)

-- | We represent DFA states by sets of NFA states.  This is really
-- unnecessary, they could be unique integers instead, but it makes
-- the subset construction algorithm slightly more convenient.
type DFAState = S.Set NFAState
-- | DFA transitions are maps from concrete characters to a single
-- state.
type DFATransitions = M.Map Char DFAState

data DFA = DFA { dfaStates      :: S.Set DFAState
               , dfaStartState  :: DFAState
               , dfaTransitions :: M.Map DFAState DFATransitions
               , dfaAccepting   :: S.Set DFAState }
         deriving (Show)

runDFA :: DFA -> String -> Maybe (String, String)
runDFA dfa str' = runDFA' str' (dfaStartState dfa)
  where runDFA' str s
          | s `S.member` dfaAccepting dfa =
            consume str s <|> Just ("", str)
          | otherwise = consume str s
        consume [] _ = Nothing
        consume (c:cs) s =
          case M.lookup s $ dfaTransitions dfa of
            Nothing -> error "Invalid DFA"
            Just ts -> prepend c <$> (runDFA' cs =<< M.lookup c ts)
        prepend c (a,b) = (c:a, b)

-- | Compute the complete epsilon closure for the given set of NFA
-- states in the given NFA.  This is done by repeatedly calling
-- 'eTransitions' until we reach a fixed point.
eClosure :: NFA -> S.Set NFAState -> DFAState
eClosure nfa t = if t' `S.isSubsetOf` t then t
                 else eClosure nfa $ t' `S.union` t
  where t' = eTransitions nfa t

-- | @eTransitions' nfa ss@ is the states reachable by the states in @ss@
-- via epsilon-transitions, which does not necessarily include @ss@
-- itself.
eTransitions :: NFA -> S.Set NFAState -> S.Set NFAState
eTransitions nfa ss = S.unions $ map f (S.toList ss)
  where f s = S.unions (map snd eTransitions)
          where eTransitions = filter ((==Epsilon) . fst) transitions
                transitions = maybe [] M.toList $ M.lookup s $ nfaTransitions nfa

-- | Convert an NFA to a DFA using subset construction.
nfaToDFA :: NFA -> DFA
nfaToDFA nfa = dfa' { dfaAccepting = S.filter accepting $ dfaStates dfa' }
  -- We start by constructing a DFA consisting of nothing but the
  -- starting state, then using nfaToDFA' to perform the actual work.
  where dfa = DFA { dfaStates = S.singleton start
                  , dfaStartState = start
                  , dfaTransitions = M.empty
                  , dfaAccepting = S.empty }
        dfa' = nfaToDFA' nfa dfa [] [start]
        start = eClosure nfa $ S.singleton $ nfaStartState nfa
        accepting = not . S.null . S.intersection (nfaAccepting nfa)

nfaToDFA' :: NFA -> DFA -> [DFAState] -> [DFAState] -> DFA
nfaToDFA' _ dfa _ [] = dfa
nfaToDFA' nfa dfa seen (s:ss) = nfaToDFA' nfa dfa' (s:seen) ss'
  where dfa' = dfa { dfaStates = foldr S.insert (dfaStates dfa) (M.elems ts)
                   , dfaTransitions = M.insert s ts (dfaTransitions dfa) }
        ss' = union ss (M.elems ts) \\ seen
        ts = M.map (eClosure nfa) $
             foldl (M.unionWith S.union) M.empty $
             map transitions $ S.toList s
        transitions = maybe M.empty (M.foldlWithKey noepsilons M.empty)
                      . flip M.lookup (nfaTransitions nfa)
        noepsilons m Epsilon _ = m
        noepsilons m (Symbol c) v = M.insert c v m

-- | Convert a regular expression to an NFA.  Runs in a state monad
-- solely so we can generate unique numbers for representing the NFA
-- states.
regexpToNfa :: Regexp -> NFA
regexpToNfa regex =
  flip evalState 0 $ do
    start <- newstate
    end <- newstate
    (states, trs) <- regexpToNFA' regex start end
    return NFA { nfaStates = S.fromList [start,end] `S.union` states
               , nfaStartState = start
               , nfaTransitions = trs
               , nfaAccepting = S.singleton end }
  where newstate = do v <- get
                      put (v+1)
                      return v
        connect from c to = M.singleton from (M.singleton c (S.singleton to))
        combine = M.unionWith (M.unionWith S.union)
        regexpToNFA' (ReChar c) from to =
          return (S.empty, connect from (Symbol c) to)
        regexpToNFA' (ReEpsilon) from to =
          return (S.empty, connect from Epsilon to)
        regexpToNFA' (ReConcat t1 t2) from to = do
          s <- newstate
          (t1', trs1) <- regexpToNFA' t1 from s
          (t2', trs2) <- regexpToNFA' t2 s to
          return ( s `S.insert` t1' `S.union` t2'
                 , trs1 `combine` trs2)
        regexpToNFA' (ReChoice t1 t2) from to = do
          (t1', trs1) <- regexpToNFA' t1 from to
          (t2', trs2) <- regexpToNFA' t2 from to
          return ( t1' `S.union` t2', trs1 `combine` trs2 )
        regexpToNFA' (ReKleene t) from to = do
          s <- newstate
          (t', trs) <- regexpToNFA' t s s
          return ( s `S.insert` t'
                 , trs
                   `combine` connect from Epsilon s
                   `combine` connect s Epsilon to )

initialMatch :: Regexp -> String -> Maybe (String, String)
initialMatch regex str = runDFA dfa str
  where dfa = nfaToDFA $ regexpToNfa regex

-- The real work is done.  The functions below deal with printing NFAs
-- and DFAs in Graphviz format.

match :: Regexp -> String -> Bool
match r str =
  isJust (initialMatch r str) ||
  case str of [] -> False
              (_:cs) -> match r cs

class Ord a => Next a where
  next :: a -> a

instance Next Symbol where
  next Epsilon = Epsilon
  next (Symbol c) = Symbol $ chr $ ord c + 1

instance Next Char where
  next c = chr (ord c + 1)

ranges :: (Next a, Ord b) => [(a, b)] -> [([(a,a)], b)]
ranges = map ranges' . M.toList . foldl arrange M.empty
  where arrange m (k, v) = M.insertWith (++) v [k] m
        ranges' (v, ks) = (foldl ranges'' [] $ sort ks, v)
        ranges'' [] x = [(x,x)]
        ranges'' ((y1,y2):ys) x
          | next y2 == x = (y1, x) : ys
          | otherwise = (x,x) : (y1,y2) : ys

-- | Escape the double-quotes in a string so it can be put in a
-- Graphviz string.
escape :: String -> String
escape [] = []
escape ('"':s) = "\\\"" ++ escape s
escape (c:s) = c : escape s

translabel :: Next a => (a -> String) -> [(a,a)] -> String
translabel f [(x,y)] | x == y = f x
                     | otherwise = "[" ++ f x ++ "-" ++ f y ++ "]"
translabel f xs = "[" ++ concatMap charclass xs ++ "]"
  where charclass (x,y) | x == y = f x
                        | otherwise = f x ++ "-" ++ f y

statelabel :: String -> Int -> Bool -> String
statelabel k i a =
  k ++ "[label=\"" ++ show i ++ "\"" ++
      (if a then ", shape=doublecircle" else "shape=circle")
      ++ "]\n"

printNFA :: NFA -> String
printNFA nfa = evalState (execWriterT printNFA') (M.empty,0::Int)
  where node k = do
          (s, v) <- get
          case M.lookup k s of
            Just v' -> return v'
            Nothing -> do
              let v' = v+1
                  v'' = 'S' : show v'
              tell $ statelabel v'' v' $ k `S.member` nfaAccepting nfa
              put (M.insert k v'' s, v')
              return v''
        symbol Epsilon = "epsilon"
        symbol (Symbol c) = [c]
        trans (from, ts) =
          forM_ (ranges $ M.toList ts) $ \(clss, tos) ->
            forM_ (S.toList tos) $ \to -> do
              from' <- node from
              to' <- node to
              tell $ from' ++ "->" ++ to' ++
                     " [label=\"" ++ escape (translabel symbol clss) ++ "\"]\n"
        printNFA' = do
          tell "digraph nfa {\nrankdir=TD\nEmp [style=invisible]\n"
          mapM_ trans $ M.toList $ nfaTransitions nfa
          tell "}\n"

printDFA :: DFA -> String
printDFA dfa = evalState (execWriterT printDFA') (M.empty,0::Int)
  where node k = do
          (s, v) <- get
          case M.lookup k s of
            Just v' -> return v'
            Nothing -> do
              let v' = v+1
                  v'' = 'S' : show v'
              tell $ statelabel v'' v $ k `S.member` dfaAccepting dfa
              put (M.insert k v'' s, v')
              return v''
        trans (from, ts) =
          forM_ (ranges $ M.toList ts) $ \(clss, to) -> do
            from' <- node from
            to' <- node to
            tell $ from' ++ "->" ++ to' ++
                   " [label=\"" ++ escape (translabel (:[]) clss) ++ "\"]\n"
        printDFA' = do
          tell "digraph dfa {\nrankdir=LR\nEmp [style=invisible]\n"
          mapM_ trans $ M.toList $ dfaTransitions dfa
          tell "}\n"

compileRegexp :: SourceName -> String -> Either ParseError NFA
compileRegexp s r = regexpToNfa <$> parseRegexp s r

printRegexpDFA :: String -> String
printRegexpDFA regex = printDFA $ nfaToDFA nfa
  where nfa = case compileRegexp "command-line" regex of
                Left e  -> error $ show e
                Right v -> v

printRegexpNFA :: String -> String
printRegexpNFA regex = printNFA nfa
  where nfa = case compileRegexp "command-line" regex of
                Left e  -> error $ show e
                Right v -> v

-- | Finally, a simple program entry point.
main :: IO ()
main = do
  args <- getArgs
  prog <- getProgName
  case args of
    ["grep", r] -> grep r
    ["nfa",  r] -> putStr $ printRegexpNFA r
    ["dfa",  r] -> putStr $ printRegexpDFA r
    _ -> error $ "Usage: " ++ prog ++ " <grep | nfa | dfa> regexp"
  where grep r = case parseRegexp "command-line" r of
                   Left e   -> error $ show e
                   Right r' -> interact (unlines . filter (match r') . lines)
