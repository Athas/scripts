-- Haskell implementation of simple regular expressions, inspired by
-- Torben Mogensens textbook "Introduction to Compiler Design".
--
-- Character ranges are supported through translation to alternations.
-- Negative ranges are not supported.  The full path from regular
-- expressions over NFAs to DFAs has been implemented, and several
-- utility functions for printing the state machines as graphs (in
-- GraphViz format) are also provided.
--
-- If compiled as an executable, the program acts as a very simple
-- `grep` clone.
--
module Main where
import Control.Applicative
import Control.Monad.State
import Control.Monad.Writer
import Data.Maybe
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S

import Text.Parsec hiding ((<|>), many)
import Text.Parsec.String

import System.Environment

data Regexp = ReChar Char
            | ReEpsilon
            | ReConcat Regexp Regexp
            | ReChoice Regexp Regexp
            | ReKleene Regexp
              deriving (Show)

regexp :: Parser Regexp
regexp = chainl simple (char '|' >> pure ReChoice) ReEpsilon
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
        clchr = noneOf "[]"
        chr  = pure ReChar <*> noneOf "()|*[]"
        kleene p = do s <- p
                      (char '*' >> return (ReKleene s)) <|> return s

type NFAState = Int
data Symbol = Symbol Char
            | Epsilon
              deriving (Eq, Ord, Show)

data NFA = NFA { nfaStates      :: S.Set NFAState
               , nfaStartState  :: NFAState
               , nfaTransitions :: M.Map NFAState (M.Map Symbol (S.Set NFAState))
               , nfaAccepting   :: S.Set NFAState }
         deriving (Show)

type DFAState = S.Set NFAState

data DFA = DFA { dfaStates      :: S.Set DFAState
               , dfaStartState  :: DFAState
               , dfaTransitions :: M.Map DFAState (M.Map Char DFAState)
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

eClosure :: NFA -> S.Set NFAState -> DFAState
eClosure nfa t = if t' `S.isSubsetOf` t then t
                 else eClosure nfa $ t' `S.union` t
  where t' = eClosure' nfa t

eClosure' :: NFA -> S.Set NFAState -> S.Set NFAState
eClosure' nfa ss = S.unions $ map f (S.toList ss)
  where f s = S.unions (map snd eTransitions)
          where eTransitions = filter ((==Epsilon) . fst) transitions
                transitions = maybe [] M.toList $ M.lookup s $ nfaTransitions nfa

nfaToDFA :: NFA -> DFA
nfaToDFA nfa = dfa' { dfaAccepting = S.filter accepting $ dfaStates dfa' }
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

compileRegexp :: SourceName -> String -> Either ParseError NFA
compileRegexp name s = regexpToNfa <$> parse regexp name s

initialMatch :: Regexp -> String -> Maybe (String, String)
initialMatch regex str = runDFA dfa str
  where dfa = nfaToDFA $ regexpToNfa regex

initialMatch_ :: String -> String -> Maybe (String, String)
initialMatch_ regex = initialMatch regex'
  where regex' = case parse regexp "" regex of
                   Left e  -> error $ show e
                   Right v -> v

match :: Regexp -> String -> Bool
match r str =
  isJust (initialMatch r str) ||
  case str of [] -> False
              (_:cs) -> match r cs

printNFA :: NFA -> String
printNFA nfa = evalState (execWriterT printNFA') (M.empty,0::Int)
  where node k = do
          (s, v) <- get
          case M.lookup k s of
            Just v' -> return v'
            Nothing -> do
              let accepting = k `S.member` nfaAccepting nfa
                  v' = v+1
                  v'' = 'S' : show v'
              tell $ v'' ++ "[label=\"" ++ show v' ++ "\"" ++
                     (if accepting then ", shape=doublecircle" else "")
                     ++ "]\n"
              put (M.insert k v'' s, v')
              return v''
        symbol Epsilon = "epsilon"
        symbol (Symbol c) = [c]
        trans (from, ts) = forM_ (M.toList ts) $ \(sym, tos) ->
                             forM_ (S.toList tos) $ \to -> do
                               from' <- node from
                               to' <- node to
                               tell $ from' ++ "->" ++ to' ++
                                      " [label=\"" ++ symbol sym ++ "\"]\n"
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
              let accepting = k `S.member` dfaAccepting dfa
                  v' = v+1
                  v'' = 'S' : show v'
              tell $ v'' ++ "[label=\"" ++ show v' ++ "\"" ++
                     (if accepting then ", shape=doublecircle" else "")
                     ++ "]\n"
              put (M.insert k v'' s, v')
              return v''
        trans (from, ts) = forM_ (M.toList ts) $ \(sym, to) -> do
                             from' <- node from
                             to' <- node to
                             tell $ from' ++ "->" ++ to' ++
                                    " [label=\"" ++ [sym] ++ "\"]\n"
        printDFA' = do
          tell "digraph dfa {\nrankdir=LR\nEmp [style=invisible]\n"
          mapM_ trans $ M.toList $ dfaTransitions dfa
          tell "}\n"

printRegexp :: String -> String
printRegexp regex = printDFA $ nfaToDFA nfa
  where nfa = case compileRegexp "" regex of
                Left e  -> error $ show e
                Right v -> v

main :: IO ()
main = do
  args <- getArgs
  prog <- getProgName
  case args of
    [r] -> case parse regexp "command-line" r of
             Left e   -> error $ show e
             Right r' -> interact (unlines . filter (match r') . lines)
    _ -> error $ "Usage: " ++ prog ++ " regexp"
