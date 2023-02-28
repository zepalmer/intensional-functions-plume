{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE TypeFamilies #-}

module Main where

import Control.Intensional.Applicative
import Control.Intensional.Monad.Identity
import Control.Intensional.MonadPlus
import Control.Intensional.Runtime
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Function

import qualified Closure.Intensional.Indexed.Engine as ICE
import PdsReachability.Reachability
import PdsReachability.Specification
import PdsReachability.UserDataTypes

data PrimeTest

data State
  = Number Int
  | Count Int
  deriving (Eq, Ord, Show)

data StackElm
  = Bottom
  | Prime Int
  deriving (Eq, Ord, Show)

type instance Node PrimeTest = State
type instance Element PrimeTest = StackElm

allFactsIndex :: a ->%Ord Maybe ((),a)
allFactsIndex = \%Ord x -> Just ((),x)

isPrime :: Int -> Bool
isPrime n =
    let divide k =
          if k <= 1 then True else
          if mod n k == 0 then False else
          divide (k - 1)
    in
    if n == 1 then False else divide (n-1)

primeFactorCountAnalysis :: Analysis PrimeTest
primeFactorCountAnalysis =
    emptyAnalysis
    & addManyPathComputation
        (\%Ord node -> case node of
            Number n -> intensional Ord do
                          k <- pdrmChoose $ [1..n]
                          itsGuard %@ isPrime k
                          itsGuard %@ (n `mod` k == 0)
                          itsPure %@
                            ( Path [Push $ Prime k]
                            , Number $ div n k
                            )
            Count _ -> itsMzero
        )
    & addEdge (Edge (Number 1) Nop (Count 0))
    & addManyPathComputation
        (\%Ord node -> case node of
            Number _ -> itsMzero
            Count n -> intensional Ord do
                        item <- pop
                        case item of
                            Bottom -> itsPure %@ ( Path [], node )
                            _ -> itsPure %@ ( Path [], Count $ n + 1 )
        )
    & addQuestion (Question (Number 12) [Push Bottom])
    & fullClosure

primeFactorCountTest :: [State]
primeFactorCountTest =
  case (getReachableNodes
          (Question (Number 12) [Push Bottom])
          primeFactorCountAnalysis) of
    Just res -> res
    Nothing -> []

newtype PWrapNode = PWrapNode (InternalNode PrimeTest)
    deriving (Eq, Ord)
newtype PWrapFact = PWrapFact (Fact PrimeTest)
    deriving (Eq, Ord)

instance Show PWrapNode where
    show (PWrapNode node) =
        case node of
            UserNode (Number n) -> "Num " ++ show n
            UserNode (Count n) -> "Count " ++ show n
            IntermediateNode actions node ->
                "(" ++ show actions ++ " => " ++ show node ++ ")"

instance Show PWrapFact where
    show (PWrapFact fact) =
        case fact of
            EdgeFact source action dest ->
                show source ++ " --- " ++ show action ++ " --> " ++ show dest
            NodeFact node ->
                show $ PWrapNode node
            ActiveFact node ->
                (show $ PWrapNode node) ++ " is active"

main :: IO ()
main = do
    putStrLn "-----------------------------------------"
    print $ primeFactorCountTest
    putStrLn "~~~~"
    let IntensionalIdentity closureEngine = ICE.close $ ICE.addIndex allFactsIndex $ analysisEngine primeFactorCountAnalysis
    let allFacts = Set.map PWrapFact $ ICE.getAllIndexedFacts allFactsIndex () closureEngine
    putStrLn $ allFacts
             & Set.toList
             & List.foldl
                (\a e ->
                    a ++ (if a == "" then "" else "\n") ++
                    show e
                )
                ""
    pure ()