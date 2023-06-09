{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE TypeFamilies #-}

module PrimeTest where

import Test.Tasty
import Test.Tasty.HUnit

import Control.Intensional.Applicative
import Control.Intensional.MonadPlus
import Control.Intensional.Runtime
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Function

import PdsReachability.Reachability
import PdsReachability.Specification
import PdsReachability.UserDataTypes

tests :: TestTree
tests =
  testGroup "Prime test"
  [primeTest]

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

primeTest :: TestTree
primeTest =
  testCase "Prime test" (assertEqual "state check" [Count 3] primeFactorCountTest)
