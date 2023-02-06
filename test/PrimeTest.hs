{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE EmptyDataDeriving #-}

module PrimeTest where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Set as S
import qualified Data.List as L
import Data.Function
import PdsReachability.Reachability
import PdsReachability.Specification
import PdsReachability.Structure
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

data StateClass
  = NumberClass
  | CountClass
  deriving (Eq, Ord, Show)

data StackElm
  = Bottom Char
  | Prime Int
  deriving (Eq, Ord, Show)

data PrimeDynPop
  = PopAnythingBut StackElm
  deriving (Eq, Ord, Show)

data PrimeUntDynPop
  deriving (Eq, Ord, Show)

type instance Node PrimeTest = State
type instance NodeClass PrimeTest = StateClass
type instance Element PrimeTest = StackElm
type instance TargetedDynPop PrimeTest = PrimeDynPop
type instance UntargetedDynPop PrimeTest = PrimeUntDynPop

classifyState :: State -> StateClass
classifyState (Number _) = NumberClass
classifyState (Count _) = CountClass

doDynPopPrime :: PrimeDynPop -> Element PrimeTest -> [Path PrimeTest]
doDynPopPrime dpf element =
  case dpf of
    PopAnythingBut se ->
      if (element == se) then [] else [Path []]

doUntargetedDynPopPrime :: PrimeUntDynPop -> Element PrimeTest -> [(Path PrimeTest, Terminus PrimeTest)]
doUntargetedDynPopPrime _ _ = []

primeFactorCountAnalysis :: Analysis PrimeTest
primeFactorCountAnalysis =
  let isPrime = \n ->
        let divide = \k ->
              if (k <= 1) then True else
                case (mod n k) of 0 -> False
                                  otherwise -> divide (k-1)
        in
        case n of 1 -> False
                  _ -> divide (n-1)
  in
  let isFactor n k = if (mod n k == 0) then True else False
  in
  let start = Number 12 in
  emptyAnalysis classifyState doDynPopPrime doUntargetedDynPopPrime
  & addEdgeFunction (Just NumberClass)
      (EdgeFunction (\state ->
                        case state of
                          Number n ->
                            let leqState = [1..n] in
                            let primesLeqState = L.filter isPrime leqState in
                            let primeFactors = L.filter (isFactor n) primesLeqState in
                            L.map (\k -> (Path [Push (Prime k)], StaticTerminus (Number (div n k)))) primeFactors
                          Count _ -> []
                    ))
  & addAnalysisEdge (RegularEdge (Edge (UserNode (Number 1)) Nop (UserNode (Count 0))))
  & addEdgeFunction (Just CountClass)
      (EdgeFunction (\state ->
                case state of
                  Count c -> [(Path [DynamicPop (PopAnythingBut(Bottom '$'))], StaticTerminus (Count (c+1)))]
                  Number _ -> []
            ))
  & addEdgeFunction (Just CountClass)
      (EdgeFunction (\state ->
                case state of
                  Count _ ->
                    [(Path [Pop (Bottom '$')], StaticTerminus state)]
                  Number _ -> []
            ))
  & addQuestion (Question start [Push (Bottom '$')])
  & fullClosure

primeFactorCountTest :: [State]
primeFactorCountTest =
  let start = Number 12 in
  case (getReachableNodes
          (Question start [Push (Bottom '$')])
          primeFactorCountAnalysis) of
    Just res -> res
    Nothing -> []

primeTest :: TestTree
primeTest =
  testCase "Prime test" (assertEqual "state check" [Count 3] primeFactorCountTest)
