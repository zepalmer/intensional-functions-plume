{-# LANGUAGE TypeFamilies #-}

module Spec where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Set as S
import Data.Function
import PdsReachability.Reachability
import PdsReachability.Specification
import PdsReachability.Structure
import PdsReachability.UserDataTypes

data Test

type instance Node Test = String
type instance NodeClass Test = ()
type instance Element Test = String
type instance TargetedDynPop Test = DynPop
type instance UntargetedDynPop Test = UntDynPop

-- type Analysis Test = Analysis String String DynPopFun
-- type ActiveNodes Test = ActiveNodes String String DynPopFun
-- type EdgeFunction Test = EdgeFunction String String DynPopFun
-- type Graph Test = Graph String String DynPopFun
-- type (Edge Test) = Edge String String DynPopFun
-- type TestNode = Node String String DynPopFun
-- type TestPath = Path String DynPopFun

data DynPop
  = DynPop1
  | DynPop2 deriving (Eq, Ord, Show)

data UntDynPop
  = UntDynPop1
  deriving (Eq, Ord, Show)

doDynPop1 :: DynPop -> Element Test -> [Path Test]
doDynPop1 dpf se =
  case dpf of
    DynPop1 -> [Path [Push "II", Push "IV", Push "VI", Push se, Push "I"]]
    DynPop2 -> [Path [Push "1", Push "1", Push "1"]]

doUntargetedDynPop1 :: UntDynPop -> Element Test -> [(Path Test, Terminus Test)]
doUntargetedDynPop1 udpf se =
  case udpf of
    UntDynPop1 -> []

edgeFun1 :: EdgeFunction Test
edgeFun1 = EdgeFunction (\n ->
  case n of
    "b" -> [(Path [Pop "x"], (StaticTerminus "c"))]
    otherwise -> [])

tests :: TestTree
tests =
  testGroup "Spec tests"
  [pushPopTest,
   pushPopTest2,
   pushNopTest,
   popNopTest,
   nopNopTest,
   biggerTest1,
   dynPopTest1,
   dynPopTest2,
   activeNodesTest1,
   addEdgeFunBeforeActiveTest,
   addEdgeFunAfterActiveTest,
   extraWorkTest
  ]

setActiveNodes ::
 ActiveNodes Test ->
 Analysis Test ->
 Analysis Test
setActiveNodes (ActiveNodes actives) analysis =
  S.foldl (flip addActiveNode) analysis actives

setEdgeFunctions ::
 [EdgeFunction Test] ->
 Analysis Test ->
 Analysis Test
setEdgeFunctions efs analysis =
  foldl (flip $ addEdgeFunction Nothing) analysis efs

-- fullAnalysis :: Graph Test -> Analysis Test
-- fullAnalysis g =
--   let edges = getEdges g in
--   let actives = S.map (\(Edge n1 _ _) -> n1) edges in
--   let initialAnalysis = S.foldl (\acc -> \e -> updateAnalysis e acc) (emptyAnalysis doDynPop1 actives) edges in
--   fullClosure initialAnalysis

emptyTestAnalysis :: Analysis Test
emptyTestAnalysis = emptyAnalysis (const ()) doDynPop1 doUntargetedDynPop1

graphClosure :: Graph Test -> Graph Test
graphClosure g =
  let edges = S.map (\e -> RegularEdge e) (getEdges g) in
  let utedges = S.map (\e -> UntargetedEdge e) (getUntargetedDynPopEdges g) in
  -- TODO: Handle utedges
  let actives = ActiveNodes $ S.map (\(RegularEdge (Edge n1 _ _)) -> n1) edges in
  let preparedAnalysis = setActiveNodes actives emptyTestAnalysis in
  let initialAnalysis = S.foldl (\acc -> \e -> addAnalysisEdge e acc) preparedAnalysis edges in
  let fullAnalysis = fullClosure initialAnalysis in
  getGraph fullAnalysis

-- graphClosureWithActives :: ActiveNodes Test -> Graph Test -> Graph Test
-- graphClosureWithActives actives g =
--   let edges = getEdges g in
--   let preparedAnalysis = (emptyAnalysis doDynPop1) { activeNodes = actives } in
--   let initialAnalysis = S.foldl (\acc -> \e -> addAnalysisEdge e acc) preparedAnalysis edges in
--   let fullAnalysis = fullClosure initialAnalysis in
--   getGraph fullAnalysis

graphClosureWithActives :: ActiveNodes Test -> Graph Test -> Graph Test
graphClosureWithActives actives g =
  let edges = S.map (\e -> RegularEdge e) (getEdges g) in
  let utedges = S.map (\e -> UntargetedEdge e) (getUntargetedDynPopEdges g) in
  -- TODO: Handle utedges
  let initialAnalysis = S.foldl (\acc -> \e -> addAnalysisEdge e acc)
        (emptyTestAnalysis) edges in
  let preparedAnalysis = setActiveNodes actives initialAnalysis in
  let fullAnalysis = fullClosure preparedAnalysis in
  getGraph fullAnalysis

-- NOTE: Add Edge Function when the nodes aren't active
graphClosureWithEdgeFun1 :: [EdgeFunction Test] -> Graph Test -> Graph Test
graphClosureWithEdgeFun1 efs g =
  let edges = S.map (\e -> RegularEdge e) (getEdges g) in
  let utedges = S.map (\e -> UntargetedEdge e) (getUntargetedDynPopEdges g) in
  -- TODO: Handle utedges
  let actives = ActiveNodes $ S.map (\(RegularEdge (Edge n1 _ _)) -> n1) edges in
  let preparedAnalysis =
        (emptyTestAnalysis)
        & setEdgeFunctions efs
        & setActiveNodes actives
  in
  let initialAnalysis = S.foldl (\acc -> \e -> addAnalysisEdge e acc) preparedAnalysis edges in
  let fullAnalysis = fullClosure initialAnalysis in
  getGraph fullAnalysis

  -- NOTE: Add Edge Function after the nodes are active
graphClosureWithEdgeFun2 :: [EdgeFunction Test] -> Graph Test -> Graph Test
graphClosureWithEdgeFun2 efs g =
  let edges = S.map (\e -> RegularEdge e) (getEdges g) in
  let utedges = S.map (\e -> UntargetedEdge e) (getUntargetedDynPopEdges g) in
  -- TODO: Handle utedges
  let actives = ActiveNodes $ S.map (\(RegularEdge (Edge n1 _ _)) -> n1) edges in
  let preparedAnalysis =
        (emptyTestAnalysis)
        & setActiveNodes actives
  in
  let initialAnalysis =
        S.foldl (\acc -> \e -> addAnalysisEdge e acc) preparedAnalysis edges
        & setEdgeFunctions efs
  in
  let fullAnalysis = fullClosure initialAnalysis in
  getGraph fullAnalysis

graphClosureWithFullSpec ::
  ActiveNodes Test ->
  [EdgeFunction Test] ->
  Graph Test ->
  Graph Test
graphClosureWithFullSpec actives efs g =
  let edges = S.map (\e -> RegularEdge e) (getEdges g) in
  let utedges = S.map (\e -> UntargetedEdge e) (getUntargetedDynPopEdges g) in
  -- TODO: Handle utedges
  let initialAnalysis = S.foldl (\acc -> \e -> addAnalysisEdge e acc)
        (emptyTestAnalysis) edges in
  let preparedAnalysis =
        setActiveNodes actives initialAnalysis
        & setEdgeFunctions efs
  in
  let fullAnalysis = fullClosure preparedAnalysis in
  getGraph fullAnalysis

-- First test: Push + Pop matching stack element
pushPopTestSet :: S.Set (Edge Test)
pushPopTestSet =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "x") (UserNode "c"),
     Edge (UserNode "a") Nop (UserNode "c")]

pushPopTestRes :: Graph Test
pushPopTestRes = graphFromEdges pushPopTestSet

pushPopTestSetInit :: S.Set (Edge Test)
pushPopTestSetInit =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "x") (UserNode "c")]

pushPopTestInit :: Graph Test
pushPopTestInit = graphFromEdges pushPopTestSetInit

pushPopTest :: TestTree
pushPopTest = testCase "Testing push + pop (matching stack element)"
  (assertEqual "Should have a nop edge" pushPopTestRes (graphClosure pushPopTestInit))

-- Second Test: Push + Pop non-matching stack element
pushPopTestSet2 :: S.Set (Edge Test)
pushPopTestSet2 =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "y") (UserNode "c")]

pushPopTestRes2 :: Graph Test
pushPopTestRes2 = graphFromEdges pushPopTestSet2

pushPopTestSetInit2 :: S.Set (Edge Test)
pushPopTestSetInit2 =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "y") (UserNode "c")]

pushPopTestInit2 :: Graph Test
pushPopTestInit2 = graphFromEdges pushPopTestSetInit2

pushPopTest2 :: TestTree
pushPopTest2 = testCase "Testing push + pop (non-matching stack element)"
  (assertEqual "Should not have a nop edge" pushPopTestRes2 (graphClosure pushPopTestInit2))

-- Third Test: Push + Nop
pushNopTestSet :: S.Set (Edge Test)
pushNopTestSet =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") Nop (UserNode "c"),
     Edge (UserNode "a") (Push "x") (UserNode "c")]

pushNopTestRes :: Graph Test
pushNopTestRes = graphFromEdges pushNopTestSet

pushNopTestSetInit :: S.Set (Edge Test)
pushNopTestSetInit =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") Nop (UserNode "c")]

pushNopTestInit :: Graph Test
pushNopTestInit = graphFromEdges pushNopTestSetInit

pushNopTest :: TestTree
pushNopTest = testCase "Testing push + nop"
  (assertEqual "Should have form a nop edge" pushNopTestRes (graphClosure pushNopTestInit))

-- Third Test: Pop + Nop
popNopTestSet :: S.Set (Edge Test)
popNopTestSet =
  S.fromList
    [Edge (UserNode "a") (Pop "x") (UserNode "b"),
     Edge (UserNode "b") Nop (UserNode "c")]

popNopTestRes :: Graph Test
popNopTestRes = graphFromEdges popNopTestSet

popNopTestSetInit :: S.Set (Edge Test)
popNopTestSetInit =
  S.fromList
    [Edge (UserNode "a") (Pop "x") (UserNode "b"),
     Edge (UserNode "b") Nop (UserNode "c")]

popNopTestInit :: Graph Test
popNopTestInit = graphFromEdges popNopTestSetInit

popNopTest :: TestTree
popNopTest = testCase "Testing pop + nop"
  (assertEqual "Should not have new edges" popNopTestRes (graphClosure popNopTestInit))

-- Fourth Test: Nop + Nop
nopNopTestSet :: S.Set (Edge Test)
nopNopTestSet =
  S.fromList
    [Edge (UserNode "a") Nop (UserNode "b"),
     Edge (UserNode "b") Nop (UserNode "c"),
     Edge (UserNode "a") Nop (UserNode "c")]

nopNopTestRes :: Graph Test
nopNopTestRes = graphFromEdges nopNopTestSet

nopNopTestSetInit :: S.Set (Edge Test)
nopNopTestSetInit =
  S.fromList
    [Edge (UserNode "a") Nop (UserNode "b"),
     Edge (UserNode "b") Nop (UserNode "c")]

nopNopTestInit :: Graph Test
nopNopTestInit = graphFromEdges nopNopTestSetInit

nopNopTest :: TestTree
nopNopTest = testCase "Testing nop + nop"
  (assertEqual "Should have a new edge" nopNopTestRes (graphClosure nopNopTestInit))

-- Fifth Test: Complex 1
biggerTestSet1 :: S.Set (Edge Test)
biggerTestSet1 =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "y") (UserNode "c"),
     Edge (UserNode "b") Nop (UserNode "c"),
     Edge (UserNode "c") Nop (UserNode "d"),
     Edge (UserNode "a") (Push "x") (UserNode "c"),
     Edge (UserNode "b") Nop (UserNode "d"),
     Edge (UserNode "a") (Push "x") (UserNode "d")]

biggerTestRes1 :: Graph Test
biggerTestRes1 = graphFromEdges biggerTestSet1

biggerTestSetInit1 :: S.Set (Edge Test)
biggerTestSetInit1 =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "y") (UserNode "c"),
     Edge (UserNode "b") Nop (UserNode "c"),
     Edge (UserNode "c") Nop (UserNode "d")]

biggerTestInit1 :: Graph Test
biggerTestInit1 = graphFromEdges biggerTestSetInit1

biggerTest1 :: TestTree
biggerTest1 = testCase "Testing bigger test case"
  (assertEqual "Should have multiple new edges" biggerTestRes1 (graphClosure biggerTestInit1))

-- Sixth Test: DynamicPop 1
dynPopTestSet1 :: S.Set (Edge Test)
dynPopTestSet1 =
  S.fromList
    [Edge (UserNode "a") (Push "NULLA") (UserNode "b"),
     Edge (UserNode "b") (DynamicPop DynPop1) (UserNode "c"),
     Edge (UserNode "a") (Push "II")
            (IntermediateNode ([Push "IV", Push "VI", Push "NULLA", Push "I"]) (StaticDestination $ UserNode "c")),
     Edge (IntermediateNode ([Push "IV", Push "VI", Push "NULLA", Push "I"]) (StaticDestination $ UserNode "c"))
            (Push "IV") (IntermediateNode ([Push "VI", Push "NULLA", Push "I"]) (StaticDestination $ UserNode "c")),
     Edge (IntermediateNode ([Push "VI", Push "NULLA", Push "I"]) (StaticDestination $ UserNode "c"))
            (Push "VI") (IntermediateNode ([Push "NULLA", Push "I"]) (StaticDestination $ UserNode "c")),
     Edge (IntermediateNode ([Push "NULLA", Push "I"]) (StaticDestination $ UserNode "c"))
            (Push "NULLA") (IntermediateNode ([Push "I"]) (StaticDestination $ UserNode "c")),
     Edge (IntermediateNode ([Push "I"]) (StaticDestination $ UserNode "c")) (Push "I") (UserNode "c")
    ]

dynPopTestRes1 :: Graph Test
dynPopTestRes1 = graphFromEdges dynPopTestSet1

dynPopTestSetInit1 :: S.Set (Edge Test)
dynPopTestSetInit1 =
  S.fromList
    [Edge (UserNode "a") (Push "NULLA") (UserNode "b"),
     Edge (UserNode "b") (DynamicPop DynPop1) (UserNode "c")]

dynPopTestInit1 :: Graph Test
dynPopTestInit1 = graphFromEdges dynPopTestSetInit1

dynPopTest1 :: TestTree
dynPopTest1 = testCase "Testing push + dynpop"
  (assertEqual "Should have many new edges" dynPopTestRes1 (graphClosure dynPopTestInit1))

-- Seventh Test: DynamicPop 2
dynPopTestSet2 :: S.Set (Edge Test)
dynPopTestSet2 =
  S.fromList
    [Edge (UserNode "a") (Push "5") (UserNode "b"),
     Edge (UserNode "b") (DynamicPop DynPop2) (UserNode "c"),
     Edge (UserNode "c") (Pop "1") (UserNode "d"),
     Edge (UserNode "a") (Push "1") (IntermediateNode ([Push "1", Push "1"]) (StaticDestination $ UserNode "c")),
     Edge (IntermediateNode ([Push "1", Push "1"]) (StaticDestination $ UserNode "c")) (Push "1") (IntermediateNode ([Push "1"]) (StaticDestination $ UserNode "c")),
     Edge (IntermediateNode ([Push "1"]) (StaticDestination $ UserNode "c")) (Push "1") (UserNode "c"),
     Edge (IntermediateNode ([Push "1"]) (StaticDestination $ UserNode "c")) Nop (UserNode "d"),
     Edge (IntermediateNode ([Push "1", Push "1"]) (StaticDestination $ UserNode "c")) (Push "1") (UserNode "d")
    ]

dynPopTestRes2 :: Graph Test
dynPopTestRes2 = graphFromEdges dynPopTestSet2

dynPopTestSetInit2 :: S.Set (Edge Test)
dynPopTestSetInit2 =
  S.fromList
    [Edge (UserNode "a") (Push "5") (UserNode "b"),
     Edge (UserNode "b") (DynamicPop DynPop2) (UserNode "c"),
     Edge (UserNode "c") (Pop "1") (UserNode "d")]

dynPopTestInit2 :: Graph Test
dynPopTestInit2 = graphFromEdges dynPopTestSetInit2

dynPopTest2 :: TestTree
dynPopTest2 = testCase "Testing push + dynpop (2)"
  (assertEqual "Should have many new edges" dynPopTestRes2 (graphClosure dynPopTestInit2))

-- dynPopTest2ActiveNodes :: TestTree
-- dynPopTest2ActiveNodes = testCase "Testing push + dynpop (2): activeNodes"
--   (assertEqual "Should have many new edges" S.empty (getActiveNodes $ fullAnalysis dynPopTestInit2))

-- Eighth Test: ActiveNodes 1
activeNodesTestSet1 :: S.Set (Edge Test)
activeNodesTestSet1 =
  S.fromList
    [Edge (UserNode "d") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "x") (UserNode "f"),
     Edge (UserNode "a") (Push "y") (UserNode "b"),
     Edge (UserNode "b") (Pop "y") (UserNode "c"),
     Edge (UserNode "e") (Push "z") (UserNode "b"),
     Edge (UserNode "b") (Pop "z") (UserNode "g"),
     Edge (UserNode "a") Nop (UserNode "c")
    ]

activeNodesTestRes1 :: Graph Test
activeNodesTestRes1 = graphFromEdges activeNodesTestSet1

activeNodesTestSetInit1 :: S.Set (Edge Test)
activeNodesTestSetInit1 =
  S.fromList
    [Edge (UserNode "d") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "x") (UserNode "f"),
     Edge (UserNode "a") (Push "y") (UserNode "b"),
     Edge (UserNode "b") (Pop "y") (UserNode "c"),
     Edge (UserNode "e") (Push "z") (UserNode "b"),
     Edge (UserNode "b") (Pop "z") (UserNode "g")
    ]

activeNodesTestInit1 :: Graph Test
activeNodesTestInit1 = graphFromEdges activeNodesTestSetInit1

activeNodesTest1 :: TestTree
activeNodesTest1 = testCase "Testing activeNodes algorithm"
  (assertEqual "Should have one new edge" activeNodesTestRes1
  (graphClosureWithActives (ActiveNodes $ S.fromList [UserNode "a"])
  activeNodesTestInit1))

addEdgeFunBeforeActive :: S.Set (Edge Test)
addEdgeFunBeforeActive =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "x") (UserNode "c"),
     Edge (UserNode "a") Nop (UserNode "c")
    ]

addEdgeFunBeforeActiveTestRes :: Graph Test
addEdgeFunBeforeActiveTestRes = graphFromEdges addEdgeFunBeforeActive

addEdgeFunBeforeActiveTestSetInit :: S.Set (Edge Test)
addEdgeFunBeforeActiveTestSetInit =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b")
    ]

addEdgeFunBeforeActiveTestInit :: Graph Test
addEdgeFunBeforeActiveTestInit = graphFromEdges addEdgeFunBeforeActiveTestSetInit

addEdgeFunBeforeActiveTest :: TestTree
addEdgeFunBeforeActiveTest = testCase "Testing edgeFunction algorithm"
  (assertEqual "Should have one new edge" addEdgeFunBeforeActiveTestRes
  (graphClosureWithEdgeFun1 [edgeFun1] addEdgeFunBeforeActiveTestInit))

addEdgeFunAfterActive :: S.Set (Edge Test)
addEdgeFunAfterActive =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "x") (UserNode "c"),
     Edge (UserNode "a") Nop (UserNode "c")
    ]

addEdgeFunAfterActiveTestRes :: Graph Test
addEdgeFunAfterActiveTestRes = graphFromEdges addEdgeFunAfterActive

addEdgeFunAfterActiveTestSetInit :: S.Set (Edge Test)
addEdgeFunAfterActiveTestSetInit =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b")
    ]

addEdgeFunAfterActiveTestInit :: Graph Test
addEdgeFunAfterActiveTestInit = graphFromEdges addEdgeFunAfterActiveTestSetInit

addEdgeFunAfterActiveTest :: TestTree
addEdgeFunAfterActiveTest = testCase "Testing edgeFunction algorithm"
  (assertEqual "Should have one new edge" addEdgeFunAfterActiveTestRes
  (graphClosureWithEdgeFun2 [edgeFun1] addEdgeFunAfterActiveTestInit))

extraWork :: S.Set (Edge Test)
extraWork =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "x") (UserNode "c")
    ]

extraWorkTestRes :: Graph Test
extraWorkTestRes = graphFromEdges extraWork

extraWorkTestSetInit :: S.Set (Edge Test)
extraWorkTestSetInit =
  S.fromList
    [Edge (UserNode "a") (Push "x") (UserNode "b"),
     Edge (UserNode "b") (Pop "x") (UserNode "c")
    ]

extraWorkTestInit :: Graph Test
extraWorkTestInit = graphFromEdges extraWorkTestSetInit

extraWorkTest :: TestTree
extraWorkTest = testCase "Testing algorithm for doing unnecessary work"
  (assertEqual "Should have no new edge" extraWorkTestRes
  (graphClosureWithFullSpec (ActiveNodes S.empty) [edgeFun1] extraWorkTestInit))
