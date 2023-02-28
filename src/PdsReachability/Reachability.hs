{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

module PdsReachability.Reachability where

import AST.Ast
import Control.Intensional.Alternative
import Control.Intensional.Applicative
import Control.Intensional.Functor
import Control.Intensional.Monad
import Control.Intensional.MonadPlus
import Control.Intensional.Monad.Identity
import Control.Intensional.Monad.Trans
import Control.Intensional.Monad.Trans.Coroutine
import Control.Intensional.Monad.Trans.List
import Control.Intensional.Monad.Trans.Maybe
import Control.Intensional.Monad.Trans.State
import Control.Intensional.Runtime
import Data.Function
import qualified Data.List as List
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set
import PdsReachability.Specification
import PdsReachability.UserDataTypes

import qualified Closure.Intensional.Indexed.Engine as ICE

-- Internal Data Types ---------------------------------------------------------

data InternalNode spec
  = UserNode (Node spec)
  | IntermediateNode [StackAction spec] (InternalNode spec)
deriving instance (SpecIs Eq spec) => (Eq (InternalNode spec))
deriving instance (SpecIs Ord spec) => (Ord (InternalNode spec))
deriving instance (SpecIs Show spec) => (Show (InternalNode spec))

data Fact spec
  = EdgeFact (InternalNode spec) (StackAction spec) (InternalNode spec)
  | NodeFact (InternalNode spec)
  | ActiveFact (InternalNode spec)
deriving instance (SpecIs Eq spec) => Eq (Fact spec)
deriving instance (SpecIs Ord spec) => Ord (Fact spec)
deriving instance (SpecIs Show spec) => Show (Fact spec)

newtype Questions spec = Questions (Set (Question spec))
deriving instance (SpecIs Eq spec) => (Eq (Questions spec))
deriving instance (SpecIs Ord spec) => (Ord (Questions spec))
deriving instance (SpecIs Show spec) => (Show (Questions spec))

data Analysis spec =
  Analysis
    { analysisEngine :: ICE.Engine (IntensionalIdentity Ord) (Fact spec)
    , analysisQuestions :: Questions spec
    }

-- Indexing Functions ----------------------------------------------------------

indexAllEdges ::
    ICE.IndexingFunction (Fact spec)
      () (InternalNode spec, StackAction spec, InternalNode spec)
indexAllEdges = \%Ord fact ->
  case fact of
    EdgeFact src action dst -> Just ((), (src, action, dst))
    _ -> Nothing

indexNopEdges ::
    ICE.IndexingFunction (Fact spec) () (InternalNode spec, InternalNode spec)
indexNopEdges = \%Ord fact ->
  case fact of
    EdgeFact src Nop dst -> Just ((), (src, dst))
    _ -> Nothing

indexNopEdgesByDest ::
    ICE.IndexingFunction (Fact spec)
      (InternalNode spec) (InternalNode spec)
indexNopEdgesByDest = \%Ord fact ->
  case fact of
    EdgeFact src Nop dst -> Just (dst, src)
    _ -> Nothing

indexNopEdgesBySource ::
    ICE.IndexingFunction (Fact spec)
      (InternalNode spec) (InternalNode spec)
indexNopEdgesBySource = \%Ord fact ->
  case fact of
    EdgeFact src Nop dst -> Just (src, dst)
    _ -> Nothing

indexPopEdgesBySourceAndElement ::
    ICE.IndexingFunction (Fact spec)
      (InternalNode spec, Element spec) (InternalNode spec)
indexPopEdgesBySourceAndElement = \%Ord fact ->
  case fact of
    EdgeFact src (Pop elem) dst -> Just ((src,elem),dst)
    _ -> Nothing

indexPushEdges ::
    ICE.IndexingFunction (Fact spec)
      () (InternalNode spec, Element spec, InternalNode spec)
indexPushEdges = \%Ord fact ->
  case fact of
    EdgeFact src (Push element) dst -> Just ((), (src, element, dst))
    _ -> Nothing

indexPushEdgesByDest ::
    ICE.IndexingFunction (Fact spec)
      (InternalNode spec) (InternalNode spec, Element spec)
indexPushEdgesByDest = \%Ord fact ->
  case fact of
    EdgeFact src (Push elem) dst -> Just (dst, (src, elem))
    _ -> Nothing

indexPushEdgesByDestAndElement ::
    ICE.IndexingFunction (Fact spec)
      (InternalNode spec, Element spec) (InternalNode spec)
indexPushEdgesByDestAndElement = \%Ord fact ->
  case fact of
    EdgeFact src (Push elem) dst -> Just ((dst, elem), src)
    _ -> Nothing

indexPushEdgesBySource ::
    ICE.IndexingFunction (Fact spec)
      (InternalNode spec) (InternalNode spec, Element spec)
indexPushEdgesBySource = \%Ord fact ->
  case fact of
    EdgeFact src (Push elem) dst -> Just (src, (dst, elem))
    _ -> Nothing

indexActiveNode :: ICE.IndexingFunction (Fact spec) () (InternalNode spec)
indexActiveNode = \%Ord fact ->
  case fact of
    ActiveFact node -> Just ((), node)
    _ -> Nothing

indexIsActiveNode :: ICE.IndexingFunction (Fact spec) (InternalNode spec) ()
indexIsActiveNode = \%Ord fact ->
  case fact of
    ActiveFact node -> Just (node, ())
    _ -> Nothing

-- Helpers for manipulating analysis structures --------------------------------

updateEngine :: forall spec.
                (Spec spec)
             => (ICE.Engine (IntensionalIdentity Ord) (Fact spec) ->
                 ICE.Engine (IntensionalIdentity Ord) (Fact spec))
             -> Analysis spec
             -> Analysis spec
updateEngine fn analysis =
  analysis { analysisEngine = fn $ analysisEngine analysis }

addIndex :: forall spec key derivative.
            ( Spec spec
            , Typeable key
            , Typeable derivative
            , Ord key
            , Ord derivative
            )
         => ICE.IndexingFunction (Fact spec) key derivative
         -> ICE.Engine (IntensionalIdentity Ord) (Fact spec)
         -> ICE.Engine (IntensionalIdentity Ord) (Fact spec)
addIndex = ICE.addIndex

addComputation :: forall spec.
                  (Spec spec)
               => ICE.Computation (IntensionalIdentity Ord) (Fact spec)
               -> ICE.Engine (IntensionalIdentity Ord) (Fact spec)
               -> ICE.Engine (IntensionalIdentity Ord) (Fact spec)
addComputation computation engine =
  let IntensionalIdentity engine' = ICE.addComputation computation engine in
  engine'

addFact :: forall spec.
           (Spec spec)
        => Fact spec
        -> ICE.Engine (IntensionalIdentity Ord) (Fact spec)
        -> ICE.Engine (IntensionalIdentity Ord) (Fact spec)
addFact = ICE.addFact

addFacts :: forall spec.
            (Spec spec)
         => [Fact spec]
         -> ICE.Engine (IntensionalIdentity Ord) (Fact spec)
         -> ICE.Engine (IntensionalIdentity Ord) (Fact spec)
addFacts = ICE.addFacts

-- Analysis Operations ---------------------------------------------------------

-- USER
emptyAnalysis :: (Spec spec) => Analysis spec
emptyAnalysis =
  updateEngine
    ( addIndex indexAllEdges
    . addIndex indexNopEdges
    . addIndex indexNopEdgesByDest
    . addIndex indexNopEdgesBySource
    . addIndex indexPopEdgesBySourceAndElement
    . addIndex indexPushEdges
    . addIndex indexPushEdgesByDest
    . addIndex indexPushEdgesByDestAndElement
    . addIndex indexPushEdgesBySource
    . addIndex indexActiveNode
    . addIndex indexIsActiveNode
    -- If an edge exists between two nodes, then those nodes exist.
    . addComputation
        (intensional Ord do
          (src, _, dst) <- ICE.getIndexedFact indexAllEdges ()
          itsPure %$ Set.fromList [NodeFact src, NodeFact dst]
        )
    -- If a node is active and a nop or push leads to another node, then that
    -- other node is active.
    . addComputation
        (intensional Ord do
          node <- ICE.getIndexedFact indexActiveNode ()
          dest <- ICE.getIndexedFact indexNopEdgesBySource node
          itsPure %@ Set.fromList [ActiveFact dest]
        )
    . addComputation
        (intensional Ord do
          node <- ICE.getIndexedFact indexActiveNode ()
          (dest, _) <- ICE.getIndexedFact indexPushEdgesBySource node
          itsPure %@ Set.fromList [ActiveFact dest]
        )
    -- Push + nop = push
    . addComputation
        (intensional Ord do
          (nodeA, element, nodeB) <- ICE.getIndexedFact indexPushEdges ()
          ICE.getIndexedFact indexIsActiveNode nodeA
          nodeC <- ICE.getIndexedFact indexNopEdgesBySource nodeB
          itsPure %@ Set.fromList [EdgeFact nodeA (Push element) nodeC]
        )
    -- Nop + push = push
    . addComputation
        (intensional Ord do
          (nodeA, nodeB) <- ICE.getIndexedFact indexNopEdges ()
          ICE.getIndexedFact indexIsActiveNode nodeA
          (nodeC, element) <- ICE.getIndexedFact indexPushEdgesBySource nodeB
          itsPure %@ Set.fromList [EdgeFact nodeA (Push element) nodeC]
        )
    -- Nop + nop = nop
    . addComputation
        (intensional Ord do
          (nodeA, nodeB) <- ICE.getIndexedFact indexNopEdges ()
          ICE.getIndexedFact indexIsActiveNode nodeA
          nodeC <- ICE.getIndexedFact indexNopEdgesBySource nodeB
          itsPure %@ Set.fromList [EdgeFact nodeA Nop nodeC]
        )
    -- Push + pop = nop
    . addComputation
        (intensional Ord do
          (nodeA, element, nodeB) <- ICE.getIndexedFact indexPushEdges ()
          ICE.getIndexedFact indexIsActiveNode nodeA
          nodeC <- ICE.getIndexedFact indexPopEdgesBySourceAndElement
                      (nodeB, element)
          itsPure %@ Set.fromList [EdgeFact nodeA Nop nodeC]
        )
    )
    (Analysis { analysisEngine = ICE.emptyEngine
              , analysisQuestions = Questions $ Set.empty
              }
    )

-- USER
addEdge :: (Spec spec) => Edge spec -> Analysis spec -> Analysis spec
addEdge (Edge src action dst) analysis =
  analysis &
    updateEngine (addFact (EdgeFact (UserNode src) action (UserNode dst)))

-- USER
addPath :: (Spec spec)
        => Node spec -> Path spec -> Node spec -> Analysis spec -> Analysis spec
addPath source path destination analysis =
  let facts = pathToFacts (UserNode source) path (UserNode destination) in
  analysis & updateEngine (addFacts $ Set.toList facts)

-- INTERNAL
pathToFacts :: (Spec spec)
            => InternalNode spec -> Path spec -> InternalNode spec
            -> Set (Fact spec)
pathToFacts source (Path actions) destination =
  case actions of
    [] -> Set.singleton $ EdgeFact source Nop destination
    [action] -> Set.singleton $ EdgeFact source action destination
    action:actions' ->
      let intermediateNode = IntermediateNode actions' destination in
      Set.insert (EdgeFact source action intermediateNode) $
        pathToFacts intermediateNode (Path actions') destination

-- TODO: organize these declarations in some order that makes more sense
type PDRMInner spec =
  (StateT Ord (InternalNode spec)
    (ListT Ord
      (ICE.ComputationT (IntensionalIdentity Ord) (Fact spec))
    )
  )
newtype PDRM spec a = PDRM (PDRMInner spec a)

deriving instance Eq (PDRM spec a)
deriving instance Ord (PDRM spec a)

instance (Typeable spec) => IntensionalFunctor (PDRM spec) where
  type IntensionalFunctorCF (PDRM spec) = Ord
  type IntensionalFunctorMapC (PDRM spec) a b =
    IntensionalFunctorMapC (PDRMInner spec) a b
  itsFmap = \%%Ord ab (PDRM a) -> PDRM $ itsFmap %@% (ab,a)

instance (Typeable spec) => IntensionalApplicative (PDRM spec) where
  type IntensionalApplicativePureC (PDRM spec) a =
    (IntensionalApplicativePureC (PDRMInner spec) a)
  type IntensionalApplicativeApC (PDRM spec) a b =
    (IntensionalApplicativeApC (PDRMInner spec) a b)
  itsPure = \%%Ord a -> PDRM $ itsPure %@ a
  (%<*>) = \%%Ord (PDRM fab) (PDRM fa) -> PDRM $ (%<*>) %@% (fab,fa)

instance (Typeable spec) => IntensionalMonad (PDRM spec) where
  type IntensionalMonadBindC (PDRM spec) a b =
    (IntensionalMonadBindC (PDRMInner spec) a b)
  itsBind = \%%Ord (PDRM ma) (amb :: a ->%Ord PDRM spec b) ->
    PDRM $ intensional Ord do
      a <- ma
      let PDRM mb = amb %@ a
      mb

instance (Typeable spec) => IntensionalAlternative (PDRM spec) where
  type IntensionalAlternativeEmptyC (PDRM spec) a =
    (IntensionalAlternativeEmptyC (PDRMInner spec) a)
  type IntensionalAlternativeChoiceC (PDRM spec) a =
    (IntensionalAlternativeChoiceC (PDRMInner spec) a)
  itsEmpty = PDRM $ itsEmpty
  (%<|>) = \%%Ord (PDRM a) (PDRM b) -> PDRM $ (%<|>) %@% (a, b)

instance (Typeable spec) => IntensionalMonadPlus (PDRM spec) where
  type IntensionalMonadPlusZeroC (PDRM spec) a =
        (IntensionalMonadPlusZeroC (PDRMInner spec) a)
  type IntensionalMonadPlusPlusC (PDRM spec) a =
        (IntensionalMonadPlusPlusC (PDRMInner spec) a)
  itsMzero = PDRM $ itsMzero
  itsMplus = \%%Ord (PDRM a) (PDRM b) -> PDRM $ itsMplus %@% (a, b)

pop :: forall spec.
       ( Spec spec
       , IntensionalMonad (PDRM spec)
       , IntensionalApplicativePureC (PDRM spec) (Element spec)
       , IntensionalMonadBindC (PDRM spec) (InternalNode spec) (Element spec)
       , IntensionalMonadBindC
          (PDRM spec) (InternalNode spec, Element spec) (Element spec)
       , IntensionalMonadBindC (PDRM spec) () (Element spec)
       , (IntensionalFunctorCF (PDRM spec)) (PDRM spec (Element spec))
       )
    => PDRM spec (Element spec)
pop = PDRM $ intensional Ord do
  currentNode <- itsGet
  (prevNode, element) <- itsLift %@ (itsLift %@
                            ICE.getIndexedFact indexPushEdgesByDest currentNode)
  itsSet %@ prevNode
  itsPure %@ element

pdrmMaybe :: forall spec a.
             (Spec spec, Ord a, Typeable a)
          => Maybe a -> PDRM spec a
pdrmMaybe ma = case ma of
  Just x -> itsPure %@ x
  Nothing -> itsEmpty

pdrmChoose :: forall spec a.
              (Spec spec, Ord a, Typeable a)
           => [a] -> PDRM spec a
pdrmChoose items =
  PDRM $ itsLift %$ liftList %$ items

-- USER
addPathComputation ::
     forall spec.
     (Spec spec, Ord (Path spec))
  => Node spec -> PDRM spec (Path spec, Node spec) -> Analysis spec
  -> Analysis spec
addPathComputation source pdrComputation analysis =
  let PDRM innerComputations = pdrComputation in
  let computationsWithResultsM =
        runListT $ ((runStateT $ innerComputations) %@ UserNode source)
  in
  let computation =
        intensional Ord do
          () <- ICE.getIndexedFact indexIsActiveNode (UserNode source)
          computationsWithResults <- computationsWithResultsM
          factSets <- imListToList %$ itsFmap %@% (
                  \%Ord ((path, destination), currentNode) ->
                    pathToFacts currentNode path (UserNode destination)
                  , computationsWithResults )
          itsPure %@ List.foldr Set.union Set.empty factSets
  in
  analysis & updateEngine (addComputation computation)

-- USER
addManyPathComputation ::
     forall spec.
     (Spec spec, Ord (Path spec))
  => (Node spec ->%Ord PDRM spec (Path spec, Node spec)) -> Analysis spec
  -> Analysis spec
addManyPathComputation pdrComputationFunction analysis =
  let computation =
        intensional Ord do
          node <- ICE.getIndexedFact indexActiveNode ()
          case node of
            UserNode source -> intensional Ord do
                let PDRM innerComputations = pdrComputationFunction %@ source
                computationsWithResults <-
                    runListT $ ((runStateT $ innerComputations) %@ node)
                factSets <- imListToList %$ itsFmap %@% (
                    \%Ord ((path, destination), currentNode) ->
                        pathToFacts currentNode path (UserNode destination)
                    , computationsWithResults )
                itsPure %@ List.foldr Set.union Set.empty factSets
            IntermediateNode {} -> itsPure %@ Set.empty
  in
  analysis & updateEngine (addComputation computation)

-- USER
addEdgeFunction :: forall spec. (Spec spec)
                => Maybe (Node spec ->%Ord Bool)
                -> (Node spec ->%Ord [(Path spec, Node spec)])
                -> Analysis spec
                -> Analysis spec
addEdgeFunction maybeNodeFilter edgeFunction analysis =
  -- First: add index to engine
  let nodeIndex :: Fact spec ->%Ord Maybe ((), Node spec)
      nodeIndex =
        case maybeNodeFilter of
          Just nodeFilter ->
            \%Ord fact ->
              case fact of
                NodeFact (UserNode node) ->
                  if nodeFilter %@ node then Just ((), node) else Nothing
                _ ->
                  Nothing
          Nothing ->
            \%Ord fact ->
              case fact of
                NodeFact (UserNode node) -> Just ((), node)
                _ -> Nothing
  in
  let analysis' = analysis & updateEngine (addIndex nodeIndex) in
  -- Next: add a computation to the engine to call the edge function whenever
  -- an active and filter-passing node appears.
  let computation =
        intensional Ord do
          node <- ICE.getIndexedFact nodeIndex ()
          () <- ICE.getIndexedFact indexIsActiveNode (UserNode node)
          let results = edgeFunction %@ node
          let facts =
                results
                & List.map
                    (\(path, dest) ->
                        pathToFacts (UserNode node) path (UserNode dest)
                    )
                & List.foldr Set.union Set.empty
          itsPure %@ facts
  in
  analysis' & updateEngine (addComputation computation)

-- USER
addQuestion :: (Spec a) => Question a -> Analysis a -> Analysis a
addQuestion question analysis =
  let Questions questions = analysisQuestions analysis in
  if question `Set.member` questions then analysis else
    let Question node actions = question in
    let internalTarget = UserNode node in
    let questions' = Set.insert question $ questions in
    let internalSource =
          if List.null actions then
            internalTarget
          else
            IntermediateNode actions internalTarget
    in
    let facts = pathToFacts internalSource (Path actions) internalTarget in
    let analysis' =
          analysis
          & updateEngine
              (addFacts $ (ActiveFact internalSource) : Set.toList facts) in
    analysis' { analysisQuestions = Questions questions' }

-- USER
getReachableNodes :: (Spec spec)
                  => Question spec -> Analysis spec -> Maybe [Node spec]
getReachableNodes question analysis =
  let Questions questions = analysisQuestions analysis in
  let Question node actions = question in
  let lookupNode = IntermediateNode actions (UserNode node) in
  -- Look up Nop edges in the analysis graph and filter out the IntermediateNodes
  if question `Set.member` questions then
    let internalTargets =
          ICE.getAllIndexedFacts indexNopEdgesBySource lookupNode $
            analysisEngine analysis
    in
    Just $ internalTargets
         & Set.toList
         & Maybe.mapMaybe
             (\n -> case n of UserNode n' -> Just n'
                              IntermediateNode _ _ -> Nothing)
  else Nothing

-- USER
isClosed :: Analysis spec -> Bool
isClosed analysis = ICE.isClosed $ analysisEngine analysis

-- USER
closureStep :: (Spec spec)
            => Analysis spec -> (Analysis spec, Set (Question spec, Node spec))
closureStep analysis =
  let IntensionalIdentity (engine', newFacts) =
        ICE.stepWithFacts $ analysisEngine analysis
  in
  let newAnswers =
        newFacts
        & Set.toList
        & Maybe.mapMaybe
            (\fact -> case fact of
                EdgeFact
                    (IntermediateNode actions (UserNode src))
                    Nop
                    (UserNode dst) ->
                  let potentialQuestion = Question src actions in
                  let Questions questions = analysisQuestions analysis in
                  if potentialQuestion `Set.member` questions then
                    Just (potentialQuestion, dst)
                  else
                    Nothing
                _ -> Nothing
            )
        & Set.fromList
  in
  (analysis { analysisEngine = engine' }, newAnswers)

-- USER
fullClosure :: (Spec spec) => Analysis spec -> Analysis spec
fullClosure analysis =
  if isClosed analysis then analysis else
    fullClosure $ fst $ closureStep analysis
