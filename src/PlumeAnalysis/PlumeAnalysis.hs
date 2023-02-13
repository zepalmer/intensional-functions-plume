{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}

-- TODO: Translate the smarter closure algorithm

module PlumeAnalysis.PlumeAnalysis where

import AST.AbstractAst
import AST.Ast
import AST.AstUtils
import qualified Closure.Intensional.Indexed.Engine as ICE
import qualified PlumeAnalysis.Context as C
import qualified PdsReachability
import PlumeAnalysis.Pds.PlumePdsComputations
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph
import PlumeAnalysis.Utils.PlumeUtils

import Control.DeepSeq
import Control.Intensional.Applicative
import Control.Intensional.Monad.Identity
import Control.Intensional.Runtime
-- import Control.Monad
import Data.Function
-- import qualified Data.Either as E
import qualified Data.List as List
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import Data.Set (Set)
import qualified Data.Set as Set

-- Internal Data Types ---------------------------------------------------------

data Lookup context
  = Lookup AbstractVar AbstractCls context (Set Pattern) (Set Pattern)
  deriving (Eq, Ord, Show)

data PlumeFact context
  = CFGEdgeFact (CFGEdge context)
  | CFGNodeFact (CFGNode context)
  | CFGNodeActiveFact (CFGNode context)
  | LookupResultFact (Lookup context) AbstractValue
  | PlumeNeedsLookup (Lookup context)
  deriving (Eq, Ord, Show)

data PlumeAnalysis context =
  PlumeAnalysis
    { pdsEngine :: PdsReachability.Analysis (PlumePds context)
    , plumeEngine :: ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
    , plumeExpression :: ConcreteExpr
    }

instance NFData (PlumeAnalysis context) where
    rnf plumeAnalysis =
      seq (pdsEngine plumeAnalysis) $
      seq (plumeEngine plumeAnalysis) $
      seq (plumeExpression plumeAnalysis) $
      ()

-- Indexing Functions ----------------------------------------------------------

indexPredecessors ::
    ICE.IndexingFunction (PlumeFact context) (CFGNode context) (CFGNode context)
indexPredecessors = \%Ord fact ->
  case fact of
    CFGEdgeFact (CFGEdge source target) -> Just (target, source)
    _ -> Nothing

indexSuccessors ::
    ICE.IndexingFunction (PlumeFact context) (CFGNode context) (CFGNode context)
indexSuccessors = \%Ord fact ->
  case fact of
    CFGEdgeFact (CFGEdge source target) -> Just (source, target)
    _ -> Nothing

indexAllEdges ::
    ICE.IndexingFunction (PlumeFact context) () (CFGEdge context)
indexAllEdges = \%Ord fact ->
  case fact of
    CFGEdgeFact edge -> Just ((), edge)
    _ -> Nothing

indexAllActiveNodes ::
    ICE.IndexingFunction (PlumeFact context) () (CFGNode context)
indexAllActiveNodes = \%Ord fact ->
  case fact of
    CFGNodeActiveFact node -> Just ((), node)
    _ -> Nothing

indexIsActiveNode ::
    ICE.IndexingFunction (PlumeFact context) (CFGNode context) ()
indexIsActiveNode = \%Ord fact ->
  case fact of
    CFGNodeActiveFact node -> Just (node, ())
    _ -> Nothing

indexLookupResultsByLookup ::
    ICE.IndexingFunction (PlumeFact context) (Lookup context) AbstractValue
indexLookupResultsByLookup = \%Ord fact ->
  case fact of
    LookupResultFact lookup result -> Just (lookup, result)
    _ -> Nothing

indexLookupResultExists ::
    ICE.IndexingFunction (PlumeFact context) (Lookup context) ()
indexLookupResultExists = \%Ord fact ->
  case fact of
    LookupResultFact lookup _ -> Just (lookup, ())
    _ -> Nothing

indexAllCallSites ::
    ICE.IndexingFunction (PlumeFact context) ()
        ( AbstractCls, AbstractVar, AbstractVar, AbstractVar
        , ContextualityCallSiteAnnot, context, CFGNode context)
indexAllCallSites = \%Ord fact ->
  case fact of
    CFGNodeFact node@(CFGNode
      (UnannotatedClause cls@(Clause x1 (ApplBody x2 x3 callSiteAnnot)))
      context) ->
        Just ( ()
             , (cls, x1, x2, x3, csaContextuality callSiteAnnot, context, node))
    _ -> Nothing

indexAllConditionalSites ::
    ICE.IndexingFunction (PlumeFact context) ()
        ( AbstractCls, AbstractVar, AbstractVar, Pattern, AbstractFun
        , AbstractFun , context, CFGNode context)
indexAllConditionalSites = \%Ord fact ->
  case fact of
    CFGNodeFact node@(CFGNode
      (UnannotatedClause cls@(Clause x1 (ConditionalBody x2 p f1 f2)))
      context ) ->
        Just ((), (cls, x1, x2, p, f1, f2, context, node))
    _ -> Nothing

-- Helpers for manipulating analysis structures --------------------------------

updatePlumeEngine :: forall context.
                     (C.Context context)
                  => (ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
                   -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context))
                  -> PlumeAnalysis context
                  -> PlumeAnalysis context
updatePlumeEngine fn analysis =
  analysis { plumeEngine = fn $ plumeEngine analysis }

addIndex :: forall context key derivative.
            ( C.Context context
            , Typeable context
            , Typeable key
            , Typeable derivative
            , Ord key
            , Ord derivative
            )
         => ICE.IndexingFunction (PlumeFact context) key derivative
         -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
         -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
addIndex = ICE.addIndex

addComputation :: forall context.
                  (C.Context context, Typeable context)
               => ICE.Computation (IntensionalIdentity Ord) (PlumeFact context)
               -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
               -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
addComputation computation engine =
  let IntensionalIdentity engine' = ICE.addComputation computation engine in
  engine'

addComputations :: forall context.
                  (C.Context context, Typeable context)
               => [ICE.Computation (IntensionalIdentity Ord) (PlumeFact context)]
               -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
               -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
addComputations computations engine =
  List.foldl (\eng comp -> addComputation comp eng) engine computations

addFact :: forall context.
           (C.Context context, Typeable context)
        => PlumeFact context
        -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
        -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
addFact = ICE.addFact

addFacts :: forall context.
            (C.Context context, Typeable context)
         => [PlumeFact context]
         -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
         -> ICE.Engine (IntensionalIdentity Ord) (PlumeFact context)
addFacts = ICE.addFacts

-- Analysis Operations ---------------------------------------------------------

wireM :: (Typeable context, Ord context)
      => context
      -> CFGNode context
      -> AbstractFun
      -> AbstractVar
      -> AbstractVar
      -> ICE.Computation (IntensionalIdentity Ord) (PlumeFact context)
wireM context siteNode func argVar bindVar =
    intensional Ord do
    let (bodyEdges, wireInNode, wireOutNode) =
            wireInner context siteNode func argVar bindVar
    ICE.addIntermediateFacts $ Set.toList $
        Set.map CFGEdgeFact bodyEdges
    ICE.addIntermediateComputation $
        (\%Ord () -> intensional Ord do
        pred <- ICE.getIndexedFact indexPredecessors siteNode
        itsPure %@ Set.singleton
            (CFGEdgeFact $ CFGEdge pred wireInNode)
        )
    ICE.addIntermediateComputation $
        (\%Ord () -> intensional Ord do
        succ <- ICE.getIndexedFact indexSuccessors siteNode
        itsPure %@ Set.singleton
            (CFGEdgeFact $ CFGEdge wireOutNode succ)
        )
    itsPure %@ Set.empty

{-| The closure engine computations defining Plume abstract evaluation rules.
-}
abstractEvaluationRules :: forall context.
                           (C.Context context, Typeable context, Ord context)
                        => [ICE.Computation
                                (IntensionalIdentity Ord)
                                (PlumeFact context)]
abstractEvaluationRules =
    [ -- Application (contextual or acontextual)
      (intensional Ord do
        (cls,x1,x2,x3,annot,context,cfgNode) <-
            ICE.getIndexedFact indexAllCallSites ()
        () <- ICE.getIndexedFact indexIsActiveNode cfgNode
        let x2lookup = Lookup x2 cls context Set.empty Set.empty
        ICE.addIntermediateFact $ PlumeNeedsLookup x2lookup
        x2val <- ICE.getIndexedFact indexLookupResultsByLookup x2lookup
        case x2val of
          AbsValueFunction x2funval@(FunctionValue (Var x4id) body) ->
            intensional Ord do
              let x3lookup = Lookup x3 cls context Set.empty Set.empty
              ICE.addIntermediateFact $ PlumeNeedsLookup x3lookup
              () <- ICE.getIndexedFact indexLookupResultExists x3lookup
              let isContextual =
                    case annot of
                      CallSiteAcontextual -> False
                      CallSiteContextual -> True
                      CallSiteAcontextualFor xids -> x4id `Set.member` xids
              let context' =
                    if isContextual then
                      C.add cls context
                    else
                      context
              wireM context' cfgNode x2funval x3 x1
          _ -> itsPure %@ Set.empty
      )
    , -- Conditional True
      (intensional Ord do
        (cls,x1,x2,p,thenFn,elseFn,context,cfgNode) <-
            ICE.getIndexedFact indexAllConditionalSites ()
        () <- ICE.getIndexedFact indexIsActiveNode cfgNode
        let (posPatSet,negPatSet,branchFn) =
              (Set.singleton p, Set.empty, thenFn)
        let lookup = Lookup x2 cls context posPatSet negPatSet
        () <- ICE.addIntermediateFact $ PlumeNeedsLookup lookup
        () <- ICE.getIndexedFact indexLookupResultExists lookup
        wireM context cfgNode branchFn x2 x1
      )
    , -- Conditional False
      (intensional Ord do
        (cls,x1,x2,p,thenFn,elseFn,context,cfgNode) <-
            ICE.getIndexedFact indexAllConditionalSites ()
        () <- ICE.getIndexedFact indexIsActiveNode cfgNode
        let (posPatSet,negPatSet,branchFn) =
              (Set.empty, Set.singleton p, elseFn)
        let lookup = Lookup x2 cls context posPatSet negPatSet
        () <- ICE.addIntermediateFact $ PlumeNeedsLookup lookup
        () <- ICE.getIndexedFact indexLookupResultExists lookup
        wireM context cfgNode branchFn x2 x1
      )
    ]

{-| Creates an initial, empty analysis of the provided concrete expression.  An
    empty context model of the expected type to use must be provided as the
    first argument.
-}
createInitialAnalysis :: forall context.
                         (C.Context context, Typeable context)
                      => context -> ConcreteExpr -> PlumeAnalysis context
createInitialAnalysis emptyCtx expr =
  let Expr cls = transform expr in
  let rx = rv cls in
  let nodes =
        cls
        & List.map (\x -> CFGNode (UnannotatedClause x) emptyCtx) -- FIXME: What to do with empty contexts?
        & (\tl -> (CFGNode (StartClause rx) emptyCtx) : tl)
        & flip (++) [CFGNode (EndClause rx) emptyCtx]
  in
  let edges = edgesFromNodeList nodes in
  updatePlumeEngine
    ( addFacts (List.map CFGEdgeFact $ Set.toList edges)
    . addIndex indexPredecessors
    . addIndex indexSuccessors
    . addIndex indexAllEdges
    . addIndex indexAllActiveNodes
    . addIndex indexIsActiveNode
    . addIndex indexLookupResultsByLookup
    . addIndex indexAllCallSites
    . addIndex indexAllConditionalSites
    -- If an edge exists between two nodes, then those nodes exist.
    . addComputation
      (intensional Ord do
        CFGEdge src dst <- ICE.getIndexedFact indexAllEdges ()
        itsPure %$ Set.fromList [CFGNodeFact src, CFGNodeFact dst]
      )
    -- If an edge exists and its source node is active, then its target node is
    -- active.
    . addComputation
      (intensional Ord do
        node <- ICE.getIndexedFact indexAllActiveNodes ()
        dst <- ICE.getIndexedFact indexSuccessors node
        itsPure %$ Set.singleton (CFGNodeActiveFact dst)
      )
    -- Now add computations for the abstract evaluation rules.
    . addComputations abstractEvaluationRules
    )
    ( PlumeAnalysis { pdsEngine = PdsReachability.emptyAnalysis
                    , plumeEngine = ICE.emptyEngine
                    , plumeExpression = expr
                    }
    )

{-| Prepares the provided analysis to answer a lookup question.  The arguments
    are the variable to look up, the clause from which the lookup should start,
    the context in which the lookup should occur, and the positive and negative
    filters to apply to the lookup.  Note that the analysis must be closed over
    before any work to answer this question will be performed.
-}
prepareQuestion ::
  (C.Context context, Typeable context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  Set Pattern ->
  Set Pattern ->
  PlumeAnalysis context ->
  PlumeAnalysis context
prepareQuestion x acl ctx patsp patsn analysis =
  let startNode = CFGNode acl ctx in
  let startState = ProgramPointState startNode in
  let startActions = [ PdsReachability.Push BottomOfStack
                     , PdsReachability.Push (LookupVar x patsp patsn)
                     ] in
  let question = PdsReachability.Question startState startActions in
  let reachability = pdsEngine analysis in
  let reachability' = PdsReachability.addQuestion question reachability in
  analysis { pdsEngine = reachability' }

{-| Retrieves the current results of a particular lookup question.  See
    prepareQuestion for a description of the arguments.  The question must be
    prepared and the analysis closed before work toward the question will occur.
    This function returns the abstract filtered values which answer this
    question thus far.  Note that an analysis which is not fully closed will not
    contain the full set of answers.
-}
askQuestion ::
  (C.Context context, Typeable context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  Set Pattern ->
  Set Pattern ->
  PlumeAnalysis context ->
  [AbsFilteredVal]
askQuestion x acl ctx patsp patsn analysis =
  let startNode = CFGNode acl ctx in
  let startState = ProgramPointState startNode in
  let startActions = [ PdsReachability.Push BottomOfStack
                     , PdsReachability.Push (LookupVar x patsp patsn)
                     ] in
  let question = PdsReachability.Question startState startActions in
  let reachability = pdsEngine analysis in
  let reachableStates =
        PdsReachability.getReachableNodes question reachability
  in
  let values =
        case reachableStates of
          Nothing -> []
          Just vals -> Maybe.mapMaybe
                        (\val -> case val of ProgramPointState _ -> Nothing
                                             ResultState v -> Just v) vals
  in
  values

{-| Ensures that the PDS of the provided Plume analysis is fully closed. -}
pdsClosure :: forall context.
              (C.Context context, Typeable context)
           => PlumeAnalysis context -> PlumeAnalysis context
pdsClosure analysis =
  let loop currentAnalysis newAnswers =
        let pds = pdsEngine currentAnalysis in
        if PdsReachability.isClosed pds then
          (currentAnalysis, newAnswers)
        else
          let (pds', newAnswers') = PdsReachability.closureStep pds in
          let currentAnalysis' = currentAnalysis { pdsEngine = pds' } in
          loop currentAnalysis' (Set.union newAnswers newAnswers')
  in
  let (analysis', newAnswers) = loop analysis Set.empty in
  let newAnswerFacts =
        newAnswers
        & Set.toList
        & Maybe.mapMaybe
            (\(PdsReachability.Question startNode actions, answerNode) ->
              case (startNode, actions, answerNode) of
                    ( ProgramPointState
                        (CFGNode (UnannotatedClause acl) context),
                      [ PdsReachability.Push BottomOfStack
                      , PdsReachability.Push (LookupVar x patsp patsn)
                      ],
                      ResultState (AbsFilteredVal value _ _)) ->
                        let lookup = Lookup x acl context patsp patsn in
                        Just $ LookupResultFact lookup value
                    _ ->
                        Nothing
            )
  in
  updatePlumeEngine (addFacts newAnswerFacts) analysis'

{-| Performs a single CFG closure step in a given Plume analysis. -}
cfgClosureStep :: forall context.
                  (C.Context context, Typeable context)
               => PlumeAnalysis context -> PlumeAnalysis context
cfgClosureStep analysis =
  let plume = plumeEngine analysis in
  let IntensionalIdentity (plume', newFacts) = ICE.stepWithFacts plume in
  -- For each new CFG edge discovered, we need to update the PDS so that
  -- later lookup operations behave correctly.  We translate each CFG edge
  -- into a computation to be entered into the PDS.  Other Plume facts (such as
  -- lookup results or CFG nodes) do not have direct bearing on the PDS.
  let newPdsComputations :: [( PdsState context
                             , PdsReachability.PDRM (PlumePds context)
                                ( PdsReachability.Path (PlumePds context)
                                , PdsState context
                                )
                             )
                            ]
      newPdsComputations =
        List.concatMap
          (\fact ->
            case fact of
              CFGEdgeFact edge ->
                computationForEdge edge
              _ -> []
          )
          (Set.toList newFacts)
  in
  let newPdsLookups :: [Lookup context]
      newPdsLookups =
        Maybe.mapMaybe
          (\fact ->
            case fact of
              PlumeNeedsLookup lookup -> Just lookup
              _ -> Nothing
          )
          (Set.toList newFacts)
  in
  let pds' =
        List.foldl
          (\pds (startNode,pathComputation) ->
            PdsReachability.addPathComputation startNode pathComputation pds
          )
          (pdsEngine analysis) newPdsComputations
  in
  let analysis' =
        analysis
          { plumeEngine = plume'
          , pdsEngine = pds'
          }
  in
  let analysis'' =
        List.foldl
          (\pds (Lookup x acl ctx patsp patsn) ->
            prepareQuestion x (UnannotatedClause acl) ctx patsp patsn pds
          )
          analysis' newPdsLookups
  in
  analysis''

{-| Performs a single Plume closure step.  This performs a single step of CFG
    closure and then fully closes over the underlying PDS.
-}
performClosureStep ::
  (C.Context context, Typeable context) =>
  PlumeAnalysis context ->
  PlumeAnalysis context
performClosureStep analysis =
  analysis
  & cfgClosureStep
  & pdsClosure

{-| Determines whether a given Plume analysis is fully closed. -}
isClosed :: (C.Context context) => PlumeAnalysis context -> Bool
isClosed analysis =
  ICE.isClosed (plumeEngine analysis) &&
  PdsReachability.isClosed (pdsEngine analysis)

{-| Performs a full closure of the provided Plume analysis. -}
performFullClosure ::
    (C.Context context, Typeable context)
 => PlumeAnalysis context -> PlumeAnalysis context
performFullClosure analysis =
  if isClosed analysis then analysis
  else performFullClosure $ performClosureStep analysis

{-| Queries a Plume analysis for the values of a variable at a given point,
    within a particular context, and using the given sets of positive and
    negative filters.  This process performs a full closure of the provided
    analysis and so returns the values together with the fully-closed analysis.
-}
restrictedValuesOfVariableWithClosure ::
  (C.Context context, Typeable context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  Set Pattern ->
  Set Pattern ->
  PlumeAnalysis context ->
  ([AbsFilteredVal], PlumeAnalysis context)
restrictedValuesOfVariableWithClosure x acl ctx patsp patsn analysis =
  let analysis' = prepareQuestion x acl ctx patsp patsn analysis in
  let analysis'' = performFullClosure analysis' in
  let answer = askQuestion x acl ctx patsp patsn analysis'' in
  (answer, analysis'')

{-| Queries a Plume analysis for the values of a variable at a given point
    within the empty context.  This process performs a full closure of the
    provided analysis and so returns the values together with the fully-closed
    analysis.
-}
valuesOfVariable ::
  (C.Context context, Typeable context) =>
  AbstractVar ->
  AnnotatedClause ->
  PlumeAnalysis context ->
  (Set AbsFilteredVal, PlumeAnalysis context)
valuesOfVariable x acl analysis =
  let (valLst, analysis') =
        restrictedValuesOfVariableWithClosure
          x acl C.empty Set.empty Set.empty analysis
  in
  (Set.fromList valLst, analysis')

{-| Queries a Plume analysis for the values of a variable at a given point
    within a given context.  This process performs a full closure of the
    provided analysis and so returns the values together with the fully-closed
    analysis.
-}
contextualValuesOfVariable ::
  (C.Context context, Typeable context) =>
  AbstractVar ->
  AnnotatedClause ->
  context ->
  PlumeAnalysis context ->
  (Set AbsFilteredVal, PlumeAnalysis context)
contextualValuesOfVariable x acl ctx analysis =
  let (valLst, analysis') =
        restrictedValuesOfVariableWithClosure
          x acl ctx Set.empty Set.empty analysis
  in
  (Set.fromList valLst, analysis')
