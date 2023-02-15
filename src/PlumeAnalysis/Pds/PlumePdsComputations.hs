{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE TupleSections #-}

module PlumeAnalysis.Pds.PlumePdsComputations
( computationForEdge
) where

import AST.AbstractAst
import AST.Ast
import AST.AstUtils
import qualified PlumeAnalysis.Context as C
import qualified PdsReachability
import PdsReachability (pop, Path(..), StackAction(..))
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph
import PlumeAnalysis.Utils.PlumeUtils
import Utils.Exception

import Control.Exception
import Control.Intensional.Applicative
import Control.Intensional.MonadPlus
import Control.Intensional.Runtime
import Control.Monad
import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

type CFGEdgeComputation context =
    (PdsReachability.PDRM (PlumePds context)
     ( PdsReachability.Path (PlumePds context)
     , PdsState context
     )
    )

type CFGEdgeComputationFunction context =
    CFGNode context -> CFGNode context -> Maybe (CFGEdgeComputation context)

type CFGEdgeComputationFunctionConstraints context =
    ( Typeable context, Ord context, Show context )

-- Variable discovery ----------------------------------------------------------

discoveredOrIntermediateValue :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
discoveredOrIntermediateValue n1 n0 =
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      ContinuationValue absFilteredVal ->
        intensional Ord do
          stackElement' <- pop
          case stackElement' of
            BottomOfStack ->
              -- Discovered value: keep it!
              itsPure %@ (Path [], ResultState absFilteredVal)
            _ ->
              -- Intermediate value: discard it and move on.
              itsPure %@ (Path [Push $ stackElement'], ProgramPointState n0)
      _ -> itsMzero

-- Variable search -------------------------------------------------------------

alias :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
alias n1 n0 = do
  (CFGNode (UnannotatedClause (Clause x (VarBody x'))) _) <- Just n1
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x
          itsPure %@ ( Path [Push $ LookupVar x' patsp patsn]
                     , ProgramPointState n1 )
      _ -> itsMzero

skip :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
skip n1 n0 = do
  (CFGNode (UnannotatedClause (Clause x' _)) _) <- Just n1
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup /= x'
          itsPure %@ ( Path [Push $ stackElement], ProgramPointState n1 )
      _ -> itsMzero

blockMarkerSkip :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
blockMarkerSkip n1@(CFGNode anncl _) n0 =
  pure $ case anncl of
    StartClause _ -> itsPure %@ ( Path [], ProgramPointState n1 )
    EndClause _ -> itsPure %@ ( Path [], ProgramPointState n1 )
    _ -> itsMzero

-- Navigation ------------------------------------------------------------------

jump :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
jump _ _ =
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      Jump node -> itsPure %@ ( Path [], ProgramPointState node )
      _ -> itsMzero

capture :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
capture _ n0 =
  pure $ intensional Ord do
    stackElement <- pop
    stackElement' <- pop
    case stackElement' of
      Capture (CaptureSize n) ->
        let doCapture :: Int ->%Ord [PdsContinuation context]
                      ->%Ord CFGEdgeComputation context
            doCapture = \%Ord k elements ->
              if k == 0 then
                itsPure %$ ( Path $ map Push $
                                reverse elements ++ [stackElement]
                           , ProgramPointState n0 )
              else
                intensional Ord do
                  stackElement'' <- pop
                  doCapture %@ (k-1) %@ (stackElement'':elements)
        in
        doCapture %@ n %@ []
      _ -> itsMzero

-- Function wiring -------------------------------------------------------------

ruleFunctionEnterParameter :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
ruleFunctionEnterParameter n1 n0 = do
  (CFGNode (EnterClause x x' (Clause _ (ApplBody {}))) _) <- Just n1
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          () <- itsGuard %$ xlookup == x
          itsPure %@ ( Path [Push $ LookupVar x' patsp patsn]
                     , ProgramPointState n1 )
      _ -> itsMzero

ruleFunctionEnterNonLocal :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
ruleFunctionEnterNonLocal n1 n0 = do
  (CFGNode (EnterClause x x' cls@(Clause _ (ApplBody xf _ _))) _) <- Just n1
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          () <- itsGuard %$ xlookup /= x
          itsPure %@ ( Path [ Push $ LookupVar xf Set.empty Set.empty
                            , Push $ LookupVar xlookup patsp patsn
                            ]
                     , ProgramPointState n1 )
      _ -> itsMzero

ruleFunctionExit :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
ruleFunctionExit n1 n0 = do
  (CFGNode (ExitClause x x' (Clause _ (ApplBody {}))) _) <- Just n1
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          () <- itsGuard %$ xlookup == x
          itsPure %@ ( Path [Push $ LookupVar x' patsp patsn]
                     , ProgramPointState n1 )
      _ -> itsMzero

-- Conditional wiring ----------------------------------------------------------

conditionalTopSubjectPositive :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
conditionalTopSubjectPositive n1 n0 = do
  (CFGNode (EnterClause x' x1 cls) _) <- Just n1
  Clause x2 (ConditionalBody _ p (FunctionValue x'_ _) _) <- Just cls
  guard $ x' == x'_
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x' || xlookup == x1
          itsPure %@ ( Path [Push $ LookupVar x1 (Set.insert p patsp) patsn]
                     , ProgramPointState n1 )
      _ -> itsMzero

conditionalTopSubjectNegative :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
conditionalTopSubjectNegative n1 n0 = do
  (CFGNode (EnterClause x' x1 cls) _) <- Just n1
  Clause x2 (ConditionalBody _ p _ (FunctionValue x'_ _)) <- Just cls
  guard $ x' == x'_
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x' || xlookup == x1
          itsPure %@ ( Path [Push $ LookupVar x1 patsp (Set.insert p patsn)]
                     , ProgramPointState n1 )
      _ -> itsMzero

conditionalBottomReturnPositive :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
conditionalBottomReturnPositive n1 n0 = do
  (CFGNode (ExitClause x x' cls) _) <- Just n1
  Clause x2 (ConditionalBody x1 p (FunctionValue _ e) _) <- Just cls
  guard $ x' == retv e
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x
          itsPure %@ ( Path [ Push $ LookupVar x1 (Set.singleton p) Set.empty
                            , Push $ Jump n1
                            , Push $ LookupVar x' patsp patsn
                            ]
                     , ProgramPointState n1 )
      _ -> itsMzero

conditionalBottomReturnNegative :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
conditionalBottomReturnNegative n1 n0 = do
  (CFGNode (ExitClause x x' cls) _) <- Just n1
  Clause x2 (ConditionalBody x1 p _ (FunctionValue _ e)) <- Just cls
  guard $ x' == retv e
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x
          itsPure %@ ( Path [ Push $ LookupVar x1 Set.empty (Set.singleton p)
                            , Push $ Jump n1
                            , Push $ LookupVar x' patsp patsn
                            ]
                     , ProgramPointState n1 )
      _ -> itsMzero

conditionalTopNonSubjectVariable :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
conditionalTopNonSubjectVariable n1 n0 = do
  (CFGNode (EnterClause x' x1 cls) _) <- Just n1
  Clause x2 (ConditionalBody _ p _ _) <- Just cls
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup /= x' && xlookup /= x1
          itsPure %@ ( Path [ Push $ stackElement ]
                     , ProgramPointState n1 )
      _ -> itsMzero

-- Record construction/destruction ---------------------------------------------

recordProjectionStart :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
recordProjectionStart n1 n0 = do
  (CFGNode (UnannotatedClause (Clause x (ProjectionBody x' l))) _) <- Just n1
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x
          itsPure %@ ( Path [ Push $ LookupVar x' Set.empty Set.empty
                            , Push $ Project l patsp patsn
                            ]
                     , ProgramPointState n1 )
      _ -> itsMzero

recordProjectionStop :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
recordProjectionStop n1 n0 =
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      ContinuationValue (AbsFilteredVal
            (AbsValueRecord r@(RecordValue m)) patsp patsn) ->
        intensional Ord do
          stackElement <- pop
          case stackElement of
            Project l patsp' patsn' ->
              intensional Ord do
                itsGuard %$ Map.member l m
                let patCheck = List.all (\pat -> not $ Set.member pat patsn)
                                 [RecordPattern Map.empty, AnyPattern]
                if not $ isRecordPatternSet patsp && patCheck
                then throw $ InvariantFailureException "Record projection received a value that doesn't satisfy to the record pattern. This might be an error in the record-value-filter-validation rule (7b at the time of this writing)."
                else
                  let patsnsel = negativePatternSetSelection r patsn in
                  let x' = (Map.!) m l in
                  let patsp'' =
                        Set.union patsp' $ patternSetProjection patsp l
                  in
                  let patsn'' =
                        Set.union patsn' $ patternSetProjection patsnsel l
                  in
                  itsPure %$ ( Path [Push $ LookupVar x' patsp'' patsn'']
                             , ProgramPointState n0)
            _ -> itsMzero
      _ -> itsMzero

-- Aggregate computations ------------------------------------------------------

computationForEdge :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdge context
    -> [( PdsState context
        , PdsReachability.PDRM (PlumePds context)
          ( PdsReachability.Path (PlumePds context)
          , PdsState context
          )
        )
       ]
computationForEdge (CFGEdge n1 n0) =
  -- TODO: remaining rules
  let rules = [ discoveredOrIntermediateValue
              , alias
              , skip
              , blockMarkerSkip
              , jump
              , capture
              , ruleFunctionEnterParameter
              , ruleFunctionEnterNonLocal
              , ruleFunctionExit
              , conditionalTopSubjectPositive
              , conditionalTopSubjectNegative
              , conditionalBottomReturnPositive
              , conditionalBottomReturnNegative
              , conditionalTopNonSubjectVariable
              , recordProjectionStart
              , recordProjectionStop
              ]
  in
  rules
  & Maybe.mapMaybe
      (\rule ->
        let maybeComputation = rule n1 n0 in
        fmap (ProgramPointState n0,) maybeComputation
      )
