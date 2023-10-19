{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}

module PlumeAnalysis.Pds.PlumePdsComputations
( computationsForEdge
) where

import AST.AbstractAst
import AST.Ast
import AST.AstUtils
import qualified PlumeAnalysis.Context as C
import qualified PdsReachability
import PdsReachability (pop, pdrmMaybe, pdrmChoose, Element, Path(..), StackAction(..))
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph
import PlumeAnalysis.Utils.PlumeUtils
import Utils.Exception

import Control.Exception
import Control.Intensional.Functor
import Control.Intensional.Applicative
import Control.Intensional.Monad
import Control.Intensional.MonadPlus
import Control.Intensional.Runtime
import Control.Intensional.Runtime.NonEmptyHList
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
    CFGNode context -> CFGNode context -> [CFGEdgeComputation context]

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
  (CFGNode (UnannotatedClause (Clause x (VarBody x'))) _) <- [n1]
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
  (CFGNode (UnannotatedClause (Clause x' _)) _) <- [n1]
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

doCapture :: forall context.
             (Typeable context, Ord context, Show context)
          => '[ CFGNode context
              , PdsContinuation context
              , Int
              , [PdsContinuation context]
              ]
     ->%%Ord CFGEdgeComputation context
doCapture = \%%Ord n0 capturedElement k elements ->
    if k == 0 then
      itsPure %$ ( Path $ map Push $
                    capturedElement : elements
                 , ProgramPointState n0 )
    else
      intensional Ord do
        stackElement <- pop
        doCapture %@% (n0, capturedElement, (k-1), (stackElement:elements))

capture :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
capture _ n0 =
  pure $ intensional Ord do
    stackElement <- pop
    stackElement' <- pop
    case stackElement' of
      Capture (CaptureSize captureSize) ->
        doCapture %@% (n0, stackElement, captureSize, [])
      _ -> itsMzero

-- Function wiring -------------------------------------------------------------

ruleFunctionEnterParameter :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
ruleFunctionEnterParameter n1 n0 = do
  (CFGNode (EnterClause x x' (Clause _ (ApplBody {}))) _) <- [n1]
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
  (CFGNode (EnterClause x x' cls@(Clause _ (ApplBody xf _ _))) _) <- [n1]
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          () <- itsGuard %$ xlookup /= x
          itsPure %@ ( Path [ Push $ LookupVar xlookup patsp patsn
                            , Push $ LookupVar xf Set.empty Set.empty
                            ]
                     , ProgramPointState n1 )
      _ -> itsMzero

ruleFunctionExit :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
ruleFunctionExit n1 n0 = do
  (CFGNode (ExitClause x x' (Clause _ (ApplBody {}))) _) <- [n1]
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x
          itsPure %@ ( Path [Push $ LookupVar x' patsp patsn]
                     , ProgramPointState n1 )
      _ -> itsMzero

-- Conditional wiring ----------------------------------------------------------

conditionalTopSubjectPositive :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
conditionalTopSubjectPositive n1 n0 = do
  (CFGNode (EnterClause x' x1 cls) _) <- [n1]
  Clause x2 (ConditionalBody _ p (FunctionValue x'_ _) _) <- [cls]
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
  (CFGNode (EnterClause x' x1 cls) _) <- [n1]
  Clause x2 (ConditionalBody _ p _ (FunctionValue x'_ _)) <- [cls]
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
  (CFGNode (ExitClause x x' cls) _) <- [n1]
  Clause x2 (ConditionalBody x1 p (FunctionValue _ e) _) <- [cls]
  guard $ x' == retv e
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x
          itsPure %@ ( Path [ Push $ LookupVar x' patsp patsn
                            , Push $ Jump n1
                            , Push $ LookupVar x1 (Set.singleton p) Set.empty
                            ]
                     , ProgramPointState n1 )
      _ -> itsMzero

conditionalBottomReturnNegative :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
conditionalBottomReturnNegative n1 n0 = do
  (CFGNode (ExitClause x x' cls) _) <- [n1]
  Clause x2 (ConditionalBody x1 p _ (FunctionValue _ e)) <- [cls]
  guard $ x' == retv e
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x
          itsPure %@ ( Path [ Push $ LookupVar x' patsp patsn
                            , Push $ Jump n1
                            , Push $ LookupVar x1 Set.empty (Set.singleton p)
                            ]
                     , ProgramPointState n1 )
      _ -> itsMzero

conditionalTopNonSubjectVariable :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
conditionalTopNonSubjectVariable n1 n0 = do
  (CFGNode (EnterClause x' x1 cls) _) <- [n1]
  Clause x2 (ConditionalBody _ p _ _) <- [cls]
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
  (CFGNode (UnannotatedClause (Clause x (ProjectionBody x' l))) _) <- [n1]
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x
          itsPure %@ ( Path [ Push $ Project l patsp patsn
                            , Push $ LookupVar x' Set.empty Set.empty
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

-- Filter validation -----------------------------------------------------------

filterImmediate :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
filterImmediate n1 n0 = do
  CFGNode (UnannotatedClause (Clause x (ValueBody v))) _ <- [n1]
  patsLegal <- Maybe.maybeToList $ immediatelyMatchedBy v
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x
          let patCheck =
                List.all (\pat -> not $ Set.member pat patsn)
                         [FunPattern, AnyPattern]
          itsGuard %$ (patsp `Set.isSubsetOf` patsLegal) &&
                      Set.disjoint patsn patsLegal && patCheck
          let absFilteredVal = AbsFilteredVal v Set.empty Set.empty
          itsPure %@ ( Path [Push $ ContinuationValue absFilteredVal]
                     , ProgramPointState n1 )
      _ -> itsMzero

filterRecord :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
filterRecord n1 n0 = do
  CFGNode (UnannotatedClause (Clause x (ValueBody v))) _ <- [n1]
  AbsValueRecord r@(RecordValue m) <- [v]
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          itsGuard %$ xlookup == x
          let patCheck =
                List.all (\pat -> not $ Set.member pat patsn)
                  [RecordPattern Map.empty, AnyPattern]
          itsGuard %$ isRecordPatternSet patsp && patCheck
          let patsn' = negativePatternSetSelection r patsn
          let patternSetLabels = labelsInPatternSet patsp
          let recordLabels = labelsInRecord r
          itsGuard %$ patternSetLabels `Set.isSubsetOf` recordLabels
          let makeK'' l =
                let x'' = (Map.!) m l in
                [ Push $ LookupVar x'' (patternSetProjection patsp l)
                                       (patternSetProjection patsn' l)
                , Push $ Jump n1
                ]
          let firstPushes =
                [ Push $ ContinuationValue $ AbsFilteredVal v patsp patsn'
                , Push $ Jump n1
                ]
          let allPushes =
                recordLabels
                & Set.toList
                & List.map makeK''
                & List.concat
                & (++) firstPushes
          itsPure %@ (Path allPushes, ProgramPointState n1)
      _ -> itsMzero

-- Binary operators ------------------------------------------------------------

binaryOperationStart :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
binaryOperationStart n1 n0 = do
  CFGNode (UnannotatedClause
              (Clause x1 (BinaryOperationBody x2 _ x3))) _ <- [n1]
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup _ _ ->
        intensional Ord do
          itsGuard %$ xlookup == x1
          let k1'' = [ Capture $ CaptureSize 5
                     , LookupVar x2 Set.empty Set.empty]
          let k2'' = [ Capture $ CaptureSize 2
                     , LookupVar x3 Set.empty Set.empty
                     , Jump n1 ]
          let k3'' = [ BinaryOperation, Jump n0 ]
          let k0 = [stackElement]
          itsPure %@ ( Path $ List.map Push $ k0 ++ k3'' ++ k2'' ++ k1''
                     , ProgramPointState n1 )
      _ -> itsMzero

binaryOperationEvaluation :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
binaryOperationEvaluation n1 n0 = do
  CFGNode (UnannotatedClause
              (Clause x1 (BinaryOperationBody x2 op x3))) _ <- [n1]
  pure $ intensional Ord do
    stackElement1 <- pop
    case stackElement1 of
      BinaryOperation ->
        intensional Ord do
          stackElement2 <- pop
          case stackElement2 of
            ContinuationValue (AbsFilteredVal v2 patsp patsn) ->
              intensional Ord do
                itsGuard %$ Set.null patsp && Set.null patsn
                stackElement3 <- pop
                case stackElement3 of
                  ContinuationValue (AbsFilteredVal v1 patsp' patsn') ->
                    intensional Ord do
                      itsGuard %$ Set.null patsp' && Set.null patsn'
                      resultValues <- pdrmMaybe $
                                        abstractBinaryOperation op v1 v2
                      stackElement4 <- pop
                      case stackElement4 of
                        LookupVar xlookup patsplookup patsnlookup ->
                          intensional Ord do
                            itsGuard %$ x1 == xlookup
                            resultValue <- pdrmChoose resultValues
                            immediatePatterns <- pdrmMaybe $
                                                immediatelyMatchedBy resultValue
                            itsGuard %$ patsp `Set.isSubsetOf` immediatePatterns
                                    && Set.disjoint immediatePatterns patsn
                            itsPure %@ ( Path [Push $ ContinuationValue $
                                                AbsFilteredVal resultValue
                                                    Set.empty Set.empty]
                                       , ProgramPointState n1
                                       )
                        _ -> itsMzero
                  _ -> itsMzero
            _ -> itsMzero
      _ -> itsMzero

unaryOperationStart :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
unaryOperationStart n1 n0 = do
  CFGNode (UnannotatedClause
              (Clause x1 (UnaryOperationBody _ x2))) _ <- [n1]
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup _ _ ->
        intensional Ord do
          itsGuard %$ xlookup == x1
          let k1'' = [ Capture $ CaptureSize 2
                     , LookupVar x2 Set.empty Set.empty ]
          let k2'' = [ UnaryOperation, Jump n0 ]
          let k0 = [stackElement]
          itsPure %@ ( Path $ List.map Push $ k0 ++ k2'' ++ k1''
                     , ProgramPointState n1 )
      _ -> itsMzero

unaryOperationEvaluation :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdgeComputationFunction context
unaryOperationEvaluation n1 n0 = do
  CFGNode (UnannotatedClause
              (Clause x1 (UnaryOperationBody op x2))) _ <- [n1]
  pure $ intensional Ord do
    stackElement1 <- pop
    case stackElement1 of
      UnaryOperation ->
        intensional Ord do
          stackElement2 <- pop
          case stackElement2 of
            ContinuationValue (AbsFilteredVal v patsp patsn) ->
              intensional Ord do
                itsGuard %$ Set.null patsp && Set.null patsn
                resultValues <- pdrmMaybe $ abstractUnaryOperation op v
                stackElement3 <- pop
                case stackElement3 of
                  LookupVar xlookup patsplookup patsnlookup ->
                    intensional Ord do
                      itsGuard %$ x1 == xlookup
                      resultValue <- pdrmChoose resultValues
                      immediatePatterns <- pdrmMaybe $
                                            immediatelyMatchedBy resultValue
                      itsGuard %$ patsp `Set.isSubsetOf` immediatePatterns
                               && Set.disjoint immediatePatterns patsn
                      itsPure %@ ( Path [Push $ ContinuationValue $
                                            AbsFilteredVal resultValue
                                                Set.empty Set.empty]
                                 , ProgramPointState n1
                                 )
                  _ -> itsMzero
            _ -> itsMzero
      _ -> itsMzero

-- Aggregate computations ------------------------------------------------------

computationsForEdge :: forall context.
       (CFGEdgeComputationFunctionConstraints context)
    => CFGEdge context
    -> [( PdsState context
        , PdsReachability.PDRM (PlumePds context)
          ( PdsReachability.Path (PlumePds context)
          , PdsState context
          )
        )
       ]
computationsForEdge (CFGEdge n1 n0) =
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
              , filterImmediate
              , filterRecord
              , binaryOperationStart
              , binaryOperationEvaluation
              , unaryOperationStart
              , unaryOperationEvaluation
              ]
  in
  rules
  & List.map
      (\rule ->
        let computations = rule n1 n0 in
        fmap (ProgramPointState n0,) computations
      )
  & List.concat
