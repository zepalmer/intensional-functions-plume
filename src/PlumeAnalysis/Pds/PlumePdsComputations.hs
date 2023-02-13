{-# LANGUAGE IntensionalFunctions #-}
{-# LANGUAGE TupleSections #-}

module PlumeAnalysis.Pds.PlumePdsComputations where

import AST.AbstractAst
import AST.Ast
import qualified PlumeAnalysis.Context as C
import qualified PdsReachability
import PdsReachability (pop, Path(..), StackAction(..))
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph

import Control.Intensional.Applicative
import Control.Intensional.MonadPlus
import Control.Intensional.Runtime
import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

type CFGEdgeComputationFunction context =
    CFGNode context -> CFGNode context
 -> Maybe (PdsReachability.PDRM (PlumePds context)
           ( PdsReachability.Path (PlumePds context)
           , PdsState context
           )
          )

-- Function wiring -------------------------------------------------------------

ruleFunctionEnterParameter :: forall context.
       ( Typeable context, Ord context, Show context
       , IntensionalMonadPlusZeroC (PdsReachability.PDRM (PlumePds context)) ()
       , IntensionalMonadPlusZeroC (PdsReachability.PDRM (PlumePds context))
            (Path (PlumePds context), PdsState context)
       )
    => CFGEdgeComputationFunction context
ruleFunctionEnterParameter n1 n0 = do
  (CFGNode (EnterClause x x' cls) context) <- Just n1
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          () <- itsGuard %$ xlookup == x
          itsPure %@ ( Path [Push $ LookupVar x' patsp patsn]
                     , ProgramPointState n1
                     )
      _ -> itsMzero

ruleFunctionEnterNonLocal :: forall context.
       ( Typeable context, Ord context, Show context
       , IntensionalMonadPlusZeroC (PdsReachability.PDRM (PlumePds context)) ()
       )
    => CFGEdgeComputationFunction context
ruleFunctionEnterNonLocal n1 n0 = do
  (CFGNode (EnterClause x x' cls@(Clause _ (ApplBody xf _ _)))
        context) <- Just n1
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          () <- itsGuard %$ xlookup /= x
          itsPure %@ ( Path [ Push $ LookupVar xf Set.empty Set.empty
                            , Push $ LookupVar xlookup patsp patsn
                            ]
                     , ProgramPointState n1
                     )
      _ -> itsMzero

ruleFunctionExit :: forall context.
       ( Typeable context, Ord context, Show context
       , IntensionalMonadPlusZeroC (PdsReachability.PDRM (PlumePds context)) ()
       , IntensionalMonadPlusZeroC (PdsReachability.PDRM (PlumePds context))
            (Path (PlumePds context), PdsState context)
       )
    => CFGEdgeComputationFunction context
ruleFunctionExit n1 n0 = do
  (CFGNode (ExitClause x x' cls) context) <- Just n1
  pure $ intensional Ord do
    stackElement <- pop
    case stackElement of
      LookupVar xlookup patsp patsn ->
        intensional Ord do
          () <- itsGuard %$ xlookup == x
          itsPure %@ ( Path [Push $ LookupVar x' patsp patsn]
                     , ProgramPointState n1
                     )
      _ -> itsMzero

-- Aggregate computations ------------------------------------------------------

computationForEdge :: forall context.
       ( Typeable context, Ord context, Show context
       , IntensionalMonadPlusZeroC (PdsReachability.PDRM (PlumePds context)) ()
       , IntensionalMonadPlusZeroC (PdsReachability.PDRM (PlumePds context))
            (Path (PlumePds context), PdsState context)
       )
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
  let rules = [ ruleFunctionEnterParameter
              , ruleFunctionExit
              ]
  in
  rules
  & Maybe.mapMaybe
      (\rule ->
        let maybeComputation = rule n1 n0 in
        fmap (ProgramPointState n0,) maybeComputation
      )
