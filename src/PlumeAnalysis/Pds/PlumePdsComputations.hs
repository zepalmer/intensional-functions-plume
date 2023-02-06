{-# LANGUAGE TupleSections #-}

module PlumeAnalysis.Pds.PlumePdsComputations where

import AST.AbstractAst
import qualified PlumeAnalysis.Context as C
import qualified PdsReachability
import PlumeAnalysis.Pds.PlumePdsStructureTypes
import PlumeAnalysis.PlumeSpecification
import PlumeAnalysis.Types.PlumeGraph

import Data.Function ((&))
import qualified Data.List as List
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe

-- Function wiring
ruleFunctionTopParameterVariable ::
    CFGNode context -> CFGNode context
 -> Maybe (PdsReachability.PDRM (PlumePds context)
           ( PdsReachability.Path (PlumePds context)
           , PdsState context
           )
          )
ruleFunctionTopParameterVariable n1 n0 =
  undefined -- TODO

computationForEdge :: CFGEdge context
                   -> [( PdsState context
                       , PdsReachability.PDRM (PlumePds context)
                         ( PdsReachability.Path (PlumePds context)
                         , PdsState context
                         )
                       )
                      ]
computationForEdge (CFGEdge n1 n0) =
  let rules = [ ruleFunctionTopParameterVariable
              ]
  in
  rules
  & Maybe.mapMaybe
      (\rule ->
        let maybeComputation = rule n1 n0 in
        fmap (ProgramPointState n0,) maybeComputation
      )
  -- TODO: port work from PdsEdgeFunctions to here



-- Old notes below:
{-
let edge = CFGNode n1 n0 in
let computation =
      case n1 of
        CFGNode (EnterClause x x' (Clause _ (ApplBody _ x3'' _))) _ ->
          intensional Ord do
            LookupVar x'' patsp patsn <- pop
            itsGuard (x' == x'')
            itsPure $ ( Path $ [Push $ LookupVar x1 patsp patsn]
                      , ProgramPointState n1
                      )
in
let pds' = PdsReachability.addPathComputation
            (ProgramPointState n0)
            computation
            pds
in
...







               , case n1 of
                    CFGNode (EnterClause x x' c) _ ->
                      case c of
                        -- NOTE: ignoring call site annotations
                        -- as none apply to Plume lookup.
                        Clause _ (ApplBody _ x3'' _) ->
                          if not (x' == x3'') then undefined
                          else
                            return (VariableAliasing x x', ProgramPointState n1)
                        otherwise -> mzero
                    otherwise -> mzero

case element of
        LookupVar x' patsp patsn ->
          if (x' == x2)
          then return $ Path $ [Push $ LookupVar x1 patsp patsn]
          else mzero
        otherwise -> mzero






-}
