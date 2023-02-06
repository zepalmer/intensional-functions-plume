{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module PdsReachability.UserDataTypes where

import PdsReachability.Specification

data StackAction a
  = Push (Element a)
  | Pop (Element a)
  | Nop
deriving instance (SpecIs Eq a) => (Eq (StackAction a))
deriving instance (SpecIs Ord a) => (Ord (StackAction a))
deriving instance (SpecIs Show a) => (Show (StackAction a))

data Edge a
  = Edge (Node a) (StackAction a) (Node a)
deriving instance (SpecIs Eq a) => (Eq (Edge a))
deriving instance (SpecIs Ord a) => (Ord (Edge a))
deriving instance (SpecIs Show a) => (Show (Edge a))

data Path a = Path [StackAction a]
deriving instance (SpecIs Eq a) => (Eq (Path a))
deriving instance (SpecIs Ord a) => (Ord (Path a))
deriving instance (SpecIs Show a) => (Show (Path a))

-- TODO: consider whether this type is necessary.  If it is, it
-- may need to be more complicated; it used to return a "terminus".
-- For instance, it may be that this function needs to produce a
-- general computation rather than just a path (so that e.g. it could
-- yield the computation that handles jumps).
data EdgeFunction a = EdgeFunction (Node a -> [(Path a, Node a)])

data Question a = Question (Node a) [StackAction a]
deriving instance (SpecIs Show a) => (Show (Question a))
deriving instance (SpecIs Eq a) => (Eq (Question a))
deriving instance (SpecIs Ord a) => (Ord (Question a))
