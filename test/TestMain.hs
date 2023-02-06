module Main where

import Test.Tasty

import qualified Spec
import qualified PrimeTest
import qualified TestingFramework.TestFiles

main :: IO ()
main = do
  unitTests <- TestingFramework.TestFiles.tests
  defaultMain (testGroup "all tests" [Spec.tests, PrimeTest.tests, unitTests])
