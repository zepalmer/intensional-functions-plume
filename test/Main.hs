module Main where

import Test.Tasty

import qualified PrimeTest
import qualified TestingFramework.TestFiles

main :: IO ()
main = do
  unitTests <- TestingFramework.TestFiles.tests
  defaultMain (testGroup "all tests"
    [ PrimeTest.tests
    , unitTests
    ])
