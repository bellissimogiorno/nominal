module Language.Nominal.UtilitiesSpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Properties.SpecUtilities ()

import Language.Nominal.Properties.UtilitiesSpec

spec :: Spec
spec = do
    it "superSucc on [Int]" $ property prop_test_rewrite1
    it "superSucc on [Name Int]" $ property prop_test_rewrite2

