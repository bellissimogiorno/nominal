module Language.Nominal.NameSetSpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Properties.SpecUtilities ()

import Language.Nominal.Properties.NameSetSpec

spec :: Spec
spec = do
    it "ns disjoint ns', if apart" $ property prop_supp_apart
    it "ns disjoint ns' iff apart, if triv labels" $ property prop_supp_apart_atom
