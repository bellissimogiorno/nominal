module Language.Nominal.NomSpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Names 
import Language.Nominal.Nom

import Language.Nominal.SpecUtilities ()

import Language.Nominal.Properties.NomSpec

spec :: Spec
spec = do
    it "Check restriction creates local scope. Should return False." $ property prop_split_scope
    it "n' # n if n' is chosen fresh, after n" $ property prop_fresh_neq
    it "freshName () /= freshName (). Lazy evaluation means distinct fresh names generated." $ property prop_fresh_neq'
    it "Same thing using let." $ property prop_fresh_neq''
    it "But if we unpack a single fresh name monadically, we can compare it for equality." $ property prop_fresh_eq
    it "~ (n # (n,n'))" $ property prop_isFresh1
    it "n # n'" $ property prop_isFresh2



