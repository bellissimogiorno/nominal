module Language.Nominal.UnifySpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Properties.SpecUtilities ()

import Language.Nominal.Properties.UnifySpec

spec :: Spec
spec = do
    it "l is not always unifiable with l', e.g. l = [] and l' nonempty" $ property prop_l_l'
    it "res ns' (res ns x)  unifiable with  res ns (res ns' x)" $ property prop_res_res
    it "x' -> ns x -> res ns x  unifies with x'" $ property prop_res_unres
    it "Unifiers correctly calculated" $ property prop_unify_ren
    it "Permutations and freshening renamings coincide (lists of lists of atoms)" $ property prop_fresh_ren_atmlistlist
    it "Permutations and freshening renamings coincide (abstractions of lists of atoms)" $ property prop_fresh_ren_absatmlist


