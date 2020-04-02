module Language.Nominal.AbsSpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Names 
import Language.Nominal.Nom
import Language.Nominal.Abs

import Language.Nominal.SpecUtilities ()

import Language.Nominal.Properties.AbsSpec

spec :: Spec
spec = do
    it "fuse a.x a.x' = a.(x,x')" $ property prop_fuse
    it "n # x => [n](x @ n) = x" $ property prop_Abs_Conc
    it "n' # x => [n]x = [n'](n' n).x" $ property prop_Abs_alpha
    it "(n.x) \\@ n = x" $ property prop_Conc_Abs
    it "(n.x) \\@ n = x" $ property prop_Conc_Abs_swap
    it "Atm.(X x Y) iso Atm.X x Atm.Y, left-to-right-to-left" $ property prop_fuse_unfuse_Abs
    it "Atm.(X x Y) iso Atm.X x Atm.Y, right-to-left-to-right" $ property prop_unfuse_fuse_Abs
    it "Iso fails if atoms labelled, since one label lost Atm.X x Atm.Y -> Atm.(X x Y)" $ property prop_unfuse_fuse_Abs'
    it "Atm.X iso Nom (Atm x X)" $ property prop_abs_to_nom

