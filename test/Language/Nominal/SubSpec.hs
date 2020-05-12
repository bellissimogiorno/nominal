module Language.Nominal.SubSpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Properties.SpecUtilities ()

import Language.Nominal.Properties.SubSpec

spec :: Spec
spec = do
    it "[n1][n1 -> n2] = [n2]" $ property prop_sub_singleton1 
    it "[n2][n1 -> n2] = [n2]" $ property prop_sub_singleton2 
    it "n#n1,n2 ==> (n.x)[n1 -> n2] = n.(x[n1 -> n2])" $ property prop_sub_abs_1
    it "(n.x)[n1 -> n2] = n.(x[n1 -> n2]) fails in general" $ property prop_sub_abs_1' 
    it "(n.x)[n -> n2] = n.x" $ property prop_sub_abs_3 
