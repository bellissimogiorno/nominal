module Language.Nominal.NamesSpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Names 
import Language.Nominal.Nom

import Language.Nominal.SpecUtilities ()

import Language.Nominal.Properties.NamesSpec

spec :: Spec
spec = do
    it "nameLabel (nameOverwriteLabel t n) == t" $ property prop_namelabel
    it "Name equality depends on the atom, not the label" $ property prop_namelabel_eq_irrelevant
    it "(n' n).x = x  (we expect this to fail)" $ property prop_singleswap
    it "n',n#x => (n' n).x = x.  Test on x a tuple" $ property prop_freshswap
    it "(n' n).(n' n).x = x" $ property prop_doubleswap
    it "n'',n'#x => (n'' n').(n' n).m = (n'' n).m" $ property prop_doubleswap_fresh'
    it "n'#x => (n'' n').(n' n).x = (n'' n).x" $ property prop_doubleswap_fresh

