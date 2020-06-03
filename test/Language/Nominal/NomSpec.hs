module Language.Nominal.NomSpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Properties.SpecUtilities ()

import Language.Nominal.Properties.NomSpec

spec :: Spec
spec = do
    it "Nom creates local binding, which is unpacked separately by equality." $ property prop_x_neq_x
    it "Check restriction creates local scope. Should return False." $ property prop_split_scope
    it "n' # n if n' is chosen fresh, after n" $ property prop_fresh_neq
    it "freshName () /= freshName (). Lazy evaluation means distinct fresh names generated." $ property prop_fresh_neq'
    it "Same thing using let." $ property prop_fresh_neq''
    it "But if we unpack a single fresh name monadically, we can compare it for equality." $ property prop_fresh_eq
    it "~ (n # (n,n'))" $ property prop_freshFor1
    it "n # n'" $ property prop_freshFor2
    it "Nom Maybe -> Maybe Nom -> Nom Maybe = id" $ property prop_transposeNomMaybe
    it "Maybe Nom -> Nom Maybe -> Maybe Nom = id" $ property prop_transposeMaybeNom
    it "a,b#x |- (a b).x = x" $ property prop_new'
    it "a#x |/- (a b).x = x" $ property prop_not_new'
    it "a,b#x |- (a b).x = x" $ property prop_new
    it "n#l iff n not in l, for n a name and l a list of names" $ property prop_freshFor_notElem
    it "atoms-restriction precisely removes atoms from support (atom list)" $ property prop_support_nom_atmlist 
    it "atoms-restriction precisely removes atoms from support (nom of atom list)" $ property prop_support_nom_nomatmlist 
    it "if we freshen all atoms in an element, its support is apart from the original (atom list)" $ property prop_freshen_apart_atmlist 
    it "if we freshen all atoms in an element, its support is apart from the original (nom atom list)" $ property prop_freshen_apart_nom_atmlist 
    it  "a freshened list of atoms is disjoint from its original" $ property prop_freshen_apart_disjoint 
    it  "two notions of trivial Nom binding are equal" $ property prop_isTrivial_equal 
    it  "isTrivial sanity check (supp version)" $ property prop_isTrivial_sane 
    it  "isTrivial sanity check (freshFor version)" $ property prop_isTrivial_sane' 
