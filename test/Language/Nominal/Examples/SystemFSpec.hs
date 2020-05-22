module Language.Nominal.Examples.SystemFSpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Properties.SpecUtilities ()

import Language.Nominal.Properties.Examples.SystemFSpec

spec :: Spec
spec = do
    it "(id id) has no type (it needs a type argument)" $ property prop_untypeable
    describe "y[n-> var n] = y" $ do
        it "typevar'" $ property prop_sub_id_typevar'
        it "termvar" $ property prop_sub_id_termvar
        it "typevar" $ property prop_sub_id_typevar
    describe "n # y => y[n->x] = y" $ do
        it "typevar'" $ property prop_sub_fresh_typevar'
        it "typevar" $ property prop_sub_fresh_typevar
        it "termvar" $ property prop_sub_fresh_termvar
    describe "n' # y => y[n->n'] = (n' n).y" $ do
        it "typevar'" $ property prop_sub_perm_typevar'
        it "typevar''" $ property prop_sub_perm_typevar''
        it "termvar" $ property prop_sub_perm_termvar
    it "normal forms are typeable" $ property prop_typeable_nf
    it "typeable terms are normalisable" $ property prop_nf_typeable
    it "Type soundness: if a term is typeable and normalisable then its normal form has the same type as it does." $
        property prop_type_soundness
    it "Not all terms are typeable" $ property prop_all_typeable
    it "typeof(id t) = typeof(t)" $ property prop_id_type_unchanged
    it "If x : t then (id t x) --> x" $ property prop_app_id
    it "0 : nat" $ property prop_typeof_zero
    it "i+1 /= 0" $ property prop_church_numerals0
    it "i+1 /= i" $ property prop_church_numerals1
    it "i : nat" $ property prop_church_numerals_type
 
