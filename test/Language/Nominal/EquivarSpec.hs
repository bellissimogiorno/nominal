module Language.Nominal.EquivarSpec
    ( spec
    ) where

import Test.Hspec
import Test.QuickCheck

import Language.Nominal.Properties.SpecUtilities ()

import Language.Nominal.Properties.EquivarSpec

spec :: Spec
spec = do
    it "Atoms one orbit" $ property prop_atoms_one_orbit
    it "Two orbits of atoms pairs (equal, or distinct)" $ property prop_atomssq_orbit


