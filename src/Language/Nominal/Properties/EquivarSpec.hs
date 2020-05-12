{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE PolyKinds           #-}

-- {-# OPTIONS_GHC -Wno-orphans #-}


module Language.Nominal.Properties.EquivarSpec
    where

import Language.Nominal.Name 
import Language.Nominal.Equivar

-- | Only one orbit of atoms 
prop_atoms_one_orbit :: [Name ()] -> Bool
prop_atoms_one_orbit [] = length (evRep ([] :: [Name Int])) == 0
prop_atoms_one_orbit l  = length (evRep l)  == 1

-- | Two orbits of atom pairs (equal, or disjoint) 
prop_atomssq_orbit :: [(Name (),Name ())] -> Bool
prop_atomssq_orbit l  = length (evRep l) <= 2

-- TODO: more tests

