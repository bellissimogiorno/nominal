module Language.Nominal.Properties.NameSetSpec
    where

import qualified Data.List.Extra as L
import           Test.QuickCheck

import           Language.Nominal.Name 
import           Language.Nominal.NameSet
-- import           Language.Nominal.Properties.SpecUtilities

-- ns disjoint ns', if apart 
prop_supp_apart :: [Name Bool] -> [Name Bool] -> Property 
prop_supp_apart ns ns' = (take 4 ns `apart` take 4 ns') ==> take 4 ns `L.disjoint` take 4 ns'  -- restrict length so tests don't give up

-- ns disjoint ns' iff apart, if triv labels 
prop_supp_apart_atom :: [Name ()] -> [Name ()] -> Bool 
prop_supp_apart_atom ns ns' = (ns `apart` ns') == ns `L.disjoint` ns'

{-- supp([[a]]) = supp(unions [a])
prop_supp_unions :: [[Name Int]] -> Bool 
prop_supp_unions l = supp (S.unions --} 
