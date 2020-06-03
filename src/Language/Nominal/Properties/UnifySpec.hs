{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
-- {-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE TypeApplications       #-}

{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Nominal.Properties.UnifySpec
    where

import Data.Set                      as S
import Test.QuickCheck

import Language.Nominal.Name 
import Language.Nominal.NameSet 
import Language.Nominal.Nom
import Language.Nominal.Binder
import Language.Nominal.Abs
import Language.Nominal.Unify

-- | l is unifiable with  l' for any l and l'
-- Should fail, taking e.g. l = [] and l' nonempty
prop_l_l' :: [Name Int] -> [Name Int] -> Property 
prop_l_l' ns' ns = expectFailure $ unifiablePerm ns ns' 

-- | ns @> ns' @> x  is unifiable with  ns' @> ns @> x  
prop_res_res :: [Atom] -> [Atom] -> [Atom] -> Bool
prop_res_res ns' ns x = kunifiablePerm atTom (restrict ns' ((ns @> x) :: Nom [Atom])) (restrict ns (ns' @> x))

-- | x' -> ns x -> res ns x unifies with x'
prop_res_unres :: Nom [Name Int] -> Bool
prop_res_unres x' = x' @@! \atms x -> unifiablePerm x' $ atms @> x

-- | Unifiers correctly calculated 
prop_unify_ren :: [Name ()] -> [Name ()] -> Property 
prop_unify_ren a b = let a' = Prelude.take 5 a -- control size so decent chance are unifiable
                         b' = Prelude.take 5 b
                     in unifiablePerm a' b' ==> ren (unifyPerm a' b') a' === b'

-- | 'idRen' equals 'idRen' extended with an identity mapping (since equality is on nub).
prop_renId :: Atom -> Bool
prop_renId a = renExtend a a idRen == idRen 


-- | Permutations and freshening renamings coincide
iprop_fresh_ren :: (UnifyPerm a, Support a, Swappable a, Eq a) => a -> Bool
iprop_fresh_ren a = let (atms :: [Atom]) = S.toList $ supp a in unNom $ do -- Nom monad
   atms' <- freshKAtoms atms
   let p = zip atms atms'
   return $ perm p a == ren (renFromList p) a 

prop_fresh_ren_atmlistlist :: [[Atom]] -> Bool
prop_fresh_ren_atmlistlist = iprop_fresh_ren 

prop_fresh_ren_absatmlist :: Abs () [Atom] -> Bool
prop_fresh_ren_absatmlist = iprop_fresh_ren 

-- TODO: arbitrary instance for Ren?
