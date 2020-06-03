module Language.Nominal.Properties.AbsSpec
     where

import Test.QuickCheck

import Language.Nominal.Name 
import Language.Nominal.Nom
import Language.Nominal.Binder
import Language.Nominal.Abs
import Language.Nominal.Unify
import Language.Nominal.Properties.SpecUtilities ()

-- | @fuse a.x a.x' = a.(x,x')@
prop_fuse :: Name () -> [Name ()] -> [Name ()] -> Bool
prop_fuse n a b = fuse (abst n a, abst n b) == abst n (a,b)

-- | @n # x => [n](x @ n) = x@
prop_Abs_Conc :: Name () -> Abs () [Name ()] -> Property 
prop_Abs_Conc n x = n `freshFor` x ==> (abst n (conc x n) === x) 

-- | @n' # x => [n]x = [n'](n' n).x@
prop_Abs_alpha :: Name () -> Name () -> [Name()] -> Property
prop_Abs_alpha n n' l = n' `freshFor` l ==> (abst n l === abst n' (swpN n' n l))

-- | @(n.x) \@ n = x@
prop_Conc_Abs :: Name () -> [Name ()] -> Property 
prop_Conc_Abs n x = conc (abst n x) n === x

-- | @(n.x) \@ n' = (n' n).x@
prop_Conc_Abs_swap :: Name () -> Name () -> [Name ()] -> Property 
prop_Conc_Abs_swap n n' x = n' `freshFor` x ==> conc (abst n x) n' === swpN n' n x

-- | Atm.(X x Y) iso Atm.X x Atm.Y, left-to-right-to-left
prop_fuse_unfuse_Abs :: Abs () ([Name ()], [Name ()]) -> Property 
prop_fuse_unfuse_Abs x = (fuse . unfuse) x === x 

-- | Atm.(X x Y) iso Atm.X x Atm.Y, right-to-left-to-right
prop_unfuse_fuse_Abs :: (Abs () [Name ()], Abs () [Name ()]) -> Property 
prop_unfuse_fuse_Abs (a, b) = (unfuse . fuse) (a, b) === (a, b) 

-- | Iso fails if atoms labelled, since one label lost Atm.X x Atm.Y -> Atm.(X x Y), and one label invented if list empty 
prop_unfuse_fuse_Abs' :: (Abs Int [Name Int], Abs Int [Name Int]) -> Property 
prop_unfuse_fuse_Abs' (a, b) = expectFailure ( (unfuse . fuse) (a, b) === (a, b) )

-- | Atm.X iso Nom (Atm x X)
prop_abs_to_nom :: Abs Int [Name Int] -> Bool
prop_abs_to_nom x' = x' == nomToAbs (absToNom x')

-- | Nom (Atm x X) iso Atm.X.  
--
-- Note: We have to use unifiability because of local scope.
prop_nom_to_abs :: Nom (Name Int, [Name Int]) -> Bool 
prop_nom_to_abs x' = unifiablePerm x' (absToNom (nomToAbs x'))

